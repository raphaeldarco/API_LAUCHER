import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import customtkinter as ctk
import os
import sys
import ctypes
import base64
import re
import time
import threading
import configparser
from datetime import datetime
from pathlib import Path
from queue import Queue, Empty

import requests
import pandas as pd
from cryptography.fernet import Fernet
from requests.adapters import HTTPAdapter

# ============================================================
# DIPJE - API V4
# ============================================================
# Mantido o comportamento dos números CNJ: o programa NÃO
# normaliza/transforma o número encontrado. O formato capturado
# é preservado exatamente como veio da origem.
# Todos os arquivos gerados também ficam na pasta do executável.
# ============================================================

APP_NAME = "DIPJE"
APP_VERSION = "1.4.0"
BASE_DIR = Path(sys.executable if getattr(sys, "frozen", False) else __file__).resolve().parent

CONFIG_PATH = BASE_DIR / "config.ini"
REPORT_DIR = BASE_DIR

# ---------- ESTADO / CONSTANTES ----------
ESTADOS = {
    "PRONTO": "PRONTO",
    "EXECUTANDO": "EXECUTANDO",
    "PARANDO": "PARANDO",
    "FINALIZANDO": "FINALIZANDO",
    "AGUARDANDO_CONFIRMACAO": "AGUARDANDO CONFIRMAÇÃO",
    "CONCLUIDO": "CONCLUÍDO",
    "PARADO": "PARADO",
}

STATUS_SUCESSO = set(range(200, 300))
RESPONSE_LOG_LIMIT = 1000

# ---------- ANTI SLEEP ----------
ES_CONTINUOUS = 0x80000000
ES_SYSTEM_REQUIRED = 0x00000001
ES_DISPLAY_REQUIRED = 0x00000002

IS_WINDOWS = os.name == "nt"
if IS_WINDOWS:
    try:
        ctypes.windll.kernel32.SetThreadExecutionState(
            ES_CONTINUOUS | ES_SYSTEM_REQUIRED | ES_DISPLAY_REQUIRED
        )
    except Exception:
        pass

# ---------- COMPATIBILIDADE CRIPTOGRÁFICA ----------
LEGACY_SECRET_KEY = b"z1Tn2N0hx5KwvW2BFS7PTeMFGP_VIp2XUuXxutOfUHs="
try:
    legacy_cipher = Fernet(LEGACY_SECRET_KEY)
except Exception:
    legacy_cipher = None


# ============================================================
# DPAPI WINDOWS
# ============================================================
class DATA_BLOB(ctypes.Structure):
    _fields_ = [
        ("cbData", ctypes.c_ulong),
        ("pbData", ctypes.POINTER(ctypes.c_ubyte)),
    ]


def _make_blob(data: bytes):
    buffer = ctypes.create_string_buffer(data)
    blob = DATA_BLOB(
        len(data),
        ctypes.cast(buffer, ctypes.POINTER(ctypes.c_ubyte)),
    )
    return blob, buffer


def dpapi_encrypt(value: str) -> str:
    if not value:
        return ""
    if not IS_WINDOWS:
        return "F:" + legacy_cipher.encrypt(value.encode()).decode() if legacy_cipher else value

    crypt32 = ctypes.windll.crypt32
    kernel32 = ctypes.windll.kernel32
    kernel32.LocalFree.argtypes = [ctypes.c_void_p]
    kernel32.LocalFree.restype = ctypes.c_void_p

    data_in, data_buffer = _make_blob(value.encode("utf-8"))
    data_out = DATA_BLOB()

    crypt32.CryptProtectData.argtypes = [
        ctypes.POINTER(DATA_BLOB),
        ctypes.c_wchar_p,
        ctypes.POINTER(DATA_BLOB),
        ctypes.c_void_p,
        ctypes.c_void_p,
        ctypes.c_ulong,
        ctypes.POINTER(DATA_BLOB),
    ]
    crypt32.CryptProtectData.restype = ctypes.c_bool

    ok = crypt32.CryptProtectData(
        ctypes.byref(data_in),
        "DIPJE",
        None,
        None,
        None,
        0,
        ctypes.byref(data_out),
    )
    if not ok:
        raise ctypes.WinError()

    try:
        encrypted = ctypes.string_at(data_out.pbData, data_out.cbData)
        return "D:" + base64.b64encode(encrypted).decode("ascii")
    finally:
        kernel32.LocalFree(data_out.pbData)


def dpapi_decrypt(value: str) -> str:
    if not value:
        return ""

    if value.startswith("D:") and IS_WINDOWS:
        try:
            crypt32 = ctypes.windll.crypt32
            kernel32 = ctypes.windll.kernel32
            kernel32.LocalFree.argtypes = [ctypes.c_void_p]
            kernel32.LocalFree.restype = ctypes.c_void_p
            raw = base64.b64decode(value[2:])
            data_in, data_buffer = _make_blob(raw)
            data_out = DATA_BLOB()

            crypt32.CryptUnprotectData.argtypes = [
                ctypes.POINTER(DATA_BLOB),
                ctypes.POINTER(ctypes.c_wchar_p),
                ctypes.POINTER(DATA_BLOB),
                ctypes.c_void_p,
                ctypes.c_void_p,
                ctypes.c_ulong,
                ctypes.POINTER(DATA_BLOB),
            ]
            crypt32.CryptUnprotectData.restype = ctypes.c_bool

            description = ctypes.c_wchar_p()
            ok = crypt32.CryptUnprotectData(
                ctypes.byref(data_in),
                ctypes.byref(description),
                None,
                None,
                None,
                0,
                ctypes.byref(data_out),
            )
            if not ok:
                raise ctypes.WinError()

            try:
                return ctypes.string_at(data_out.pbData, data_out.cbData).decode("utf-8")
            finally:
                kernel32.LocalFree(data_out.pbData)
        except Exception:
            return ""

    if value.startswith("F:") and legacy_cipher:
        try:
            return legacy_cipher.decrypt(value[2:].encode()).decode()
        except Exception:
            return ""

    if legacy_cipher:
        try:
            return legacy_cipher.decrypt(value.encode()).decode()
        except Exception:
            pass

    return value


# ============================================================
# ESTADO GLOBAL
# ============================================================
parar = threading.Event()
salvamento_concluido = threading.Event()

fila = Queue()
log_queue = Queue()

inicio_execucao = 0.0
concluidos = 0
total_da_rodada = 0
sucessos = 0
falhas = 0
workers_ativos = 0
ultimo_request = 0.0

lock_contador = threading.Lock()
lock_processamento = threading.Lock()
lock_rate = threading.Lock()
lock_workers_ativos = threading.Lock()
lock_resultados = threading.Lock()
lock_estado = threading.Lock()

em_processamento = set()
resultados = []
erros = []
logs = []

estado_atual = ESTADOS["PRONTO"]
finalizador_rodando = False
ultima_rodada_processos = []

# Controle do teste inicial: quando ativado, apenas 1 processo é enviado
# antes de pedir confirmação para iniciar os demais workers.
aguardando_confirmacao_primeiro = False

# ============================================================
# UTILITÁRIOS
# ============================================================

def agora_str():
    return datetime.now().strftime("%d/%m/%Y %H:%M:%S")


def nome_timestamp(prefixo, extensao="xlsx"):
    return REPORT_DIR / f"{prefixo}_{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}.{extensao}"


def resposta_log(texto):
    texto = "" if texto is None else str(texto)
    if len(texto) > RESPONSE_LOG_LIMIT:
        return texto[:RESPONSE_LOG_LIMIT] + " ...[truncado]"
    return texto


def limpar_fila():
    while True:
        try:
            fila.get_nowait()
            fila.task_done()
        except Empty:
            break


def fila_lista():
    with fila.mutex:
        return list(fila.queue)


def extrair_lista_texto(texto):
    return [p.strip() for p in re.split(r"[\n,]+", texto) if p.strip()]


# ============================================================
# STATUS / INTERFACE
# ============================================================

def definir_estado(novo_estado):
    global estado_atual
    with lock_estado:
        estado_atual = novo_estado
    try:
        root.after(0, atualizar_estado_ui)
    except Exception:
        pass


def get_estado():
    with lock_estado:
        return estado_atual


def atualizar_estado_ui():
    estado = get_estado()
    cores = {
        "PRONTO": "#64748B",
        "EXECUTANDO": "#10B981",
        "PARANDO": "#EF4444",
        "FINALIZANDO": "#8B5CF6",
        "AGUARDANDO CONFIRMAÇÃO": "#F59E0B",
        "CONCLUÍDO": "#10B981",
        "PARADO": "#EF4444",
    }
    try:
        lbl_status.configure(text=f"● {estado}", text_color=cores.get(estado, "#CBD5E1"))
    except Exception:
        pass

    ativo = estado in {
        ESTADOS["EXECUTANDO"],
        ESTADOS["PARANDO"],
        ESTADOS["FINALIZANDO"],
        ESTADOS["AGUARDANDO_CONFIRMACAO"],
    }

    try:
        btn_enviar.configure(state="disabled" if ativo else "normal")
        btn_parar.configure(state="normal" if ativo else "disabled")
        btn_reprocessar.configure(state="normal" if (not ativo and erros) else "disabled")
    except Exception:
        pass


def atualizar_dashboard():
    try:
        with lock_contador:
            c = concluidos
            total = total_da_rodada
            s = sucessos
            f = falhas
            inicio = inicio_execucao
        with lock_workers_ativos:
            wa = workers_ativos

        tempo = max(0.0, time.time() - inicio) if inicio else 0.0
        req_s = c / tempo if tempo > 0 else 0.0
        restante = max(0, total - c)
        eta = restante / req_s if req_s > 0 else 0.0
        percentual = (c / total * 100.0) if total else 0.0

        def fmt_segundos(seg):
            seg = int(max(0, seg))
            h, rem = divmod(seg, 3600)
            m, s2 = divmod(rem, 60)
            return f"{h:02d}:{m:02d}:{s2:02d}" if h else f"{m:02d}:{s2:02d}"

        lbl_dashboard.configure(
            text=(
                f"Processados: {c:,}/{total:,}   |   ✅ {s:,}   |   ❌ {f:,}   |   "
                f"Workers ativos: {wa}   |   {req_s:.2f} req/s   |   "
                f"ETA: {fmt_segundos(eta)}"
            ).replace(",", ".")
        )
        progress_bar.set(min(1.0, percentual / 100.0))
        lbl_percent.configure(text=f"{percentual:.1f}%")
    except Exception:
        pass
    root.after(500, atualizar_dashboard)


# ============================================================
# LOG
# ============================================================

def log(msg):
    log_queue.put(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")


def processar_logs():
    try:
        while True:
            try:
                msg = log_queue.get_nowait()
            except Empty:
                break
            logs.append(msg)
            try:
                max_logs = max(10, int(entry_max_logs.get() or 20))
            except Exception:
                max_logs = 20
            while len(logs) > max_logs:
                logs.pop(0)

        result_text.delete("1.0", tk.END)
        result_text.insert(tk.END, "\n".join(logs))
        result_text.see(tk.END)
    except Exception:
        pass
    root.after(80, processar_logs)


def exportar_log_txt():
    if not logs:
        messagebox.showinfo("Logs", "Não há logs para exportar.", parent=root)
        return
    nome = REPORT_DIR / f"DIPJE_Log_{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}.txt"
    try:
        nome.write_text("\n".join(logs), encoding="utf-8")
        log(f"📝 Log exportado: {nome}")
    except Exception as e:
        messagebox.showerror("Erro", f"Não foi possível exportar o log:\n{e}", parent=root)


# ============================================================
# CONFIGURAÇÕES
# ============================================================

def config_values():
    return {
        "endpoint_prefix": entry_endpoint_prefix.get().strip(),
        "endpoint_suffix": entry_endpoint_suffix.get().strip(),
        "token": entry_token_acesso_api.get(),
        "login": entry_login.get(),
        "senha": entry_senha.get(),
        "variaveis": entry_variaveis.get().strip(),
        "workers": entry_workers.get().strip(),
        "rate": entry_rate.get().strip(),
        "max_logs": entry_max_logs.get().strip(),
        "teste_primeiro": "1" if var_teste_primeiro.get() else "0",
    }


def aplicar_config_values(values):
    campos_map = {
        "endpoint_prefix": entry_endpoint_prefix,
        "endpoint_suffix": entry_endpoint_suffix,
        "token": entry_token_acesso_api,
        "login": entry_login,
        "senha": entry_senha,
        "workers": entry_workers,
        "rate": entry_rate,
        "max_logs": entry_max_logs,
    }
    for chave, widget in campos_map.items():
        widget.delete(0, tk.END)
        widget.insert(0, values.get(chave, ""))

    variavel = values.get("variaveis", "")
    if variavel:
        entry_variaveis.set(variavel)

    var_teste_primeiro.set(values.get("teste_primeiro", "0") == "1")


def salvar_config():
    try:
        values = config_values()
        historico = list(entry_variaveis.cget("values")) if entry_variaveis.cget("values") else []
        atual = values["variaveis"]
        if atual and atual not in historico:
            historico.insert(0, atual)
        historico = historico[:15]
        entry_variaveis.configure(values=historico)

        config = configparser.ConfigParser()
        config["CONFIG"] = {
            "endpoint_prefix": dpapi_encrypt(values["endpoint_prefix"]),
            "endpoint_suffix": dpapi_encrypt(values["endpoint_suffix"]),
            "token": dpapi_encrypt(values["token"]),
            "login": dpapi_encrypt(values["login"]),
            "senha": dpapi_encrypt(values["senha"]),
            "variaveis": dpapi_encrypt(atual),
            "variaveis_historico": dpapi_encrypt("||".join(historico)),
            "workers": dpapi_encrypt(values["workers"]),
            "rate": dpapi_encrypt(values["rate"]),
            "max_logs": dpapi_encrypt(values["max_logs"]),
            "teste_primeiro": dpapi_encrypt(values["teste_primeiro"]),
        }
        with CONFIG_PATH.open("w", encoding="utf-8") as f:
            config.write(f)
    except Exception as e:
        log(f"❌ Falha ao salvar configuração: {e}")


def carregar_config():
    caminho = CONFIG_PATH
    if not caminho.exists():
        return

    try:
        config = configparser.ConfigParser()
        config.read(caminho, encoding="utf-8")
        if "CONFIG" not in config:
            return
        sec = config["CONFIG"]

        valores = {
            "endpoint_prefix": dpapi_decrypt(sec.get("endpoint_prefix", "")),
            "endpoint_suffix": dpapi_decrypt(sec.get("endpoint_suffix", "")),
            "token": dpapi_decrypt(sec.get("token", "")),
            "login": dpapi_decrypt(sec.get("login", "")),
            "senha": dpapi_decrypt(sec.get("senha", "")),
            "variaveis": dpapi_decrypt(sec.get("variaveis", "")),
            "workers": dpapi_decrypt(sec.get("workers", "20")) or "20",
            "rate": dpapi_decrypt(sec.get("rate", "0")) or "0",
            "max_logs": dpapi_decrypt(sec.get("max_logs", "20")) or "20",
            "teste_primeiro": dpapi_decrypt(sec.get("teste_primeiro", "0")) or "0",
        }
        aplicar_config_values(valores)

        hist_str = dpapi_decrypt(sec.get("variaveis_historico", ""))
        if hist_str:
            hist = hist_str.split("||")
            entry_variaveis.configure(values=hist[:15])
        elif valores["variaveis"]:
            entry_variaveis.configure(values=[valores["variaveis"]])

        salvar_config()
        log(f"⚙ Configuração carregada de: {caminho}")
    except Exception as e:
        log(f"⚠ Não foi possível carregar config.ini: {e}")


# ============================================================
# CNJ - EXTRAÇÃO E FORMATAÇÃO PADRONIZADA
# ============================================================
PADRAO_CNJ = re.compile(
    r'(?<![A-Za-z0-9])\d{7}[-.\s]?\d{2}[-.\s]?\d{4}[-.\s]?\d[-.\s]?\d{2}[-.\s]?\d{4}(?![A-Za-z0-9])'
)
ATRASO_EXTRACAO_BRUTA_MS = 350
extracao_bruta_agendada = None


def formatar_numero_cnj(numero):
    digitos = re.sub(r"\D", "", numero)
    return f"{digitos[:7]}-{digitos[7:9]}.{digitos[9:13]}.{digitos[13]}.{digitos[14:16]}.{digitos[16:20]}"


def extrair_processos_brutos(_event=None):
    global extracao_bruta_agendada
    if extracao_bruta_agendada is not None:
        root.after_cancel(extracao_bruta_agendada)
    extracao_bruta_agendada = root.after(
        ATRASO_EXTRACAO_BRUTA_MS,
        _processar_extracao_processos_brutos,
    )


def _processar_extracao_processos_brutos():
    global extracao_bruta_agendada
    extracao_bruta_agendada = None
    texto = entry_texto_bruto.get("1.0", "end-1c").strip()
    if not texto:
        txt_processos_extraidos.delete("1.0", tk.END)
        lbl_processos_extraidos.configure(text="Processos Extraídos (0)")
        return

    encontrados = [formatar_numero_cnj(numero) for numero in PADRAO_CNJ.findall(texto)]
    unicos = list(dict.fromkeys(encontrados))

    txt_processos_extraidos.delete("1.0", tk.END)
    txt_processos_extraidos.insert("1.0", "\n".join(unicos))
    atualizar_contador_lateral(quantidade=len(unicos))


def cancelar_extracao_processos_brutos():
    global extracao_bruta_agendada
    if extracao_bruta_agendada is not None:
        root.after_cancel(extracao_bruta_agendada)
        extracao_bruta_agendada = None


def atualizar_contador_lateral(event=None, quantidade=None):
    if quantidade is None:
        conteudo = txt_processos_extraidos.get("1.0", tk.END).strip()
        quantidade = sum(1 for linha in conteudo.splitlines() if linha.strip())
    lbl_processos_extraidos.configure(
        text=f"Processos Extraídos ({quantidade:,})".replace(",", ".")
    )


def limpar_lista_lateral():
    txt_processos_extraidos.delete("1.0", tk.END)
    lbl_processos_extraidos.configure(text="Processos Extraídos (0)")


def limpar_texto_bruto():
    cancelar_extracao_processos_brutos()
    entry_texto_bruto.delete("1.0", tk.END)
    txt_processos_extraidos.delete("1.0", tk.END)
    lbl_processos_extraidos.configure(text="Processos Extraídos (0)")


def copiar_processos():
    conteudo = txt_processos_extraidos.get("1.0", tk.END).strip()
    if not conteudo:
        return
    root.clipboard_clear()
    root.clipboard_append(conteudo)
    root.update()
    log("📋 Lista de processos copiada para a área de transferência.")


# ============================================================
# VARIÁVEIS COM HISTÓRICO
# ============================================================

def remover_variavel_atual():
    val_atual = entry_variaveis.get().strip()
    valores = list(entry_variaveis.cget("values")) if entry_variaveis.cget("values") else []

    if not val_atual:
        messagebox.showwarning("Aviso", "Nenhuma variável selecionada para apagar.", parent=root)
        return

    if val_atual in valores:
        valores.remove(val_atual)
        entry_variaveis.configure(values=valores)
        entry_variaveis.set(valores[0] if valores else "")
        salvar_config()
        log(f"🗑️ Variável '{val_atual}' removida do histórico.")
    else:
        messagebox.showwarning("Aviso", "A variável informada não está na lista salva.", parent=root)


# ============================================================
# ARQUIVOS / PARSERS
# ============================================================

def ler_arquivo(caminho):
    ext = caminho.lower().split(".")[-1]

    if ext == "xlsx":
        planilhas = pd.read_excel(caminho, sheet_name=None, dtype=str)
        blocos = []
        for nome, df in planilhas.items():
            if df is None or df.empty:
                continue
            df = df.fillna("")
            blocos.append(f"\n--- PLANILHA: {nome} ---\n")
            blocos.append(df.to_string(index=False, header=False))
        return "\n".join(blocos), len(planilhas)

    if ext == "txt":
        return Path(caminho).read_text(encoding="utf-8", errors="ignore"), 1

    if ext == "docx":
        try:
            import docx
        except ImportError as e:
            raise RuntimeError("Para ler .docx, instale: pip install python-docx") from e
        doc = docx.Document(caminho)
        partes = [p.text for p in doc.paragraphs if p.text]
        for tabela in doc.tables:
            for linha in tabela.rows:
                partes.append(" | ".join(c.text for c in linha.cells))
        return "\n".join(partes), 1

    if ext == "doc":
        try:
            import win32com.client
        except ImportError as e:
            raise RuntimeError("Para ler .doc, instale: pip install pywin32") from e

        word = None
        documento = None
        try:
            word = win32com.client.Dispatch("Word.Application")
            word.Visible = False
            documento = word.Documents.Open(str(Path(caminho).resolve()), ReadOnly=True)
            return documento.Content.Text, 1
        finally:
            try:
                if documento is not None:
                    documento.Close(False)
            except Exception:
                pass
            try:
                if word is not None:
                    word.Quit()
            except Exception:
                pass

    if ext == "pdf":
        try:
            import pypdf
        except ImportError as e:
            raise RuntimeError("Para ler .pdf, instale: pip install pypdf") from e
        reader = pypdf.PdfReader(caminho)
        paginas = []
        for pagina in reader.pages:
            t = pagina.extract_text()
            if t:
                paginas.append(t)
        texto = "\n".join(paginas)
        if not texto.strip():
            return "", len(reader.pages)
        return texto, len(reader.pages)

    if ext in {"html", "htm"}:
        conteudo_html = Path(caminho).read_text(encoding="utf-8", errors="ignore")
        try:
            from bs4 import BeautifulSoup
            soup = BeautifulSoup(conteudo_html, "html.parser")
            return soup.get_text(separator=" "), 1
        except ImportError:
            return conteudo_html, 1

    raise RuntimeError(f"Formato de arquivo não suportado: .{ext}")


def adicionar_processos(lista):
    conteudo_atual = txt_processos_extraidos.get("1.0", tk.END).strip()
    lista_atual = extrair_lista_texto(conteudo_atual)
    lista_final = list(dict.fromkeys(lista_atual + lista))

    txt_processos_extraidos.delete("1.0", tk.END)
    txt_processos_extraidos.insert("1.0", "\n".join(lista_final))
    atualizar_contador_lateral()
    return len(lista_final)


def carregar_arquivo():
    if get_estado() in {ESTADOS["EXECUTANDO"], ESTADOS["PARANDO"], ESTADOS["FINALIZANDO"]}:
        messagebox.showwarning("Execução ativa", "Pare a execução atual antes de carregar outro arquivo.", parent=root)
        return

    caminho = filedialog.askopenfilename(
        title="Selecione o arquivo para extrair processos",
        filetypes=[
            ("Arquivos Suportados", "*.xlsx *.txt *.docx *.doc *.pdf *.html *.htm"),
            ("Excel", "*.xlsx"),
            ("Texto", "*.txt"),
            ("Word", "*.docx *.doc"),
            ("PDF", "*.pdf"),
            ("HTML / Web", "*.html *.htm"),
            ("Todos os Arquivos", "*.*"),
        ],
    )
    if not caminho:
        return

    try:
        texto, quantidade = ler_arquivo(caminho)
        if not texto.strip():
            messagebox.showwarning(
                "Aviso",
                f"Nenhum texto foi extraído do arquivo:\n{os.path.basename(caminho)}\n\n"
                "Se for um PDF escaneado, ele pode ser apenas imagem e exigir OCR.",
                parent=root,
            )
            return

        encontrados = [formatar_numero_cnj(numero) for numero in PADRAO_CNJ.findall(texto)]
        if not encontrados:
            messagebox.showwarning(
                "Aviso",
                f"Nenhum processo válido (padrão CNJ) encontrado no arquivo:\n{os.path.basename(caminho)}",
                parent=root,
            )
            return

        unicos_arquivo = list(dict.fromkeys(encontrados))
        total = adicionar_processos(unicos_arquivo)
        log(
            f"📄 Arquivo carregado: {os.path.basename(caminho)} | "
            f"{len(unicos_arquivo)} processos únicos encontrados | {total} na lista total."
        )
        messagebox.showinfo(
            "OK",
            f"Arquivo: {os.path.basename(caminho)}\n"
            f"{len(unicos_arquivo):,} processos únicos encontrados.\n"
            f"Lista atual: {total:,} processos.".replace(",", "."),
            parent=root,
        )
    except Exception as e:
        messagebox.showerror("Erro", f"Erro ao processar o arquivo:\n{e}", parent=root)


# ============================================================
# RATE LIMITER
# ============================================================

def aguardar_rate_limit(rate_limit):
    global ultimo_request
    if rate_limit <= 0:
        return

    intervalo = 1.0 / rate_limit
    while True:
        with lock_rate:
            agora = time.monotonic()
            espera = intervalo - (agora - ultimo_request)
            if espera <= 0:
                ultimo_request = agora
                return
        time.sleep(min(espera, 0.2))


# ============================================================
# HTTP / WORKER
# ============================================================

def criar_session():
    session = requests.Session()
    adapter = HTTPAdapter(pool_connections=2, pool_maxsize=2)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    session.headers.update({"Accept": "application/json"})
    return session


def registrar_resultado(registro):
    global sucessos, falhas, concluidos
    with lock_resultados:
        resultados.append(registro)
        if registro["resultado"] == "SUCESSO":
            sucessos += 1
        else:
            falhas += 1
    with lock_contador:
        concluidos += 1
        return concluidos


def worker(login, senha, variaveis, endpoint, token, rate_limit, worker_id, somente_um=False):
    global workers_ativos, aguardando_confirmacao_primeiro
    session = criar_session()

    with lock_workers_ativos:
        workers_ativos += 1

    try:
        while True:
            if parar.is_set():
                break

            try:
                processo = fila.get(timeout=0.5)
            except Empty:
                break

            if parar.is_set():
                fila.put(processo)
                fila.task_done()
                break

            with lock_processamento:
                em_processamento.add(processo)

            data = {
                "login": login,
                "senha": senha,
                "numeroProcesso": str(processo),
                "variaveis": variaveis,
            }
            headers = {
                "Content-Type": "application/json",
                "token": token,
            }

            status = "CONEXAO"
            resposta = ""
            inicio_item = time.perf_counter()
            terminou_com_sucesso = False

            try:
                try:
                    aguardar_rate_limit(rate_limit)

                    t0 = time.perf_counter()
                    response = session.post(
                        endpoint,
                        headers=headers,
                        json=data,
                        timeout=(15, 90),
                    )
                    
                    status = response.status_code
                    resposta = response.text

                    if status in STATUS_SUCESSO:
                        terminou_com_sucesso = True

                except requests.RequestException as e:
                    status = "CONEXAO"
                    resposta = str(e)
                except Exception as e:
                    status = "ERRO_INTERNO"
                    resposta = str(e)

                duracao_total = time.perf_counter() - inicio_item
                resultado_texto = "SUCESSO" if terminou_com_sucesso else "ERRO"

                registro = {
                    "data_hora": agora_str(),
                    "worker": worker_id,
                    "processo": str(processo),
                    "status_http": status,
                    "resultado": resultado_texto,
                    "duracao_s": round(duracao_total, 3),
                    "resposta": resposta,
                }

                if not terminou_com_sucesso:
                    with lock_resultados:
                        erros.append(registro.copy())

                c = registrar_resultado(registro)
                with lock_contador:
                    total = total_da_rodada
                    inicio = inicio_execucao
                tempo = time.time() - inicio if inicio else 0
                rps = c / tempo if tempo > 0 else 0
                restante = max(0, total - c)
                eta = restante / rps if rps > 0 else 0
                log(
                    f"[{status}] {'✅' if terminou_com_sucesso else '❌'} {c}/{total} | "
                    f"{rps:.2f} req/s | ETA {eta:.1f}s | {processo} | "
                    f"{duracao_total:.2f}s | {resposta_log(resposta)}"
                )

            finally:
                with lock_processamento:
                    em_processamento.discard(processo)
                fila.task_done()

            # No modo de teste inicial, este worker envia exatamente 1 processo
            # e encerra para que o usuário possa conferir o resultado antes
            # de liberar os demais workers.
            if somente_um:
                aguardando_confirmacao_primeiro = True
                break

    finally:
        try:
            session.close()
        except Exception:
            pass
        with lock_workers_ativos:
            workers_ativos -= 1


# ============================================================
# EXECUÇÃO / CONTROLES
# ============================================================

def validar_config_execucao():
    try:
        workers_count = int(entry_workers.get() or 20)
        if workers_count < 1 or workers_count > 500:
            raise ValueError("Workers deve estar entre 1 e 500.")
    except Exception as e:
        raise ValueError(f"Workers inválido: {e}")

    try:
        rate_limit = float(entry_rate.get() or 0)
        if rate_limit < 0 or rate_limit > 10000:
            raise ValueError("Rate limit deve estar entre 0 e 10000 req/s.")
    except Exception as e:
        raise ValueError(f"Rate limit inválido: {e}")

    endpoint = entry_endpoint_prefix.get().strip() + entry_endpoint_suffix.get().strip()
    if not endpoint.startswith(("http://", "https://")):
        raise ValueError("O Endpoint final deve começar com http:// ou https://")

    if not entry_token_acesso_api.get().strip():
        raise ValueError("Informe o token de acesso da API.")
    if not entry_login.get().strip():
        raise ValueError("Informe o login.")
    if not entry_senha.get():
        raise ValueError("Informe a senha.")

    return workers_count, rate_limit, endpoint


def preparar_nova_execucao():
    global inicio_execucao, concluidos, total_da_rodada, sucessos, falhas, ultimo_request, ultima_rodada_processos

    conteudo = txt_processos_extraidos.get("1.0", tk.END).strip()
    processos = list(dict.fromkeys(extrair_lista_texto(conteudo)))
    if not processos:
        raise ValueError("Nenhum processo carregado na lista lateral!")

    limpar_fila()
    for p in processos:
        fila.put(p)

    ultima_rodada_processos = processos.copy()
    inicio_execucao = time.time()
    concluidos = 0
    sucessos = 0
    falhas = 0
    ultimo_request = 0.0

    with lock_resultados:
        resultados.clear()
        erros.clear()

    global salvamento_concluido
    salvamento_concluido.clear()
    total_da_rodada = len(processos)


def iniciar_workers(login, senha, variaveis, endpoint, token, rate_limit, workers_count, somente_um=False):
    """Inicia os workers. No teste inicial, somente 1 worker é criado."""
    quantidade = 1 if somente_um else workers_count

    for i in range(1, quantidade + 1):
        threading.Thread(
            target=worker,
            args=(login, senha, variaveis, endpoint, token, rate_limit, i, somente_um and i == 1),
            daemon=True,
            name=f"DIPJE-Worker-{i}",
        ).start()


def finalizar_teste_primeiro(continuar):
    """Executa a decisão do usuário após o primeiro processo."""
    global aguardando_confirmacao_primeiro

    aguardando_confirmacao_primeiro = False

    if continuar:
        log("▶️ Confirmação recebida. Continuando com todos os workers configurados.")
        parar.clear()
        definir_estado(ESTADOS["EXECUTANDO"])

        iniciar_workers(
            entry_login.get(),
            entry_senha.get(),
            entry_variaveis.get(),
            entry_endpoint_prefix.get().strip() + entry_endpoint_suffix.get().strip(),
            entry_token_acesso_api.get(),
            float(entry_rate.get() or 0),
            int(entry_workers.get() or 20),
            somente_um=False,
        )
        iniciar_monitor_finalizacao()
        return

    # Usuário escolheu não continuar: preserva os pendentes para retomada.
    salvar_pendentes()
    gerar_relatorio_execucao()
    if erros:
        gerar_relatorio_erros()

    definir_estado(ESTADOS["PARADO"])
    log("⏸ Teste inicial concluído. Execução pausada pelo usuário.")
    log("➡️ Clique em ENVIAR quando quiser continuar os processos pendentes.")


def perguntar_continuacao_primeiro():
    """Pergunta, na thread da interface, se deve liberar os demais workers."""
    if fila.qsize() <= 0:
        # Não há restante; o fluxo normal de finalização pode continuar.
        iniciar_monitor_finalizacao()
        return

    pendentes = fila.qsize()

    continuar = messagebox.askyesno(
        "Teste do 1º processo",
        f"O primeiro processo foi enviado.\n\n"
        f"Processados: {concluidos:,}\n"
        f"Pendentes: {pendentes:,}\n\n"
        "Confira no PJe se o processamento ocorreu como esperado.\n\n"
        "SIM = continuar com o restante da lista\n"
        "NÃO = parar e manter os pendentes para depois.",
        parent=root,
    )

    finalizar_teste_primeiro(continuar)


def executar():
    estado = get_estado()
    if estado in {
        ESTADOS["EXECUTANDO"],
        ESTADOS["PARANDO"],
        ESTADOS["FINALIZANDO"],
        ESTADOS["AGUARDANDO_CONFIRMACAO"],
    }:
        return

    salvar_config()

    try:
        workers_count, rate_limit, endpoint = validar_config_execucao()
    except ValueError as e:
        messagebox.showerror("Configuração inválida", str(e), parent=root)
        return

    pendentes = fila_lista()
    continuar_pendentes = bool(pendentes) and estado == ESTADOS["PARADO"]

    if not continuar_pendentes:
        try:
            preparar_nova_execucao()
        except ValueError as e:
            messagebox.showerror("Erro", str(e), parent=root)
            return
        log(f"🚀 INICIANDO NOVA: {total_da_rodada:,} processos.".replace(",", "."))
    else:
        log(f"⏯ CONTINUANDO: {len(pendentes):,} processos restantes.".replace(",", "."))

    parar.clear()
    salvamento_concluido.clear()

    global aguardando_confirmacao_primeiro
    aguardando_confirmacao_primeiro = False

    definir_estado(ESTADOS["EXECUTANDO"])

    login = entry_login.get()
    senha = entry_senha.get()
    variaveis = entry_variaveis.get()
    token = entry_token_acesso_api.get()

    modo_teste = var_teste_primeiro.get() and not continuar_pendentes

    if modo_teste:
        log("🧪 MODO TESTE ATIVO: será enviado somente 1 processo antes da confirmação.")
    else:
        log(f"⚙ Iniciando {workers_count} worker(s).")

    iniciar_workers(
        login,
        senha,
        variaveis,
        endpoint,
        token,
        rate_limit,
        workers_count,
        somente_um=modo_teste,
    )

    iniciar_monitor_finalizacao()


def iniciar_monitor_finalizacao():
    global finalizador_rodando
    with lock_estado:
        if finalizador_rodando:
            return
        finalizador_rodando = True
    threading.Thread(target=monitor_finalizacao, daemon=True, name="DIPJE-Finalizador").start()


def monitor_finalizacao():
    global finalizador_rodando
    try:
        while True:
            with lock_workers_ativos:
                ativos = workers_ativos
            if ativos <= 0:
                break
            time.sleep(0.2)

        # O primeiro processo terminou. Antes de liberar os demais,
        # devolve o controle à interface para o usuário conferir o PJe.
        if aguardando_confirmacao_primeiro and not parar.is_set():
            definir_estado(ESTADOS["AGUARDANDO_CONFIRMACAO"])
            root.after(0, perguntar_continuacao_primeiro)
            return

        if parar.is_set():
            salvar_pendentes()
            gerar_relatorio_execucao()
            definir_estado(ESTADOS["PARADO"])
            root.after(0, lambda: messagebox.showinfo(
                "Execução parada",
                f"Execução interrompida com segurança.\n\n"
                f"Processados: {concluidos:,}\n"
                f"Pendentes: {fila.qsize():,}\n"
                f"Erros: {len(erros):,}".replace(",", "."),
                parent=root,
            ))
            log("⛔ Execução parada com segurança. Clique em ENVIAR para continuar os pendentes.")
            return

        fila.join()
        definir_estado(ESTADOS["FINALIZANDO"])
        gerar_relatorio_execucao()
        if erros:
            gerar_relatorio_erros()

        tempo_total = time.time() - inicio_execucao if inicio_execucao else 0
        definir_estado(ESTADOS["CONCLUIDO"])
        log(
            f"✅ FINALIZADO em {tempo_total:.2f}s | sucesso: {sucessos:,} | "
            f"erros: {falhas:,}".replace(",", ".")
        )

        def mostrar_resultado():
            if erros:
                messagebox.showwarning(
                    "Concluído",
                    f"Execução finalizada com {len(erros):,} erro(s).\n\n"
                    "O relatório completo foi salvo na pasta de relatórios."
                    .replace(",", "."),
                    parent=root,
                )
            else:
                messagebox.showinfo(
                    "Sucesso",
                    "Todos os processos foram enviados com sucesso!\n\n"
                    "O relatório completo foi salvo.",
                    parent=root,
                )
        root.after(0, mostrar_resultado)
    except Exception as e:
        log(f"❌ Erro no finalizador: {e}")
    finally:
        with lock_estado:
            finalizador_rodando = False
        root.after(0, atualizar_estado_ui)


def parar_execucao():
    estado = get_estado()
    if estado != ESTADOS["EXECUTANDO"]:
        return
    log("⛔ Solicitando parada segura. Envios já iniciados terminarão normalmente.")
    parar.set()


def resetar_ambiente():
    estado = get_estado()
    if estado in {ESTADOS["EXECUTANDO"], ESTADOS["PARANDO"], ESTADOS["FINALIZANDO"]}:
        if not messagebox.askyesno(
            "Resetar Ambiente",
            "Existe uma execução em andamento. Deseja parar a execução atual e limpar tudo para uma nova lista?",
            parent=root,
        ):
            return
        parar.set()
        definir_estado(ESTADOS["PARANDO"])
        root.after(500, _executar_limpeza_total)
    else:
        _executar_limpeza_total()


def _executar_limpeza_total():
    limpar_fila()
    global concluidos, total_da_rodada, sucessos, falhas, inicio_execucao, ultima_rodada_processos
    concluidos = 0
    total_da_rodada = 0
    sucessos = 0
    falhas = 0
    inicio_execucao = 0.0
    ultima_rodada_processos.clear()
    
    with lock_resultados:
        resultados.clear()
        erros.clear()

    try:
        cancelar_extracao_processos_brutos()
        entry_texto_bruto.delete("1.0", tk.END)
        txt_processos_extraidos.delete("1.0", tk.END)
        lbl_processos_extraidos.configure(text="Processos Extraídos (0)")
    except Exception:
        pass

    definir_estado(ESTADOS["PRONTO"])
    log("🧹 Ambiente limpo e pronto para receber uma nova lista de processos.")


# ============================================================
# RELATÓRIOS
# ============================================================

def salvar_pendentes():
    if salvamento_concluido.is_set():
        return
    pendentes = fila_lista()
    if not pendentes:
        salvamento_concluido.set()
        return

    nome = nome_timestamp("Pendentes")
    try:
        pd.DataFrame({"processo": pendentes}).to_excel(nome, index=False)
        salvamento_concluido.set()
        log(f"⚠ {len(pendentes):,} processos pendentes salvos em {nome}".replace(",", "."))
    except Exception as e:
        log(f"❌ Erro ao salvar processos pendentes: {e}")


def snapshot_resultados():
    with lock_resultados:
        return list(resultados), list(erros)


def gerar_relatorio_erros():
    _, erros_snapshot = snapshot_resultados()
    if not erros_snapshot:
        return None
    nome = nome_timestamp("Relatorio_Erros")
    try:
        pd.DataFrame(erros_snapshot).to_excel(nome, index=False)
        log(f"⚠ Relatório de erros salvo: {nome}")
        return nome
    except Exception as e:
        log(f"❌ Erro ao salvar relatório de erros: {e}")
        return None


def gerar_relatorio_execucao():
    resultados_snapshot, erros_snapshot = snapshot_resultados()
    try:
        with lock_contador:
            total = total_da_rodada
            c = concluidos
            s = sucessos
            f = falhas
            inicio = inicio_execucao
        tempo_total = time.time() - inicio if inicio else 0
        req_s = c / tempo_total if tempo_total > 0 else 0

        caminho = nome_timestamp("Relatorio_Execucao")
        resumo = pd.DataFrame([
            {
                "inicio": datetime.fromtimestamp(inicio).strftime("%d/%m/%Y %H:%M:%S") if inicio else "",
                "fim": agora_str(),
                "tempo_total_s": round(tempo_total, 3),
                "total_processos": total,
                "processados": c,
                "sucessos": s,
                "erros": f,
                "taxa_media_req_s": round(req_s, 4),
                "workers_configurados": int(entry_workers.get() or 20),
                "rate_limit_configurado": float(entry_rate.get() or 0),
                "endpoint": entry_endpoint_prefix.get().strip() + entry_endpoint_suffix.get().strip(),
            }
        ])

        df_resultados = pd.DataFrame(resultados_snapshot)
        df_erros = pd.DataFrame(erros_snapshot)

        with pd.ExcelWriter(caminho, engine="openpyxl") as writer:
            resumo.to_excel(writer, sheet_name="RESUMO", index=False)
            if df_resultados.empty:
                pd.DataFrame(columns=[
                    "data_hora", "worker", "processo", "status_http", "resultado",
                    "duracao_s", "resposta"
                ]).to_excel(writer, sheet_name="RESULTADOS", index=False)
            else:
                df_resultados.to_excel(writer, sheet_name="RESULTADOS", index=False)
            if df_erros.empty:
                pd.DataFrame(columns=[
                    "data_hora", "worker", "processo", "status_http", "resultado",
                    "duracao_s", "resposta"
                ]).to_excel(writer, sheet_name="ERROS", index=False)
            else:
                df_erros.to_excel(writer, sheet_name="ERROS", index=False)

        log(f"📊 Relatório completo salvo: {caminho}")
        return caminho
    except Exception as e:
        log(f"❌ Erro ao gerar relatório completo: {e}")
        return None


def abrir_pasta_relatorios():
    try:
        os.startfile(str(BASE_DIR))
    except Exception as e:
        messagebox.showerror("Relatórios", f"Não foi possível abrir a pasta:\n{e}", parent=root)


# ============================================================
# REPROCESSAMENTO DE ERROS
# ============================================================

def reprocessar_erros():
    estado = get_estado()
    if estado in {ESTADOS["EXECUTANDO"], ESTADOS["PARANDO"], ESTADOS["FINALIZANDO"]}:
        return

    with lock_resultados:
        lista_erros = [e.copy() for e in erros]

    if not lista_erros:
        messagebox.showinfo("Reprocessar", "Não há erros para reprocessar.", parent=root)
        return

    transient = [e for e in lista_erros if str(e.get("status_http")) == "CONEXAO" or (str(e.get("status_http")).isdigit() and int(e.get("status_http")) in {408, 429, 500, 502, 503, 504})]
    outros = [e for e in lista_erros if e not in transient]

    if outros:
        escolha = messagebox.askyesno(
            "Reprocessar erros",
            f"Foram encontrados {len(lista_erros):,} erros.\n\n"
            f"Falhas transitórias recomendadas: {len(transient):,}\n"
            f"Outros erros: {len(outros):,}\n\n"
            "SIM = reprocessar todos\nNÃO = reprocessar somente falhas transitórias",
            parent=root,
        )
        selecionados = lista_erros if escolha else transient
    else:
        selecionados = transient

    if not selecionados:
        messagebox.showinfo("Reprocessar", "Não há falhas transitórias para reprocessar.", parent=root)
        return

    limpar_fila()
    processos = []
    for erro in selecionados:
        processo = str(erro.get("processo", "")).strip()
        if processo and processo not in processos:
            processos.append(processo)

    for p in processos:
        fila.put(p)

    global total_da_rodada, inicio_execucao, concluidos, sucessos, falhas, ultima_rodada_processos, ultimo_request
    total_da_rodada = len(processos)
    inicio_execucao = time.time()
    concluidos = 0
    sucessos = 0
    falhas = 0
    ultimo_request = 0.0
    ultima_rodada_processos = processos.copy()
    with lock_resultados:
        resultados.clear()
        erros.clear()
    salvamento_concluido.clear()

    try:
        workers_count, rate_limit, endpoint = validar_config_execucao()
    except ValueError as e:
        messagebox.showerror("Configuração inválida", str(e), parent=root)
        return

    log(f"↻ REPROCESSANDO {len(processos):,} processo(s) com a mesma configuração.".replace(",", "."))
    parar.clear()

    global aguardando_confirmacao_primeiro
    aguardando_confirmacao_primeiro = False

    definir_estado(ESTADOS["EXECUTANDO"])

    modo_teste = var_teste_primeiro.get()
    if modo_teste:
        log("🧪 MODO TESTE ATIVO também para o reprocessamento: será enviado 1 processo primeiro.")

    iniciar_workers(
        entry_login.get(),
        entry_senha.get(),
        entry_variaveis.get(),
        endpoint,
        entry_token_acesso_api.get(),
        rate_limit,
        workers_count,
        somente_um=modo_teste,
    )
    iniciar_monitor_finalizacao()


# ============================================================
# EXCEÇÕES GLOBAIS
# ============================================================

def tratar_excecao_global(exc_type, exc_value, exc_traceback):
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_traceback)
        return
    log(f"❌ Erro crítico detectado: {exc_value}")
    try:
        parar.set()
        salvamento_concluido.clear()
        salvar_pendentes()
        gerar_relatorio_erros()
    except Exception:
        pass
    sys.__excepthook__(exc_type, exc_value, exc_traceback)


def tratar_excecao_thread(args):
    log(f"❌ Erro no worker {getattr(args.thread, 'name', '?')}: {args.exc_value}")
    try:
        parar.set()
    except Exception:
        pass


sys.excepthook = tratar_excecao_global
if hasattr(threading, "excepthook"):
    threading.excepthook = tratar_excecao_thread


# ============================================================
# FECHAMENTO
# ============================================================

def ao_fechar():
    estado = get_estado()
    if estado in {ESTADOS["EXECUTANDO"], ESTADOS["PARANDO"], ESTADOS["FINALIZANDO"]}:
        if not messagebox.askyesno(
            "Fechar DIPJE",
            "Existe uma execução ativa.\n\nDeseja solicitar uma parada segura e fechar o programa quando os envios atuais terminarem?",
            parent=root,
        ):
            return
        parar_execucao()
        aguardar_fechamento()
        return

    finalizar_fechamento()


def aguardar_fechamento():
    with lock_workers_ativos:
        ativos = workers_ativos
    if ativos > 0:
        root.after(200, aguardar_fechamento)
        return
    salvamento_concluido.clear()
    salvar_pendentes()
    gerar_relatorio_execucao()
    finalizar_fechamento()


def finalizar_fechamento():
    try:
        salvar_config()
    except Exception:
        pass
    if IS_WINDOWS:
        try:
            ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS)
        except Exception:
            pass
    try:
        root.destroy()
    except Exception:
        pass


# ============================================================
# UI
# ============================================================
ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

root = ctk.CTk()
root.title(f"{APP_NAME} - API 🚀 v{APP_VERSION}")
root.geometry("1400x820")
root.minsize(1180, 720)

frame_main = ctk.CTkFrame(root, corner_radius=10)
frame_main.pack(fill="both", expand=True, padx=15, pady=15)

frame_esquerda = ctk.CTkFrame(frame_main, fg_color="transparent")
frame_esquerda.pack(side="left", fill="both", expand=True, padx=(0, 10))

# ---------- topo / status ----------
frame_topo = ctk.CTkFrame(frame_esquerda, corner_radius=10)
frame_topo.pack(fill="x", padx=10, pady=(8, 5))

lbl_status = ctk.CTkLabel(frame_topo, text="● PRONTO", font=("Roboto", 14, "bold"), text_color="#64748B")
lbl_status.pack(side="left", padx=12, pady=8)

lbl_percent = ctk.CTkLabel(frame_topo, text="0.0%", font=("Roboto", 12, "bold"))
lbl_percent.pack(side="right", padx=10)

progress_bar = ctk.CTkProgressBar(frame_topo, width=250)
progress_bar.set(0)
progress_bar.pack(side="right", padx=5)

frame_dashboard = ctk.CTkFrame(frame_esquerda, fg_color="transparent")
frame_dashboard.pack(fill="x", padx=10, pady=3)

lbl_dashboard = ctk.CTkLabel(
    frame_dashboard,
    text="Processados: 0/0 | ✅ 0 | ❌ 0 | Workers ativos: 0 | 0.00 req/s | ETA: 00:00",
    anchor="w",
    font=("Consolas", 11),
)
lbl_dashboard.pack(fill="x")


# ---------- configurações ----------
frame_configs = ctk.CTkFrame(frame_esquerda, fg_color="transparent")
frame_configs.pack(fill="x", padx=10, pady=5)

campos = [
    ("Endpoint", 350),
    ("Endpoint Base", 350),
    ("Token", 350),
    ("Login", 200),
    ("Senha", 200),
    ("Variáveis", 350),
    ("Workers", 120),
    ("Rate limit (req/s)", 120),
    ("Max logs", 120),
    ("Texto Bruto (Cole aqui)", 280),
]

entries = []

for i, (t, w) in enumerate(campos):
    row = i if i < 6 else i - 6
    col = 0 if i < 6 else 2

    lbl = ctk.CTkLabel(frame_configs, text=t, font=("Roboto", 12, "bold"))
    lbl.grid(row=row, column=col, sticky="e", padx=10, pady=7)

    if t == "Variáveis":
        frame_var = ctk.CTkFrame(frame_configs, fg_color="transparent")
        frame_var.grid(row=row, column=col + 1, padx=10, pady=7, sticky="w")

        e = ctk.CTkComboBox(frame_var, width=w - 45, values=[])
        e.pack(side="left")
        ctk.CTkButton(
            frame_var,
            text="❌",
            width=35,
            fg_color="#EF4444",
            hover_color="#DC2626",
            command=remover_variavel_atual,
        ).pack(side="left", padx=(5, 0))

    elif t == "Texto Bruto (Cole aqui)":
        frame_bruto = ctk.CTkFrame(frame_configs, fg_color="transparent")
        frame_bruto.grid(row=row, column=col + 1, padx=10, pady=7, sticky="w")

        e = ctk.CTkTextbox(
            frame_bruto,
            width=w - 45,
            height=64,
            wrap="word",
        )
        e.pack(side="left")
        ctk.CTkButton(
            frame_bruto,
            text="🧹",
            width=35,
            fg_color="#4B5563",
            hover_color="#374151",
            command=limpar_texto_bruto,
        ).pack(side="left", padx=(5, 0))
    else:
        e = ctk.CTkEntry(frame_configs, width=w, show="*" if t == "Senha" else "")
        e.grid(row=row, column=col + 1, padx=10, pady=7, sticky="w")

    entries.append(e)

(
    entry_endpoint_prefix,
    entry_endpoint_suffix,
    entry_token_acesso_api,
    entry_login,
    entry_senha,
    entry_variaveis,
    entry_workers,
    entry_rate,
    entry_max_logs,
    entry_texto_bruto,
) = entries

entry_texto_bruto.bind("<KeyRelease>", extrair_processos_brutos)
entry_texto_bruto.bind("<<Paste>>", extrair_processos_brutos)
entry_texto_bruto.bind("<<Cut>>", extrair_processos_brutos)

# ---------- teste inicial ----------
var_teste_primeiro = ctk.BooleanVar(value=False)

frame_teste = ctk.CTkFrame(frame_esquerda, fg_color="transparent")
frame_teste.pack(fill="x", padx=10, pady=(0, 2))

ctk.CTkCheckBox(
    frame_teste,
    text="Testar 1º processo antes de continuar",
    variable=var_teste_primeiro,
    onvalue=True,
    offvalue=False,
    command=salvar_config,
    font=("Roboto", 12, "bold"),
).pack(side="left", padx=4)

lbl_teste_info = ctk.CTkLabel(
    frame_teste,
    text="(envia 1 processo e pergunta se deve liberar os demais workers)",
    font=("Roboto", 10),
    text_color="#94A3B8",
)
lbl_teste_info.pack(side="left", padx=8)

# ---------- botões ----------
btn_frame = ctk.CTkFrame(frame_esquerda, fg_color="transparent")
btn_frame.pack(fill="x", pady=8, padx=10)

ctk.CTkButton(btn_frame, text="Carregar Arquivo 📄", command=carregar_arquivo, width=130, fg_color="#4B5563", hover_color="#374151").pack(side="left", padx=4, expand=True)
btn_enviar = ctk.CTkButton(btn_frame, text="ENVIAR 🚀", command=executar, width=130, fg_color="#10B981", hover_color="#059669")
btn_enviar.pack(side="left", padx=4, expand=True)
btn_parar = ctk.CTkButton(btn_frame, text="Parar", command=parar_execucao, width=130, fg_color="#EF4444", hover_color="#DC2626")
btn_parar.pack(side="left", padx=4, expand=True)
ctk.CTkButton(btn_frame, text="Nova Lista 🔄", command=resetar_ambiente, width=130, fg_color="#0284C7", hover_color="#0369A1").pack(side="left", padx=4, expand=True)
btn_reprocessar = ctk.CTkButton(btn_frame, text="↻ Reprocessar", command=reprocessar_erros, width=140, fg_color="#8B5CF6", hover_color="#7C3AED")
btn_reprocessar.pack(side="left", padx=4, expand=True)

btn_frame2 = ctk.CTkFrame(frame_esquerda, fg_color="transparent")
btn_frame2.pack(fill="x", padx=10, pady=(0, 5))
ctk.CTkButton(btn_frame2, text="Abrir pasta do programa 📁", command=abrir_pasta_relatorios, width=180).pack(side="left", padx=4)
ctk.CTkButton(btn_frame2, text="Exportar log 📝", command=exportar_log_txt, width=140, fg_color="#475569", hover_color="#334155").pack(side="left", padx=4)

# ---------- console ----------
result_text = tk.Text(
    frame_esquerda,
    height=15,
    bg="#0F172A",
    fg="#10B981",
    font=("Consolas", 10),
    insertbackground="white",
    relief="flat",
)
result_text.pack(fill="both", expand=True, padx=10, pady=5)

# ---------- lateral ----------
frame_lateral = ctk.CTkFrame(frame_main, width=300, corner_radius=10)
frame_lateral.pack(side="right", fill="both", padx=(0, 0))
frame_lateral.pack_propagate(False)

lbl_processos_extraidos = ctk.CTkLabel(
    frame_lateral,
    text="Processos Extraídos (0)",
    font=("Roboto", 13, "bold"),
    text_color="#10B981",
)
lbl_processos_extraidos.pack(pady=(12, 5), padx=10)

txt_processos_extraidos = ctk.CTkTextbox(
    frame_lateral,
    font=("Consolas", 11),
    fg_color="#0F172A",
    text_color="#38BDF8",
    wrap="none",
    activate_scrollbars=True,
)
txt_processos_extraidos.pack(fill="both", expand=True, padx=10, pady=(5, 5))
txt_processos_extraidos.bind("<KeyRelease>", atualizar_contador_lateral)

frame_lateral_btns = ctk.CTkFrame(frame_lateral, fg_color="transparent")
frame_lateral_btns.pack(fill="x", padx=10, pady=(0, 10))

ctk.CTkButton(
    frame_lateral_btns,
    text="Copiar 📋",
    height=28,
    command=copiar_processos,
).pack(side="left", fill="x", expand=True, padx=(0, 3))

ctk.CTkButton(
    frame_lateral_btns,
    text="Limpar Lista 🗑️",
    height=28,
    fg_color="#EF4444",
    hover_color="#DC2626",
    command=limpar_lista_lateral,
).pack(side="left", fill="x", expand=True, padx=(3, 0))

# ---------- inicialização ----------
carregar_config()
processar_logs()
atualizar_dashboard()
atualizar_estado_ui()
root.protocol("WM_DELETE_WINDOW", ao_fechar)
root.mainloop()