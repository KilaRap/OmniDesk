#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""OMNIDESK 4.0 — Sentinel-inspired RFID Operations Center para PC/SC.

Diseñado para aprendizaje y pruebas con tarjetas propias/autorizadas.

Funciones:
- Inventario de lectores PC/SC, identificación UID/ATR y monitor de presencia.
- Perfil tecnológico orientativo (no concluyente) a partir del ATR.
- Lectura, escritura y comparación limitadas al bloque de laboratorio 4.
- Autenticación con una única clave A/B conocida introducida manualmente.
- Registro JSON local e informes bajo petición, sin persistir claves.
- Conversión/análisis HEX, ASCII, decimal y binario; mapa de memoria de referencia.

No implementa fuerza bruta, recuperación de claves, clonación, escritura masiva,
lectura de tráileres ni modificación del bloque fabricante.

Dependencias en Kali/Debian:
  sudo apt install python3-tk python3-pyscard pcscd libccid -y
  sudo systemctl enable --now pcscd
Ejecución:
  python3 omnidesk.py
Autopruebas sin lector:
  python3 omnidesk.py --self-test
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import queue
import re
import subprocess
import sys
import threading
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Optional
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError as exc:  # pragma: no cover - depends on OS packaging
    print("No se pudo cargar Tkinter. En Kali instala: sudo apt install python3-tk")
    raise SystemExit(1) from exc

try:
    from smartcard.System import readers as pcsc_readers
    from smartcard.Exceptions import CardConnectionException, NoCardException
    PCSC_AVAILABLE = True
    PCSC_IMPORT_ERROR = ""
except ImportError as exc:  # GUI can open without pyscard for offline utilities
    pcsc_readers = None  # type: ignore[assignment]
    CardConnectionException = Exception  # type: ignore[assignment,misc]
    NoCardException = Exception  # type: ignore[assignment,misc]
    PCSC_AVAILABLE = False
    PCSC_IMPORT_ERROR = str(exc)

APP_NAME = "OMNIDESK"
VERSION = "4.0"
LAB_BLOCK = 4
KEY_SLOT = 0
KEY_LENGTH = 6
BLOCK_SIZE = 16
POLL_MS = 1400

# Paleta oscura con acento cian. No depende de paquetes externos.
C = {
    # Sentinel-inspired SOC palette: midnight surfaces, restrained teal signal,
    # clear severity colors and high-contrast typography.
    "bg": "#080F1B",
    "sidebar": "#0B1524",
    "panel": "#101D2E",
    "panel2": "#15253A",
    "panel3": "#1B3048",
    "border": "#263C55",
    "text": "#EAF2FA",
    "muted": "#91A7BC",
    "cyan": "#55D6D0",
    "cyan2": "#21AFAE",
    "green": "#6AD6A5",
    "yellow": "#F2C36B",
    "red": "#F17D88",
    "purple": "#B5A4FF",
    "white": "#FFFFFF",
    "nav_active": "#163C47",
    "nav_hover": "#14283D",
}

FONT = "Segoe UI" if os.name == "nt" else "DejaVu Sans"
MONO = "Cascadia Mono" if os.name == "nt" else "DejaVu Sans Mono"


def madrid_now() -> datetime:
    try:
        return datetime.now(ZoneInfo("Europe/Madrid"))
    except ZoneInfoNotFoundError:
        return datetime.now().astimezone()


def timestamp() -> str:
    return madrid_now().isoformat(timespec="seconds")


def compact_hex(value: str) -> str:
    return re.sub(r"[^0-9A-Fa-f]", "", value or "").upper()


def uid_to_bytes(uid: str) -> bytes:
    raw = compact_hex(uid)
    if not raw or len(raw) % 2:
        raise ValueError("UID vacío o con longitud hexadecimal incorrecta.")
    return bytes.fromhex(raw)


def validate_hex_block(raw: str) -> bytes:
    cleaned = compact_hex(raw)
    if not re.fullmatch(r"[0-9A-F]{32}", cleaned):
        raise ValueError("Introduce exactamente 32 caracteres hexadecimales (16 bytes).")
    return bytes.fromhex(cleaned)


def text_to_block(value: str) -> bytes:
    data = value.encode("utf-8")
    if not data:
        raise ValueError("El texto no puede estar vacío.")
    if len(data) > BLOCK_SIZE:
        raise ValueError(f"El texto ocupa {len(data)} bytes UTF-8; máximo 16.")
    return data.ljust(BLOCK_SIZE, b"\x00")


def classify_technology(atr: str) -> dict[str, str]:
    """Clasificación cautelosa del ATR comunicado para la tarjeta LF del laboratorio."""
    raw = compact_hex(atr)
    lf_prefix = "3B8F8001804F0CA00000030640"
    if raw.startswith(lf_prefix):
        return {
            "status": "lf_candidate",
            "family": "Posible HID Proximity / HITAG (LF)",
            "confidence": "indicio ATR + interpretación pcsc_scan",
            "detail": "La firma coincide con una tarjeta que pcsc_scan asoció a RFID de baja frecuencia. No identifica por sí sola el chip exacto.",
        }
    if raw:
        return {
            "status": "unknown",
            "family": "Tecnología no identificada",
            "confidence": "indeterminada",
            "detail": "El ATR no coincide con las firmas cautelosas incluidas. UID/ATR no demuestran por sí solos que sea MIFARE Classic.",
        }
    return {
        "status": "unknown",
        "family": "Tecnología no identificada",
        "confidence": "sin ATR",
        "detail": "No se ha obtenido ATR; consulta la documentación de la tarjeta.",
    }


def sw_description(sw1: int, sw2: int) -> str:
    mapping = {
        (0x90, 0x00): "Operación correcta",
        (0x63, 0x00): "Autenticación fallida o tarjeta no autenticada",
        (0x69, 0x82): "Condiciones de seguridad no satisfechas",
        (0x69, 0x85): "Condiciones de uso no satisfechas",
        (0x6A, 0x82): "Bloque no disponible",
        (0x6B, 0x00): "Dirección o parámetro incorrectos",
        (0x67, 0x00): "Longitud APDU incorrecta",
        (0x6D, 0x00): "Instrucción no admitida por lector/firmware",
        (0x6E, 0x00): "Clase APDU no admitida por lector/firmware",
    }
    return mapping.get((sw1, sw2), "Respuesta PC/SC no reconocida")


class OmniError(Exception):
    pass


def _transmit(connection: Any, apdu: list[int]) -> tuple[list[int], int, int]:
    try:
        response, sw1, sw2 = connection.transmit(apdu)
        return list(response), int(sw1), int(sw2)
    except Exception as exc:
        raise OmniError(f"Error al enviar APDU por PC/SC: {exc}") from exc


def _expect_ok(result: tuple[list[int], int, int], label: str) -> list[int]:
    data, sw1, sw2 = result
    if (sw1, sw2) != (0x90, 0x00):
        raise OmniError(f"{label}: SW={sw1:02X} {sw2:02X} — {sw_description(sw1, sw2)}")
    return data


def _connect(reader: Any) -> Any:
    if reader is None:
        raise OmniError("Selecciona primero un lector PC/SC.")
    try:
        conn = reader.createConnection()
        conn.connect()
        return conn
    except (NoCardException, CardConnectionException) as exc:
        raise OmniError("No hay tarjeta presente o el lector no puede conectarse.") from exc
    except Exception as exc:
        raise OmniError(f"No se pudo conectar con la tarjeta: {exc}") from exc


def _disconnect(conn: Any) -> None:
    if conn is not None:
        try:
            conn.disconnect()
        except Exception:
            pass


def _get_uid(conn: Any) -> str:
    data = _expect_ok(_transmit(conn, [0xFF, 0xCA, 0x00, 0x00, 0x00]), "Consulta UID")
    if not data:
        raise OmniError("El lector no ha devuelto UID.")
    return " ".join(f"{x:02X}" for x in data)


def _get_atr(conn: Any) -> str:
    try:
        values = conn.getATR()
        return " ".join(f"{x:02X}" for x in values) if values else "No disponible"
    except Exception:
        return "No disponible"


def _identity(conn: Any) -> dict[str, Any]:
    atr = _get_atr(conn)
    try:
        uid = _get_uid(conn)
        uid_len = len(uid_to_bytes(uid))
    except Exception as exc:
        uid = "No disponible"
        uid_len = 0
        uid_error = str(exc)
    else:
        uid_error = ""
    return {
        "uid": uid,
        "uid_length": uid_len,
        "atr": atr,
        "profile": classify_technology(atr),
        "timestamp": timestamp(),
        "uid_error": uid_error,
    }


def _authenticate_block4(conn: Any, key: bytes, key_type: str) -> None:
    if len(key) != KEY_LENGTH:
        raise ValueError("La clave debe contener exactamente 6 bytes.")
    if key_type not in ("A", "B"):
        raise ValueError("El tipo de clave debe ser A o B.")
    key_type_byte = 0x60 if key_type == "A" else 0x61
    _expect_ok(_transmit(conn, [0xFF, 0x82, 0x00, KEY_SLOT, KEY_LENGTH, *key]), "Carga temporal de clave")
    _expect_ok(
        _transmit(conn, [0xFF, 0x86, 0x00, 0x00, 0x05, 0x01, 0x00, LAB_BLOCK, key_type_byte, KEY_SLOT]),
        f"Autenticación del bloque {LAB_BLOCK}",
    )


def _read_block4(conn: Any) -> bytes:
    data = _expect_ok(_transmit(conn, [0xFF, 0xB0, 0x00, LAB_BLOCK, BLOCK_SIZE]), "Lectura del bloque 4")
    if len(data) != BLOCK_SIZE:
        raise OmniError(f"El lector devolvió {len(data)} bytes; se esperaban 16.")
    return bytes(data)


def _write_block4(conn: Any, data: bytes) -> None:
    if len(data) != BLOCK_SIZE:
        raise ValueError("La escritura requiere exactamente 16 bytes.")
    _expect_ok(_transmit(conn, [0xFF, 0xD6, 0x00, LAB_BLOCK, BLOCK_SIZE, *data]), "Escritura del bloque 4")


def _require_mifare_confirmation(identity: dict[str, Any]) -> None:
    if identity["profile"]["status"] == "lf_candidate":
        raise OmniError("Operación bloqueada: el ATR coincide con el perfil LF observado; no usa bloques/claves MIFARE.")


def _make_connection(reader: Any, expected_uid: Optional[str] = None) -> tuple[Any, dict[str, Any]]:
    conn = _connect(reader)
    try:
        identity = _identity(conn)
        if expected_uid and identity["uid"] != expected_uid:
            raise OmniError("La tarjeta presente no coincide con la tarjeta identificada previamente.")
        _require_mifare_confirmation(identity)
        if identity["profile"]["status"] == "unknown":
            raise OmniError("ATR desconocido. Confirma manualmente que es MIFARE Classic de laboratorio antes de continuar.")
        return conn, identity
    except Exception:
        _disconnect(conn)
        raise


def _analyse_bytes(data: bytes) -> dict[str, Any]:
    try:
        utf8 = data.rstrip(b"\x00").decode("utf-8")
    except UnicodeDecodeError:
        utf8 = "[datos binarios / UTF-8 no válido]"
    return {
        "hex": " ".join(f"{b:02X}" for b in data),
        "hex_compact": data.hex().upper(),
        "ascii": "".join(chr(b) if 32 <= b <= 126 else "." for b in data),
        "utf8": utf8,
        "decimal": " ".join(str(b) for b in data),
        "binary": " ".join(f"{b:08b}" for b in data),
        "null_bytes": data.count(0),
        "printable": sum(32 <= b <= 126 for b in data),
    }


def _test_auth_targets_block4() -> bool:
    class FakeConnection:
        def __init__(self) -> None:
            self.apdus: list[list[int]] = []
        def transmit(self, apdu: list[int]) -> tuple[list[int], int, int]:
            self.apdus.append(list(apdu))
            return [], 0x90, 0x00
    fake = FakeConnection()
    _authenticate_block4(fake, bytes.fromhex("FFFFFFFFFFFF"), "A")
    return len(fake.apdus) == 2 and fake.apdus[0][3] == KEY_SLOT and fake.apdus[1][7] == LAB_BLOCK


def _test_read_targets_block4() -> bool:
    class FakeConnection:
        def __init__(self) -> None:
            self.apdus: list[list[int]] = []
        def transmit(self, apdu: list[int]) -> tuple[list[int], int, int]:
            self.apdus.append(list(apdu))
            return list(range(16)), 0x90, 0x00
    fake = FakeConnection()
    data = _read_block4(fake)
    return len(data) == BLOCK_SIZE and fake.apdus == [[0xFF, 0xB0, 0x00, LAB_BLOCK, BLOCK_SIZE]]


def _test_write_targets_block4() -> bool:
    class FakeConnection:
        def __init__(self) -> None:
            self.apdus: list[list[int]] = []
        def transmit(self, apdu: list[int]) -> tuple[list[int], int, int]:
            self.apdus.append(list(apdu))
            return [], 0x90, 0x00
    fake = FakeConnection()
    data = bytes(range(16))
    _write_block4(fake, data)
    return len(fake.apdus) == 1 and fake.apdus[0][:5] == [0xFF, 0xD6, 0x00, LAB_BLOCK, BLOCK_SIZE] and fake.apdus[0][5:] == list(data)


def _test_lf_profile_blocked() -> bool:
    sample = classify_technology("3B 8F 80 01 80 4F 0C A0 00 00 03 06 40 00 00 00 00 00 00 28")
    try:
        _require_mifare_confirmation({"profile": sample})
    except OmniError:
        return True
    return False


def _self_test_results() -> list[tuple[str, bool]]:
    """Pruebas locales deterministas; no requieren lector ni tarjeta físicos."""
    tests: list[tuple[str, Callable[[], bool]]] = [
        ("HEX válido de 16 bytes", lambda: len(validate_hex_block("00" * 16)) == 16),
        ("Rechazo de HEX incompleto", lambda: _raises(lambda: validate_hex_block("AABB"))),
        ("Texto UTF-8 con relleno", lambda: text_to_block("LAB-TEST").startswith(b"LAB-TEST") and len(text_to_block("LAB-TEST")) == 16),
        ("Límite de texto de 16 bytes", lambda: _raises(lambda: text_to_block("X" * 17))),
        ("UID de cinco bytes", lambda: uid_to_bytes("30 00 45 63 B0") == bytes.fromhex("30004563B0")),
        ("Rechazo de UID irregular", lambda: _raises(lambda: uid_to_bytes("ABC"))),
        ("Perfil LF indicativo", lambda: classify_technology("3B 8F 80 01 80 4F 0C A0 00 00 03 06 40 00 00 00 00 00 00 28")["status"] == "lf_candidate"),
        ("ATR desconocido no se etiqueta MIFARE", lambda: classify_technology("3B 00")["status"] == "unknown"),
        ("Análisis de bloque de 16 bytes", lambda: _analyse_bytes(text_to_block("LAB-TEST"))["utf8"] == "LAB-TEST"),
        ("Autenticación dirigida al bloque 4", _test_auth_targets_block4),
        ("Lectura limitada al bloque 4", _test_read_targets_block4),
        ("Escritura limitada al bloque 4", _test_write_targets_block4),
        ("Perfil LF bloqueado para MIFARE", _test_lf_profile_blocked),
    ]
    results: list[tuple[str, bool]] = []
    for name, test in tests:
        try:
            results.append((name, bool(test())))
        except Exception:
            results.append((name, False))
    return results


def _self_tests() -> tuple[int, int]:
    results = _self_test_results()
    return sum(1 for _, passed in results if passed), len(results)


def _raises(fn: Callable[[], Any]) -> bool:
    try:
        fn()
    except (ValueError, OmniError):
        return True
    return False


class OmniDesk:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(f"{APP_NAME} {VERSION} — RFID Operations Center")
        try:
            resource_root = Path(getattr(sys, "_MEIPASS", Path(__file__).resolve().parent))
            icon_path = resource_root / "assets" / "omnidesk.ico"
            if icon_path.exists():
                self.root.iconbitmap(default=str(icon_path))
        except (tk.TclError, OSError):
            pass
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        initial_w = min(1460, max(1024, screen_w - 70))
        initial_h = min(920, max(650, screen_h - 90))
        self.root.geometry(f"{initial_w}x{initial_h}")
        self.root.minsize(min(1024, max(900, screen_w - 24)), min(640, max(580, screen_h - 35)))
        try:
            # Let Tk respect platform DPI while remaining crisp on Windows displays.
            self.root.tk.call("tk", "scaling", max(1.0, min(2.0, self.root.winfo_fpixels("1i") / 72.0)))
        except tk.TclError:
            pass
        self.root.configure(bg=C["bg"])
        self.base_dir = (Path(sys.executable).resolve().parent
                         if getattr(sys, "frozen", False)
                         else Path(__file__).resolve().parent)
        if os.name == "nt":
            data_root = Path(os.getenv("LOCALAPPDATA", str(Path.home() / "AppData" / "Local"))) / "OmniDesk"
        else:
            data_root = self.base_dir
        self.registry_dir = data_root / "omnidesk_registry"
        self.reports_dir = data_root / "omnidesk_reports"
        try:
            self.registry_dir.mkdir(parents=True, exist_ok=True)
            self.reports_dir.mkdir(parents=True, exist_ok=True)
        except OSError:
            # Folder creation is retried by the relevant save/export operation.
            pass
        self.reader_objects: list[Any] = []
        self.reader_var = tk.StringVar(value="Sin lector seleccionado")
        self.selected_reader: Any = None
        self.current_identity: Optional[dict[str, Any]] = None
        self.last_result: Optional[dict[str, Any]] = None
        self.last_data: Optional[bytes] = None
        self.last_event = "Aplicación iniciada"
        self.busy = False
        self.monitor_enabled = True
        self.card_present = False
        self.last_seen_uid = ""
        self.events: queue.Queue[tuple[str, Any]] = queue.Queue()
        self.session_started = timestamp()
        self.log_entries: list[dict[str, str]] = []
        self.console_font_size = 10
        self.console_expanded = False
        self.console_restore_y: Optional[int] = None
        self.log_filter_var = tk.StringVar(value="Todos")
        self.nav_buttons: dict[str, tk.Button] = {}
        self.active_page = "Resumen"
        self.page_titles = {
            "Resumen": ("Centro de operaciones", "Vista general del laboratorio y actividad de la sesión."),
            "Tarjetas": ("Identificación RFID", "Consulta UID y ATR, revisa perfiles y monitoriza presencia."),
            "MIFARE": ("Laboratorio MIFARE", "Operaciones controladas sobre el bloque de prueba 4."),
            "Analizador": ("Analizador de datos", "Convierte y examina bloques HEX, ASCII, decimal y binario."),
            "Memoria": ("Mapa de memoria", "Referencia visual de la estructura MIFARE Classic 1K."),
            "Registros": ("Registros y evidencias", "Gestiona los registros locales y exporta informes JSON."),
            "Diagnóstico": ("Salud del sistema", "Comprueba Python, PC/SC, lectores y pruebas internas."),
        }
        self._setup_style()
        self._build_ui()
        self._refresh_readers(silent=True)
        self._log("OMNIDESK iniciado. Las claves no se guardan ni aparecen en el registro.", "info")
        self._set_status("Preparado", "muted")
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(250, self._process_queue)
        self.root.after(900, self._presence_tick)

    # ---------- UI framework ----------
    def _setup_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        # Container styles
        style.configure("TFrame", background=C["bg"])
        style.configure("Panel.TFrame", background=C["panel"])
        style.configure("Panel2.TFrame", background=C["panel2"])
        style.configure("TLabel", background=C["bg"], foreground=C["text"], font=(FONT, 10))
        style.configure("Panel.TLabel", background=C["panel"], foreground=C["text"], font=(FONT, 10))
        style.configure("Muted.TLabel", background=C["panel"], foreground=C["muted"], font=(FONT, 9))
        style.configure("Title.TLabel", background=C["bg"], foreground=C["text"], font=(FONT, 22, "bold"))
        style.configure("SubTitle.TLabel", background=C["bg"], foreground=C["muted"], font=(FONT, 10))

        # Notebook has no native tabs: navigation is handled by the left rail.
        style.layout("NoTabs.TNotebook", [("Notebook.client", {"sticky": "nswe"})])
        style.configure("NoTabs.TNotebook", background=C["bg"], borderwidth=0, tabmargins=0)

        # Buttons and inputs
        style.configure("TButton", background=C["panel3"], foreground=C["text"], borderwidth=0,
                        padding=(12, 9), font=(FONT, 9, "bold"), focuscolor=C["cyan"])
        style.map("TButton", background=[("active", C["nav_hover"]), ("disabled", C["panel"])],
                  foreground=[("disabled", "#60758A")])
        style.configure("Accent.TButton", background=C["cyan2"], foreground="#06151B",
                        padding=(14, 10), font=(FONT, 9, "bold"), borderwidth=0)
        style.map("Accent.TButton", background=[("active", C["cyan"]), ("disabled", C["panel3"])])
        style.configure("Danger.TButton", background="#512D3A", foreground="#FFE9EC",
                        padding=(13, 9), font=(FONT, 9, "bold"), borderwidth=0)
        style.map("Danger.TButton", background=[("active", C["red"])])
        style.configure("TEntry", fieldbackground=C["panel2"], foreground=C["text"],
                        insertcolor=C["text"], bordercolor=C["border"], padding=8, relief="flat")
        style.configure("TCombobox", fieldbackground=C["panel2"], background=C["panel2"],
                        foreground=C["text"], arrowcolor=C["cyan"], padding=7, bordercolor=C["border"])
        style.map("TCombobox", fieldbackground=[("readonly", C["panel2"])],
                  foreground=[("readonly", C["text"])])
        style.configure("TCheckbutton", background=C["panel"], foreground=C["text"],
                        font=(FONT, 9), padding=4)
        style.map("TCheckbutton", background=[("active", C["panel"])],
                  foreground=[("active", C["cyan"])])

        # Data tables
        style.configure("Treeview", background=C["panel2"], fieldbackground=C["panel2"],
                        foreground=C["text"], rowheight=31, borderwidth=0, font=(FONT, 9))
        style.configure("Treeview.Heading", background=C["panel3"], foreground=C["cyan"],
                        font=(FONT, 8, "bold"), relief="flat", padding=(8, 8))
        style.map("Treeview", background=[("selected", C["nav_active"])],
                  foreground=[("selected", C["white"])])
        style.configure("Horizontal.TProgressbar", background=C["cyan"], troughcolor=C["panel2"],
                        bordercolor=C["panel2"], lightcolor=C["cyan"], darkcolor=C["cyan"])
        style.configure("Vertical.TScrollbar", background=C["panel2"], troughcolor=C["panel"],
                        bordercolor=C["panel"], arrowcolor=C["muted"])

    def _card(self, parent: tk.Widget, padding: int = 15) -> ttk.Frame:
        frame = ttk.Frame(parent, style="Panel.TFrame", padding=padding)
        return frame

    def _label(self, parent: tk.Widget, text: str, **kwargs: Any) -> ttk.Label:
        return ttk.Label(parent, text=text, style=kwargs.pop("style", "Panel.TLabel"), **kwargs)

    def _button(self, parent: tk.Widget, text: str, command: Callable[[], Any], style: str = "TButton") -> ttk.Button:
        return ttk.Button(parent, text=text, command=command, style=style)

    def _build_ui(self) -> None:
        # Application shell: persistent navigation rail + focused workspace.
        shell = tk.Frame(self.root, bg=C["bg"])
        shell.pack(fill="both", expand=True)

        sidebar = tk.Frame(shell, bg=C["sidebar"], width=226,
                           highlightthickness=1, highlightbackground=C["border"])
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        self.sidebar = sidebar

        brand = tk.Frame(sidebar, bg=C["sidebar"])
        brand.pack(fill="x", padx=17, pady=(20, 25))
        logo = tk.Canvas(brand, width=52, height=52, bg=C["sidebar"], highlightthickness=0)
        logo.pack(side="left", padx=(0, 10))
        self._draw_logo(logo)
        brand_text = tk.Frame(brand, bg=C["sidebar"])
        brand_text.pack(side="left", fill="y", pady=5)
        tk.Label(brand_text, text="OMNIDESK", bg=C["sidebar"], fg=C["text"],
                 font=(FONT, 15, "bold")).pack(anchor="w")
        tk.Label(brand_text, text="RFID OPERATIONS", bg=C["sidebar"], fg=C["cyan"],
                 font=(FONT, 8, "bold")).pack(anchor="w", pady=(2, 0))
        tk.Label(sidebar, text="MÓDULOS", bg=C["sidebar"], fg="#627A92",
                 font=(FONT, 8, "bold")).pack(anchor="w", padx=20, pady=(0, 8))

        nav_items = [
            ("Resumen", "⌂", "Overview"),
            ("Tarjetas", "◉", "Card intelligence"),
            ("MIFARE", "▦", "MIFARE lab"),
            ("Analizador", "⌘", "Data analyzer"),
            ("Memoria", "▤", "Memory map"),
            ("Registros", "▧", "Evidence vault"),
            ("Diagnóstico", "⟲", "System health"),
        ]
        for name, glyph, _hint in nav_items:
            btn = tk.Button(
                sidebar, text=f"  {glyph}     {name}", anchor="w", command=lambda n=name: self._navigate(n),
                bg=C["sidebar"], fg=C["muted"], activebackground=C["nav_hover"],
                activeforeground=C["text"], relief="flat", bd=0, padx=14, pady=11,
                font=(FONT, 10, "bold"), cursor="hand2", highlightthickness=0,
            )
            btn.pack(fill="x", padx=10, pady=2)
            self.nav_buttons[name] = btn

        spacer = tk.Frame(sidebar, bg=C["sidebar"])
        spacer.pack(fill="both", expand=True)
        rail_divider = tk.Frame(sidebar, bg=C["border"], height=1)
        rail_divider.pack(fill="x", padx=16, pady=(0, 12))
        lab_box = tk.Frame(sidebar, bg=C["panel"], padx=13, pady=12,
                           highlightthickness=1, highlightbackground=C["border"])
        lab_box.pack(fill="x", padx=12, pady=(0, 16))
        tk.Label(lab_box, text="●  MODO LAB LOCAL", bg=C["panel"], fg=C["green"],
                 font=(FONT, 8, "bold")).pack(anchor="w")
        tk.Label(lab_box, text="Bloque 04 únicamente\nClaves no almacenadas", bg=C["panel"],
                 fg=C["muted"], justify="left", font=(FONT, 8), pady=7,
                 wraplength=160).pack(anchor="w")
        tk.Label(sidebar, text=f"DESKTOP  {VERSION}", bg=C["sidebar"], fg="#5F7489",
                 font=(MONO, 8)).pack(anchor="w", padx=20, pady=(0, 16))

        # Main work area
        main = tk.Frame(shell, bg=C["bg"], padx=19, pady=15)
        main.pack(side="left", fill="both", expand=True)
        self.main_area = main

        topbar = tk.Frame(main, bg=C["bg"], height=64)
        topbar.pack(fill="x", pady=(0, 12))
        topbar.pack_propagate(False)
        heading = tk.Frame(topbar, bg=C["bg"])
        heading.pack(side="left", fill="y")
        self.page_title_label = tk.Label(heading, text="Centro de operaciones", bg=C["bg"],
                                         fg=C["text"], font=(FONT, 19, "bold"))
        self.page_title_label.pack(anchor="w")
        self.page_desc_label = tk.Label(heading, text="Vista general del laboratorio y actividad de la sesión.",
                                        bg=C["bg"], fg=C["muted"], font=(FONT, 9))
        self.page_desc_label.pack(anchor="w", pady=(3, 0))

        status_box = tk.Frame(topbar, bg=C["panel"], padx=12, pady=9,
                              highlightthickness=1, highlightbackground=C["border"])
        status_box.pack(side="right", pady=3)
        self.status_dot = tk.Label(status_box, text="●", bg=C["panel"], fg=C["yellow"], font=(FONT, 11))
        self.status_dot.pack(side="left", padx=(0, 7))
        self.status_text = tk.Label(status_box, text="INICIANDO", bg=C["panel"], fg=C["muted"],
                                    font=(FONT, 8, "bold"))
        self.status_text.pack(side="left")

        # Persistent device selector
        reader_bar = tk.Frame(main, bg=C["panel"], padx=12, pady=10,
                              highlightthickness=1, highlightbackground=C["border"])
        reader_bar.pack(fill="x", pady=(0, 12))
        tk.Label(reader_bar, text="LECTOR PC/SC", bg=C["panel"], fg=C["cyan"],
                 font=(FONT, 8, "bold")).pack(side="left", padx=(0, 12))
        self.reader_combo = ttk.Combobox(reader_bar, textvariable=self.reader_var,
                                         state="readonly", width=48)
        self.reader_combo.pack(side="left", padx=(0, 8))
        self._button(reader_bar, "↻  Actualizar", self._refresh_readers).pack(side="left", padx=3)
        self._button(reader_bar, "Seleccionar lector", self._select_reader, "Accent.TButton").pack(side="left", padx=3)
        self.reader_state_label = tk.Label(reader_bar, text="SIN LECTOR", bg=C["panel"],
                                           fg=C["muted"], font=(FONT, 8, "bold"))
        self.reader_state_label.pack(side="right", padx=8)

        # Resizable workspace + activity monitor. The user can drag the sash,
        # enlarge the log, change its font size and export the full session.
        self.workspace_split = tk.PanedWindow(
            main, orient="vertical", bg=C["border"], bd=0, relief="flat",
            sashwidth=9, sashpad=1, handlesize=8, showhandle=False,
            sashrelief="flat", opaqueresize=True, sashcursor="sb_v_double_arrow",
        )
        self.workspace_split.pack(fill="both", expand=True)

        # Stacked workspace pages. Sidebar is the only navigation source.
        self.content_container = tk.Frame(self.workspace_split, bg=C["bg"])
        self.pages: dict[str, ttk.Frame] = {}
        for name in ("Resumen", "Tarjetas", "MIFARE", "Analizador", "Memoria", "Registros", "Diagnóstico"):
            page = ttk.Frame(self.content_container, padding=13)
            page.place(relx=0, rely=0, relwidth=1, relheight=1)
            self.pages[name] = page
        self._build_dashboard()
        self._build_cards_page()
        self._build_mifare_page()
        self._build_analyzer_page()
        self._build_memory_page()
        self._build_registry_page()
        self._build_diagnostics_page()

        self.footer = tk.Frame(self.workspace_split, bg=C["panel"],
                               highlightthickness=1, highlightbackground=C["border"])
        self._build_activity_console(self.footer)
        self.workspace_split.add(self.content_container, minsize=250, stretch="always")
        self.workspace_split.add(self.footer, minsize=165, stretch="never")
        self.root.after(350, self._set_initial_splitter_position)

        self._navigate("Resumen", log=False)
        self.root.bind("<Control-1>", lambda _e: self._navigate("Resumen"))
        self.root.bind("<Control-2>", lambda _e: self._navigate("Tarjetas"))
        self.root.bind("<Control-3>", lambda _e: self._navigate("MIFARE"))
        self.root.bind("<Control-4>", lambda _e: self._navigate("Analizador"))
        self.root.bind("<Control-5>", lambda _e: self._navigate("Memoria"))
        self.root.bind("<Control-6>", lambda _e: self._navigate("Registros"))
        self.root.bind("<Control-7>", lambda _e: self._navigate("Diagnóstico"))
        self.root.bind("<F5>", lambda _e: self._refresh_readers())
        self.root.bind("<Control-l>", lambda _e: self._identify_card())
        self.root.bind("<Control-Shift-equal>", lambda _e: self._console_font_up())
        self.root.bind("<Control-minus>", lambda _e: self._console_font_down())
        self.root.bind("<Control-Shift-x>", lambda _e: self._toggle_console_expand())

    def _draw_logo(self, canvas: tk.Canvas) -> None:
        # Original OMNIDESK mark: shield/chip + radio arcs. No external assets required.
        canvas.create_oval(2, 2, 50, 50, fill="#102B3A", outline=C["border"], width=1)
        canvas.create_polygon(14, 12, 28, 7, 42, 12, 40, 31, 28, 43, 16, 31,
                              fill="#0D2432", outline=C["cyan"], width=1.6)
        canvas.create_rectangle(21, 17, 34, 31, outline=C["cyan"], width=1.5)
        for y in (21, 24, 27):
            canvas.create_line(24, y, 31, y, fill=C["cyan"], width=1)
        for x in (23, 28, 33):
            canvas.create_line(x, 13, x, 17, fill=C["cyan"], width=1)
            canvas.create_line(x, 31, x, 35, fill=C["cyan"], width=1)
        canvas.create_arc(28, 5, 56, 47, start=292, extent=136, style="arc", outline=C["cyan"], width=1.8)
        canvas.create_arc(33, 0, 63, 52, start=292, extent=136, style="arc", outline=C["cyan2"], width=1.5)
        canvas.create_oval(43, 24, 48, 29, fill=C["green"], outline="")

    def _navigate(self, name: str, log: bool = True) -> None:
        if name not in self.pages:
            return
        self.active_page = name
        self.pages[name].tkraise()
        title, description = self.page_titles.get(name, (name, ""))
        self.page_title_label.configure(text=title)
        self.page_desc_label.configure(text=description)
        for page_name, button in self.nav_buttons.items():
            selected = page_name == name
            button.configure(
                bg=C["nav_active"] if selected else C["sidebar"],
                fg=C["cyan"] if selected else C["muted"],
                activebackground=C["nav_hover"],
            )
        if log:
            self.last_event = f"Sección abierta: {name}"

    def _clear_console(self) -> None:
        self.console.configure(state="normal")
        self.console.delete("1.0", "end")
        self.console.configure(state="disabled")
        self._log("Consola de actividad limpiada.", "info")

    def _build_dashboard(self) -> None:
        page = self.pages["Resumen"]
        hero = tk.Frame(page, bg=C["panel"], padx=22, pady=20, highlightthickness=1, highlightbackground=C["border"])
        hero.pack(fill="x", pady=(0, 13))
        accent = tk.Frame(hero, bg=C["cyan"], width=4)
        accent.pack(side="left", fill="y", padx=(0, 17))
        hero_text = tk.Frame(hero, bg=C["panel"])
        hero_text.pack(side="left", fill="both", expand=True)
        tk.Label(hero_text, text="RFID OPERATIONS CENTER", bg=C["panel"], fg=C["text"], font=(FONT, 18, "bold")).pack(anchor="w")
        tk.Label(hero_text, text="Identifica, inspecciona y documenta tarjetas de laboratorio desde un único entorno.", bg=C["panel"], fg=C["muted"], font=(FONT, 10)).pack(anchor="w", pady=(5, 12))
        actions = tk.Frame(hero_text, bg=C["panel"])
        actions.pack(anchor="w")
        self._button(actions, "Identificar tarjeta", self._identify_card, "Accent.TButton").pack(side="left", padx=(0, 8))
        self._button(actions, "Diagnóstico rápido", self._run_quick_diagnostic).pack(side="left", padx=4)
        self._button(actions, "Abrir MIFARE Lab", lambda: self._navigate("MIFARE")).pack(side="left", padx=4)

        cards = tk.Frame(page, bg=C["bg"])
        cards.pack(fill="x")
        self.metric_vars: dict[str, tk.StringVar] = {}
        metrics = [("LECTOR", "reader"), ("ESTADO TARJETA", "card"), ("TECNOLOGÍA", "technology"), ("ÚLTIMA OPERACIÓN", "operation")]
        for title_text, key in metrics:
            tile = tk.Frame(cards, bg=C["panel2"], padx=14, pady=12, highlightthickness=1, highlightbackground=C["border"])
            tile.pack(side="left", fill="both", expand=True, padx=(0, 8))
            tk.Frame(tile, bg=C["cyan"], height=2).pack(fill="x", pady=(0, 9))
            tk.Label(tile, text=title_text, bg=C["panel2"], fg=C["muted"], font=(FONT, 8, "bold")).pack(anchor="w")
            var = tk.StringVar(value="—")
            self.metric_vars[key] = var
            tk.Label(tile, textvariable=var, bg=C["panel2"], fg=C["cyan"], font=(FONT, 10, "bold"), wraplength=190, justify="left").pack(anchor="w", pady=(8, 0))

        lower = tk.Frame(page, bg=C["bg"])
        lower.pack(fill="both", expand=True, pady=(14, 0))
        left = self._card(lower, 14)
        left.pack(side="left", fill="both", expand=True, padx=(0, 7))
        self._label(left, "TARJETA ACTUAL", style="Muted.TLabel").pack(anchor="w")
        self.identity_text = tk.Text(left, height=9, bg=C["panel2"], fg=C["text"], relief="flat", wrap="word", font=(MONO, 9), padx=10, pady=9)
        self.identity_text.pack(fill="both", expand=True, pady=(8, 0))
        self.identity_text.insert("1.0", "Todavía no se ha identificado ninguna tarjeta.\n\nAcerca una tarjeta al lector y pulsa 'Identificar tarjeta'.")
        self.identity_text.configure(state="disabled")
        right = self._card(lower, 14)
        right.pack(side="left", fill="both", expand=True, padx=(7, 0))
        self._label(right, "FLUJO RECOMENDADO", style="Muted.TLabel").pack(anchor="w")
        for n, text in [("01", "Detecta el lector y selecciona el dispositivo."), ("02", "Identifica UID y ATR; revisa el perfil orientativo."), ("03", "Para MIFARE, confirma que es una tarjeta propia de laboratorio."), ("04", "Usa una clave conocida; lectura/escritura solo en bloque 4."), ("05", "Documenta los resultados sin guardar claves.")]:
            row = tk.Frame(right, bg=C["panel"])
            row.pack(fill="x", pady=5)
            tk.Label(row, text=n, bg=C["panel3"], fg=C["cyan"], font=(MONO, 9, "bold"), width=4, pady=4).pack(side="left", padx=(0, 9))
            tk.Label(row, text=text, bg=C["panel"], fg=C["text"], font=(FONT, 9), wraplength=320, justify="left").pack(side="left", fill="x", expand=True)

    def _build_cards_page(self) -> None:
        page = self.pages["Tarjetas"]
        top = self._card(page)
        top.pack(fill="x", pady=(0, 10))
        self._label(top, "IDENTIFICACIÓN Y MONITORIZACIÓN", style="Muted.TLabel").pack(anchor="w")
        row = ttk.Frame(top, style="Panel.TFrame")
        row.pack(fill="x", pady=(10, 0))
        self._button(row, "Identificar ahora", self._identify_card, "Accent.TButton").pack(side="left", padx=(0, 7))
        self._button(row, "Registrar tarjeta…", self._register_card).pack(side="left", padx=4)
        self.monitor_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(row, text="Monitor de presencia automático", variable=self.monitor_var, command=self._toggle_monitor).pack(side="right")
        info = self._card(page)
        info.pack(fill="both", expand=True)
        self._label(info, "DETALLES DE LA ÚLTIMA TARJETA", style="Muted.TLabel").pack(anchor="w")
        self.card_tree = ttk.Treeview(info, columns=("field", "value"), show="headings", height=10)
        self.card_tree.heading("field", text="CAMPO")
        self.card_tree.heading("value", text="VALOR")
        self.card_tree.column("field", width=180, anchor="w")
        self.card_tree.column("value", width=760, anchor="w")
        self.card_tree.pack(fill="both", expand=True, pady=(9, 0))

    def _build_mifare_page(self) -> None:
        page = self.pages["MIFARE"]
        warning = tk.Frame(page, bg="#3B2C20", padx=12, pady=10, highlightthickness=1, highlightbackground="#76532C")
        warning.pack(fill="x", pady=(0, 10))
        tk.Label(warning, text="LABORATORIO MIFARE · BLOQUE 4 EXCLUSIVAMENTE", bg="#3B2C20", fg=C["yellow"], font=(FONT, 10, "bold")).pack(anchor="w")
        tk.Label(warning, text="Usa solo tarjetas propias de prueba y claves A/B que ya conozcas. No se inspeccionan tráileres ni bloque fabricante.", bg="#3B2C20", fg="#F5DDB4", font=(FONT, 9), wraplength=1000, justify="left").pack(anchor="w", pady=(4, 0))
        split = tk.Frame(page, bg=C["bg"])
        split.pack(fill="both", expand=True)
        left = self._card(split, 14)
        left.pack(side="left", fill="y", padx=(0, 8))
        self._label(left, "OPERACIONES", style="Muted.TLabel").pack(anchor="w", pady=(0, 9))
        self._button(left, "Leer bloque 4", self._read_block, "Accent.TButton").pack(fill="x", pady=4)
        self._button(left, "Verificar clave conocida", self._verify_key).pack(fill="x", pady=4)
        self._button(left, "Escribir bloque 4…", self._write_block, "Danger.TButton").pack(fill="x", pady=4)
        self._button(left, "Comparar bloque 4…", self._compare_block).pack(fill="x", pady=4)
        self._button(left, "Analizar última lectura", self._analyse_last).pack(fill="x", pady=4)
        self._label(left, "TIPO DE CLAVE", style="Muted.TLabel").pack(anchor="w", pady=(16, 4))
        self.key_type_var = tk.StringVar(value="A")
        ttk.Combobox(left, textvariable=self.key_type_var, values=("A", "B"), state="readonly", width=6).pack(anchor="w")
        self._label(left, "La clave se solicitará en cada operación y no se guardará.", style="Muted.TLabel").pack(anchor="w", pady=(10, 0))
        right = self._card(split, 14)
        right.pack(side="left", fill="both", expand=True)
        self._label(right, "DATOS DEL BLOQUE DE LABORATORIO", style="Muted.TLabel").pack(anchor="w")
        self.block_view = tk.Text(right, bg=C["panel2"], fg=C["text"], relief="flat", wrap="none", font=(MONO, 10), padx=12, pady=12, height=12)
        self.block_view.pack(fill="both", expand=True, pady=(8, 8))
        self.block_view.insert("1.0", "Esperando lectura…\n\nEl laboratorio utiliza únicamente el bloque 4 (16 bytes).")
        self.block_view.configure(state="disabled")
        self.block_status = self._label(right, "Sin lectura en esta sesión", style="Muted.TLabel")
        self.block_status.pack(anchor="w")

    def _build_analyzer_page(self) -> None:
        page = self.pages["Analizador"]
        top = self._card(page)
        top.pack(fill="x", pady=(0, 10))
        self._label(top, "CONVERSOR HEX ⇄ TEXTO", style="Muted.TLabel").pack(anchor="w")
        self.hex_input = tk.StringVar(value="4C41422D544553540000000000000000")
        entryrow = ttk.Frame(top, style="Panel.TFrame")
        entryrow.pack(fill="x", pady=(9, 7))
        ttk.Entry(entryrow, textvariable=self.hex_input).pack(side="left", fill="x", expand=True, padx=(0, 8))
        self._button(entryrow, "HEX → análisis", self._analyse_hex, "Accent.TButton").pack(side="left", padx=3)
        self.text_input = tk.StringVar(value="LAB-TEST")
        textrow = ttk.Frame(top, style="Panel.TFrame")
        textrow.pack(fill="x")
        ttk.Entry(textrow, textvariable=self.text_input).pack(side="left", fill="x", expand=True, padx=(0, 8))
        self._button(textrow, "Texto → HEX", self._convert_text).pack(side="left", padx=3)
        result = self._card(page)
        result.pack(fill="both", expand=True)
        self._label(result, "RESULTADO", style="Muted.TLabel").pack(anchor="w")
        self.analysis_view = tk.Text(result, bg=C["panel2"], fg=C["text"], relief="flat", wrap="word", font=(MONO, 9), padx=12, pady=10)
        self.analysis_view.pack(fill="both", expand=True, pady=(8, 0))
        self.analysis_view.insert("1.0", "Introduce 16 bytes en hexadecimal para analizar un bloque, o texto de hasta 16 bytes para convertirlo.")
        self.analysis_view.configure(state="disabled")

    def _build_memory_page(self) -> None:
        page = self.pages["Memoria"]
        intro = self._card(page)
        intro.pack(fill="x", pady=(0, 10))
        self._label(intro, "MAPA DE REFERENCIA · MIFARE CLASSIC 1K", style="Muted.TLabel").pack(anchor="w")
        tk.Label(intro, text="16 sectores × 4 bloques × 16 bytes. Vista de referencia; no implica que se haya leído toda la tarjeta.", bg=C["panel"], fg=C["muted"], font=(FONT, 9)).pack(anchor="w", pady=(5, 0))
        grid = self._card(page)
        grid.pack(fill="both", expand=True)
        for col, text in enumerate(("SECTOR", "BLOQUE 0", "BLOQUE 1", "BLOQUE 2", "BLOQUE 3")):
            tk.Label(grid, text=text, bg=C["panel3"], fg=C["cyan"], font=(FONT, 8, "bold"), padx=8, pady=7).grid(row=0, column=col, sticky="nsew", padx=2, pady=2)
            grid.grid_columnconfigure(col, weight=1)
        for sector in range(16):
            tk.Label(grid, text=f"{sector:02d}", bg=C["panel2"], fg=C["text"], font=(MONO, 9, "bold"), pady=5).grid(row=sector + 1, column=0, sticky="nsew", padx=2, pady=2)
            for offset in range(4):
                block = sector * 4 + offset
                if sector == 0 and offset == 0:
                    label, bg, fg = f"{block:02d} · FABRICANTE", "#4A3038", "#FFD7DE"
                elif offset == 3:
                    label, bg, fg = f"{block:02d} · TRÁILER", "#473A27", "#F6D58B"
                elif block == LAB_BLOCK:
                    label, bg, fg = f"{block:02d} · LAB", "#174B51", C["cyan"]
                else:
                    label, bg, fg = f"{block:02d} · DATOS", C["panel2"], C["text"]
                tk.Label(grid, text=label, bg=bg, fg=fg, font=(MONO, 8), padx=6, pady=5).grid(row=sector + 1, column=offset + 1, sticky="nsew", padx=2, pady=2)
        note = tk.Label(page, text="OMNIDESK solo opera sobre el bloque 4. No lee ni modifica bloque fabricante ni tráileres.", bg=C["bg"], fg=C["yellow"], font=(FONT, 9, "bold"))
        note.pack(anchor="w", pady=(8, 0))

    def _build_registry_page(self) -> None:
        page = self.pages["Registros"]
        controls = self._card(page)
        controls.pack(fill="x", pady=(0, 10))
        self._label(controls, "REGISTRO LOCAL DE TARJETAS E INFORMES", style="Muted.TLabel").pack(anchor="w")
        row = ttk.Frame(controls, style="Panel.TFrame")
        row.pack(fill="x", pady=(9, 0))
        self._button(row, "Registrar tarjeta actual…", self._register_card, "Accent.TButton").pack(side="left", padx=(0, 7))
        self._button(row, "Exportar último resultado…", self._export_report).pack(side="left", padx=4)
        self._button(row, "Abrir carpeta de registros", self._open_registry_folder).pack(side="left", padx=4)
        self._button(row, "Abrir carpeta de informes", self._open_reports_folder).pack(side="left", padx=4)
        list_card = self._card(page)
        list_card.pack(fill="both", expand=True)
        self._label(list_card, "ARCHIVOS LOCALES", style="Muted.TLabel").pack(anchor="w")
        self.registry_tree = ttk.Treeview(list_card, columns=("file", "kind", "date", "size"), show="headings", height=12)
        for col, heading, width in (("file", "ARCHIVO", 380), ("kind", "TIPO", 150), ("date", "MODIFICADO", 190), ("size", "TAMAÑO", 100)):
            self.registry_tree.heading(col, text=heading)
            self.registry_tree.column(col, width=width, anchor="w")
        self.registry_tree.pack(fill="both", expand=True, pady=(8, 0))
        self.registry_tree.bind("<Double-1>", self._open_selected_json)
        self._refresh_files()

    def _build_diagnostics_page(self) -> None:
        page = self.pages["Diagnóstico"]
        top = self._card(page)
        top.pack(fill="x", pady=(0, 10))
        self._label(top, "DIAGNÓSTICO DEL ENTORNO", style="Muted.TLabel").pack(anchor="w")
        row = ttk.Frame(top, style="Panel.TFrame")
        row.pack(fill="x", pady=(8, 0))
        self._button(row, "Ejecutar diagnóstico", self._run_quick_diagnostic, "Accent.TButton").pack(side="left", padx=(0, 7))
        self._button(row, "Autopruebas", self._run_self_tests).pack(side="left")
        result = self._card(page)
        result.pack(fill="both", expand=True)
        self.diag_view = tk.Text(result, bg=C["panel2"], fg=C["text"], relief="flat", wrap="word", font=(MONO, 9), padx=12, pady=10)
        self.diag_view.pack(fill="both", expand=True)
        self.diag_view.insert("1.0", "Pulsa 'Ejecutar diagnóstico' para consultar el entorno y el estado de PC/SC.")
        self.diag_view.configure(state="disabled")

    # ---------- UI helpers ----------
    def _set_text(self, widget: tk.Text, value: str) -> None:
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        widget.insert("1.0", value)
        widget.configure(state="disabled")

    def _build_activity_console(self, parent: tk.Widget) -> None:
        """Create a modern, resizable activity dock with readable typography."""
        header = tk.Frame(parent, bg=C["panel"])
        header.pack(fill="x", padx=14, pady=(9, 3))

        title_group = tk.Frame(header, bg=C["panel"])
        title_group.pack(side="left", fill="x", expand=True)
        tk.Label(title_group, text="ACTIVITY CENTER", bg=C["panel"], fg=C["text"],
                 font=(FONT, 10, "bold")).pack(side="left")
        self.console_state = tk.Label(title_group, text="● LOCAL SESSION", bg=C["panel"], fg=C["green"],
                                      font=(FONT, 8, "bold"))
        self.console_state.pack(side="left", padx=(12, 0))
        self.console_count_label = tk.Label(title_group, text="0 eventos", bg=C["panel"], fg=C["muted"],
                                            font=(FONT, 8))
        self.console_count_label.pack(side="left", padx=(10, 0))

        controls = tk.Frame(header, bg=C["panel"])
        controls.pack(side="right")
        tk.Label(controls, text="FILTRO", bg=C["panel"], fg=C["muted"],
                 font=(FONT, 7, "bold")).pack(side="left", padx=(0, 5))
        self.log_filter_combo = ttk.Combobox(
            controls, textvariable=self.log_filter_var,
            values=("Todos", "Info", "Éxito", "Aviso", "Error"),
            state="readonly", width=9,
        )
        self.log_filter_combo.pack(side="left", padx=(0, 8))
        self.log_filter_combo.bind("<<ComboboxSelected>>", lambda _e: self._render_console())

        self._console_button(controls, "A−", self._console_font_down, width=3).pack(side="left", padx=2)
        self._console_button(controls, "A+", self._console_font_up, width=3).pack(side="left", padx=2)
        self._console_button(controls, "Copiar", self._copy_console).pack(side="left", padx=2)
        self._console_button(controls, "Exportar", self._export_console).pack(side="left", padx=2)
        self._console_button(controls, "Limpiar", self._clear_console).pack(side="left", padx=2)
        self.console_expand_button = self._console_button(controls, "Ampliar", self._toggle_console_expand,
                                                           active=True)
        self.console_expand_button.pack(side="left", padx=(5, 0))

        separator = tk.Frame(parent, bg=C["border"], height=1)
        separator.pack(fill="x", padx=12, pady=(3, 5))

        body = tk.Frame(parent, bg=C["bg"])
        body.pack(fill="both", expand=True, padx=12, pady=(0, 10))
        body.grid_rowconfigure(0, weight=1)
        body.grid_columnconfigure(0, weight=1)
        self.console = tk.Text(
            body, height=8, bg="#07111E", fg=C["text"], insertbackground=C["text"],
            relief="flat", wrap="word", font=(MONO, self.console_font_size),
            padx=14, pady=11, state="disabled", borderwidth=0,
            selectbackground=C["nav_active"], selectforeground=C["white"],
            highlightthickness=1, highlightbackground=C["border"],
            highlightcolor=C["cyan"], spacing1=2, spacing3=2,
        )
        self.console.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(body, orient="vertical", command=self.console.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.console.configure(yscrollcommand=scroll.set)
        self.console.tag_configure("timestamp", foreground="#71869B")
        self.console.tag_configure("info", foreground="#C4D2E0")
        self.console.tag_configure("ok", foreground=C["green"])
        self.console.tag_configure("warn", foreground=C["yellow"])
        self.console.tag_configure("error", foreground=C["red"])
        self.console.tag_configure("system", foreground=C["cyan"])
        self.console.insert("1.0", "  OMNIDESK ACTIVITY CENTER  ·  Los eventos de la sesión aparecerán aquí.\n", "system")
        self.console.configure(state="disabled")

        hint = tk.Label(parent, text="ARRASTRA EL SEPARADOR PARA CAMBIAR LA ALTURA  ·  A+/A− AJUSTA LA LEGIBILIDAD",
                        bg=C["panel"], fg="#6E849A", font=(FONT, 7, "bold"))
        hint.pack(anchor="e", padx=15, pady=(0, 5))

    def _console_button(self, parent: tk.Widget, text: str, command: Callable[[], Any],
                        width: Optional[int] = None, active: bool = False) -> tk.Button:
        return tk.Button(
            parent, text=text, command=command, width=width,
            bg=C["nav_active"] if active else C["panel2"],
            fg=C["cyan"] if active else C["muted"],
            activebackground=C["nav_hover"], activeforeground=C["text"],
            relief="flat", bd=0, padx=9, pady=5,
            font=(FONT, 8, "bold"), cursor="hand2", highlightthickness=0,
        )

    def _set_initial_splitter_position(self) -> None:
        try:
            height = self.workspace_split.winfo_height()
            if height > 250:
                self.workspace_split.sash_place(0, 0, max(250, height - 245))
        except tk.TclError:
            pass

    def _toggle_console_expand(self) -> None:
        try:
            if not self.console_expanded:
                try:
                    _x, self.console_restore_y = self.workspace_split.sash_coord(0)
                except (tk.TclError, TypeError):
                    self.console_restore_y = max(250, self.workspace_split.winfo_height() - 235)
                # Removing the workspace pane gives the activity console the full
                # available height; unlike squeezing the sash, this works even
                # when page widgets request a large minimum height.
                self.workspace_split.forget(self.content_container)
                self.workspace_split.paneconfigure(self.footer, stretch="always")
                self.console_expanded = True
                self.console_expand_button.configure(text="Restaurar")
                self._log("Registro de actividad ampliado a pantalla de trabajo.", "info")
            else:
                self.workspace_split.paneconfigure(self.footer, stretch="never")
                self.workspace_split.add(self.content_container, before=self.footer,
                                         minsize=250, stretch="always")
                self.console_expanded = False
                self.console_expand_button.configure(text="Ampliar")
                self.root.after_idle(self._restore_workspace_sash)
                self._log("Vista de trabajo restaurada.", "info")
        except tk.TclError as exc:
            self._log(f"No se pudo cambiar el tamaño del registro: {exc}", "warn")

    def _restore_workspace_sash(self) -> None:
        try:
            height = self.workspace_split.winfo_height()
            target = self.console_restore_y if self.console_restore_y is not None else height - 235
            target = max(250, min(int(target), max(250, height - 165)))
            self.workspace_split.sash_place(0, 0, target)
        except (tk.TclError, TypeError, ValueError):
            pass

    def _console_font_up(self) -> None:
        self.console_font_size = min(16, self.console_font_size + 1)
        self.console.configure(font=(MONO, self.console_font_size))

    def _console_font_down(self) -> None:
        self.console_font_size = max(8, self.console_font_size - 1)
        self.console.configure(font=(MONO, self.console_font_size))

    def _visible_log_entries(self) -> list[dict[str, str]]:
        selected = self.log_filter_var.get() if hasattr(self, "log_filter_var") else "Todos"
        level_map = {"Info": "info", "Éxito": "ok", "Aviso": "warn", "Error": "error"}
        wanted = level_map.get(selected)
        return [entry for entry in self.log_entries if wanted is None or entry["level"] == wanted]

    def _render_console(self) -> None:
        if not hasattr(self, "console"):
            return
        entries = self._visible_log_entries()
        self.console.configure(state="normal")
        self.console.delete("1.0", "end")
        for entry in entries:
            self.console.insert("end", f"{entry['time']}  ", "timestamp")
            self.console.insert("end", f"{entry['message']}\n", entry["level"])
        if not entries:
            self.console.insert("end", "No hay eventos para este filtro.\n", "system")
        self.console.see("end")
        self.console.configure(state="disabled")
        total = len(self.log_entries)
        self.console_count_label.configure(text=f"{len(entries)} visibles / {total} eventos")

    def _log(self, message: str, level: str = "info") -> None:
        if level not in ("info", "ok", "warn", "error"):
            level = "info"
        entry = {"time": madrid_now().strftime("%H:%M:%S"), "message": str(message), "level": level}
        self.log_entries.append(entry)
        if len(self.log_entries) > 1000:
            del self.log_entries[:len(self.log_entries) - 1000]
        self.last_event = str(message)
        self._render_console()

    def _copy_console(self) -> None:
        visible = self._visible_log_entries()
        text = "\n".join(f"{e['time']}  {e['message']}" for e in visible)
        if not text:
            self._log("No hay eventos para copiar.", "warn")
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self._log(f"{len(visible)} eventos copiados al portapapeles.", "ok")
        except tk.TclError as exc:
            self._log(f"No se pudo copiar el registro: {exc}", "error")

    def _export_console(self) -> None:
        if not self.log_entries:
            messagebox.showinfo(APP_NAME, "No hay eventos que exportar.", parent=self.root)
            return
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Exportar registro de actividad", defaultextension=".log",
            initialdir=str(self.reports_dir), initialfile=f"omnidesk_activity_{madrid_now().strftime('%Y%m%d_%H%M%S')}.log",
            filetypes=(("Registro de texto", "*.log"), ("Texto", "*.txt"), ("Todos los archivos", "*.*")),
        )
        if not path:
            return
        try:
            lines = [f"{e['time']}  [{e['level'].upper()}]  {e['message']}" for e in self.log_entries]
            Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")
            self._log(f"Registro exportado: {Path(path).name}", "ok")
        except OSError as exc:
            self._log(f"No se pudo exportar el registro: {exc}", "error")
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)

    def _clear_console(self) -> None:
        self.log_entries.clear()
        self._log("Registro de actividad limpiado.", "info")

    def _set_status(self, text: str, color: str = "muted") -> None:
        self.status_text.configure(text=text.upper())
        self.status_dot.configure(fg=C.get(color, C["muted"]))

    def _update_metrics(self) -> None:
        if not hasattr(self, "metric_vars"):
            return
        self.metric_vars["reader"].set(str(self.selected_reader)[:25] if self.selected_reader else "No seleccionado")
        self.metric_vars["card"].set("Presente" if self.card_present else "Sin tarjeta")
        if self.current_identity:
            self.metric_vars["technology"].set(self.current_identity["profile"]["family"][:25])
        else:
            self.metric_vars["technology"].set("Sin identificar")
        self.metric_vars["operation"].set((self.last_result or {}).get("operation", "Ninguna").replace("_", " ").title())

    def _queue_result(self, callback: Callable[[Any], None], value: Any = None, error: Optional[BaseException] = None) -> None:
        self.events.put(("result", (callback, value, error)))

    def _run_async(self, label: str, function: Callable[[], Any], callback: Callable[[Any], None]) -> None:
        if self.busy:
            messagebox.showinfo(APP_NAME, "Ya hay una operación en curso.", parent=self.root)
            return
        self.busy = True
        self._set_status("Operación en curso", "yellow")
        self._log(f"Iniciando: {label}", "info")
        def target() -> None:
            try:
                value = function()
                self._queue_result(callback, value, None)
            except BaseException as exc:
                self._queue_result(callback, None, exc)
        threading.Thread(target=target, name="OmniDeskWorker", daemon=True).start()

    def _process_queue(self) -> None:
        try:
            while True:
                kind, payload = self.events.get_nowait()
                if kind == "result":
                    callback, value, error = payload
                    self.busy = False
                    if error is not None:
                        self._log(str(error), "error")
                        self._set_status("Error", "red")
                        messagebox.showerror(APP_NAME, str(error), parent=self.root)
                    else:
                        try:
                            callback(value)
                        except Exception as exc:
                            self._log(f"Error de interfaz: {exc}", "error")
                            messagebox.showerror(APP_NAME, str(exc), parent=self.root)
                        if not self.busy:
                            self._set_status("Preparado", "green" if self.selected_reader else "muted")
        except queue.Empty:
            pass
        self.root.after(200, self._process_queue)

    def _presence_tick(self) -> None:
        if not self.root.winfo_exists():
            return
        if self.monitor_enabled and self.monitor_var.get() and self.selected_reader is not None and not self.busy and PCSC_AVAILABLE:
            conn = None
            try:
                conn = self.selected_reader.createConnection()
                conn.connect()
                identity = _identity(conn)
                uid = identity.get("uid", "No disponible")
                if (not self.card_present or uid != self.last_seen_uid or self.current_identity is None
                        or identity.get("atr") != self.current_identity.get("atr")):
                    self.card_present = True
                    self.last_seen_uid = uid
                    self.current_identity = identity
                    self._show_identity(identity)
                    self._log(f"Tarjeta detectada · UID {uid}", "ok")
                    self._update_metrics()
            except (NoCardException, CardConnectionException):
                if self.card_present:
                    self.card_present = False
                    self.last_seen_uid = ""
                    self._log("Tarjeta retirada del lector.", "info")
                    self._update_metrics()
            except Exception:
                # Polling errors are intentionally quiet; detailed diagnostics is manual.
                pass
            finally:
                _disconnect(conn)
        self.root.after(POLL_MS, self._presence_tick)

    def _refresh_readers(self, silent: bool = False) -> None:
        if not PCSC_AVAILABLE:
            self.reader_objects = []
            self.reader_combo["values"] = ("PySCard no instalado",)
            self.reader_var.set("PySCard no instalado")
            self.reader_state_label.configure(text="Falta dependencia", foreground=C["yellow"])
            if not silent:
                messagebox.showwarning(APP_NAME, "No está instalado PySCard. En Kali: sudo apt install python3-pyscard pcscd libccid -y", parent=self.root)
            return
        try:
            self.reader_objects = list(pcsc_readers())
            labels = [str(item) for item in self.reader_objects]
            self.reader_combo["values"] = labels or ("No se detectan lectores",)
            if labels:
                current = str(self.selected_reader) if self.selected_reader is not None else ""
                if current in labels:
                    self.reader_var.set(current)
                else:
                    self.reader_var.set(labels[0])
                self.reader_state_label.configure(text=f"{len(labels)} lector(es) disponible(s)", foreground=C["green"])
                if not silent:
                    self._log(f"Detectados {len(labels)} lector(es) PC/SC.", "ok")
            else:
                self.reader_var.set("No se detectan lectores")
                self.reader_state_label.configure(text="Sin lectores", foreground=C["yellow"])
                if not silent:
                    self._log("No se detectan lectores PC/SC.", "warn")
        except Exception as exc:
            self.reader_objects = []
            self.reader_combo["values"] = ("Error PC/SC",)
            self.reader_var.set("Error PC/SC")
            self.reader_state_label.configure(text="Error de servicio", foreground=C["red"])
            if not silent:
                messagebox.showerror(APP_NAME, f"No se pudo consultar PC/SC: {exc}", parent=self.root)

    def _select_reader(self) -> None:
        label = self.reader_var.get()
        match = next((r for r in self.reader_objects if str(r) == label), None)
        if match is None:
            messagebox.showwarning(APP_NAME, "No hay un lector válido seleccionado.", parent=self.root)
            return
        self.selected_reader = match
        self.current_identity = None
        self.card_present = False
        self.last_seen_uid = ""
        self._show_identity_placeholder()
        self.reader_state_label.configure(text="Lector seleccionado", foreground=C["green"])
        self._log(f"Lector seleccionado: {match}", "ok")
        self._update_metrics()
        self._set_status("Lector seleccionado", "green")

    def _show_identity(self, identity: dict[str, Any]) -> None:
        self.current_identity = identity
        profile = identity["profile"]
        rows = [
            ("UID", identity.get("uid", "No disponible")),
            ("Longitud UID", f"{identity.get('uid_length', 0)} bytes"),
            ("ATR", identity.get("atr", "No disponible")),
            ("Familia orientativa", profile.get("family", "No identificada")),
            ("Confianza", profile.get("confidence", "indeterminada")),
            ("Detalle", profile.get("detail", "")),
            ("Fecha", identity.get("timestamp", "")),
        ]
        for item in self.card_tree.get_children():
            self.card_tree.delete(item)
        for field, value in rows:
            self.card_tree.insert("", "end", values=(field, value))
        text = "\n".join(f"{k:<20} {v}" for k, v in rows)
        self._set_text(self.identity_text, text)
        self._update_metrics()

    def _show_identity_placeholder(self) -> None:
        if hasattr(self, "card_tree"):
            for item in self.card_tree.get_children():
                self.card_tree.delete(item)
        if hasattr(self, "identity_text"):
            self._set_text(self.identity_text, "Identifica una tarjeta con el lector seleccionado.")
        self._update_metrics()

    def _get_selected_identity(self) -> Optional[dict[str, Any]]:
        if self.current_identity is None:
            messagebox.showwarning(APP_NAME, "Identifica primero una tarjeta.", parent=self.root)
            return None
        return self.current_identity

    def _ask_key(self) -> Optional[bytes]:
        key_type = self.key_type_var.get().upper()
        raw = simpledialog.askstring("Clave de laboratorio", "Introduce una única clave A/B conocida (12 caracteres HEX):", show="*", parent=self.root)
        if raw is None:
            return None
        # Solo se permiten separadores visuales habituales; no se eliminan letras ajenas al HEX.
        cleaned = re.sub(r"[\s:-]", "", raw).upper()
        if not re.fullmatch(r"[0-9A-F]{12}", cleaned):
            messagebox.showerror(APP_NAME, "La clave debe tener exactamente 12 caracteres hexadecimales (6 bytes).", parent=self.root)
            return None
        self._pending_key_type = key_type
        return bytes.fromhex(cleaned)

    def _ask_unknown_mifare_confirmation(self, identity: dict[str, Any]) -> bool:
        if identity["profile"]["status"] == "lf_candidate":
            messagebox.showerror(APP_NAME, "Operación bloqueada: el ATR coincide con el perfil LF candidato. Esta tarjeta no debe tratarse como MIFARE Classic.", parent=self.root)
            return False
        return messagebox.askyesno(
            "Confirmar tarjeta de laboratorio",
            "El ATR no identifica automáticamente MIFARE Classic.\n\n¿Has verificado por documentación que esta tarjeta es MIFARE Classic y es tuya/de laboratorio?",
            icon="warning", parent=self.root,
        )

    def _run_card_task(self, label: str, task: Callable[[Any, dict[str, Any]], Any], callback: Callable[[Any], None], confirm_unknown: bool = True) -> None:
        if self.selected_reader is None:
            messagebox.showwarning(APP_NAME, "Selecciona primero un lector PC/SC.", parent=self.root)
            return
        if self.current_identity is None:
            messagebox.showwarning(APP_NAME, "Identifica primero la tarjeta. Así podremos comprobar que no cambia durante la operación.", parent=self.root)
            return
        expected = self.current_identity.get("uid")
        if not expected or expected == "No disponible":
            messagebox.showwarning(APP_NAME, "No hay UID disponible para vincular la operación a la tarjeta identificada. No se realizará la operación.", parent=self.root)
            return
        # Confirmation for unknown ATR must happen on the UI thread before sending MIFARE APDU.
        if confirm_unknown and self.current_identity["profile"]["status"] == "unknown":
            if not self._ask_unknown_mifare_confirmation(self.current_identity):
                return
        selected_reader = self.selected_reader
        expected_atr = self.current_identity.get("atr")
        def work() -> Any:
            conn = _connect(selected_reader)
            try:
                identity = _identity(conn)
                if identity.get("uid") != expected or identity.get("atr") != expected_atr:
                    raise OmniError("La tarjeta presente no coincide con la última tarjeta identificada. Vuelve a identificarla.")
                _require_mifare_confirmation(identity)
                return task(conn, identity)
            finally:
                _disconnect(conn)
        self._run_async(label, work, callback)

    def _identify_card(self) -> None:
        if self.selected_reader is None:
            messagebox.showwarning(APP_NAME, "Selecciona primero un lector.", parent=self.root)
            return
        selected_reader = self.selected_reader
        def work() -> dict[str, Any]:
            conn = _connect(selected_reader)
            try:
                return _identity(conn)
            finally:
                _disconnect(conn)
        def done(identity: dict[str, Any]) -> None:
            self.card_present = True
            self.last_seen_uid = identity.get("uid", "")
            self._show_identity(identity)
            self._log(f"Identificación completada · {identity.get('uid')}", "ok")
            self._navigate("Tarjetas")
        self._run_async("Identificar tarjeta", work, done)

    def _toggle_monitor(self) -> None:
        self.monitor_enabled = bool(self.monitor_var.get())
        self._log("Monitor automático activado." if self.monitor_enabled else "Monitor automático pausado.", "info")

    # ---------- MIFARE operations ----------
    def _read_block(self) -> None:
        identity = self._get_selected_identity()
        if not identity:
            return
        key = self._ask_key()
        if key is None:
            return
        key_type = self._pending_key_type
        def task(conn: Any, current: dict[str, Any]) -> dict[str, Any]:
            _authenticate_block4(conn, key, key_type)
            data = _read_block4(conn)
            return {"data": data, "identity": current, "operation": "read"}
        def done(result: dict[str, Any]) -> None:
            self.last_data = result["data"]
            self.last_result = {"operation": "read", "uid": result["identity"]["uid"], "atr": result["identity"]["atr"], "block": LAB_BLOCK, "data_hex": result["data"].hex().upper(), "timestamp": timestamp()}
            self._display_block(result["data"], "LECTURA CORRECTA · BLOQUE 4")
            self._update_metrics()
            self._log("Bloque 4 leído correctamente. La clave no se ha guardado.", "ok")
            self._navigate("MIFARE")
        self._run_card_task("Leer bloque 4", task, done)
        # La clave solo se mantiene en memoria durante la operación; Python no garantiza borrado seguro de bytes.

    def _verify_key(self) -> None:
        identity = self._get_selected_identity()
        if not identity:
            return
        key = self._ask_key()
        if key is None:
            return
        key_type = self._pending_key_type
        def task(conn: Any, current: dict[str, Any]) -> dict[str, Any]:
            _authenticate_block4(conn, key, key_type)
            return {"uid": current["uid"], "type": key_type}
        def done(result: dict[str, Any]) -> None:
            self.last_result = {"operation": "verify_key", "uid": result["uid"], "block": LAB_BLOCK, "timestamp": timestamp()}
            self._update_metrics()
            self._log(f"Autenticación aceptada para bloque 4 con clave tipo {result['type']}. No se leyó ni modificó memoria.", "ok")
            messagebox.showinfo(APP_NAME, f"Autenticación aceptada para el bloque 4 con clave tipo {result['type']}.\nNo se leyó ni modificó memoria.", parent=self.root)
        self._run_card_task("Verificar clave conocida", task, done)

    def _write_block(self) -> None:
        identity = self._get_selected_identity()
        if not identity:
            return
        key = self._ask_key()
        if key is None:
            return
        mode = messagebox.askyesnocancel("Datos para escribir", "¿Quieres introducir el bloque en hexadecimal?\n\nSí = HEX (32 caracteres)\nNo = Texto UTF-8 (máximo 16 bytes)", parent=self.root)
        if mode is None:
            return
        if mode:
            raw = simpledialog.askstring("Nuevo bloque 4", "HEX (32 caracteres, 16 bytes):", parent=self.root)
            if raw is None:
                return
            try:
                new_data = validate_hex_block(raw)
            except ValueError as exc:
                messagebox.showerror(APP_NAME, str(exc), parent=self.root)
                return
        else:
            raw = simpledialog.askstring("Nuevo bloque 4", "Texto UTF-8 (máximo 16 bytes):", parent=self.root)
            if raw is None:
                return
            try:
                new_data = text_to_block(raw)
            except ValueError as exc:
                messagebox.showerror(APP_NAME, str(exc), parent=self.root)
                return
        key_type = self._pending_key_type
        expected_uid = identity.get("uid")
        expected_atr = identity.get("atr")
        selected_reader = self.selected_reader
        def prepare_task(conn: Any, current: dict[str, Any]) -> dict[str, Any]:
            _authenticate_block4(conn, key, key_type)
            old_data = _read_block4(conn)
            return {"old": old_data, "new": new_data, "identity": current}
        def prepared(preview: dict[str, Any]) -> None:
            old_data = preview["old"]
            if old_data == new_data:
                messagebox.showinfo(APP_NAME, "El bloque ya contiene esos datos. No hace falta escribir.", parent=self.root)
                return
            confirm_text = (
                "Vas a modificar físicamente el bloque 4 de la tarjeta identificada.\n\n"
                f"UID: {expected_uid}\n\nANTES:\n{old_data.hex(' ').upper()}\n\n"
                f"NUEVO:\n{new_data.hex(' ').upper()}\n\n"
                "No se tocarán bloque fabricante ni tráileres. ¿Deseas continuar?"
            )
            if not messagebox.askyesno("Confirmación 1/2 · Escritura", confirm_text, icon="warning", parent=self.root):
                self._log("Escritura cancelada antes de enviar APDU.", "warn")
                return
            phrase = simpledialog.askstring("Confirmación 2/2", 'Escribe exactamente: ESCRIBIR BLOQUE 4', parent=self.root)
            if phrase != "ESCRIBIR BLOQUE 4":
                self._log("Escritura cancelada: frase de confirmación incorrecta.", "warn")
                return
            def write_task(conn: Any, current: dict[str, Any]) -> dict[str, Any]:
                if current.get("uid") != expected_uid:
                    raise OmniError("El UID ha cambiado; escritura abortada.")
                _authenticate_block4(conn, key, key_type)
                current_data = _read_block4(conn)
                if current_data != old_data:
                    raise OmniError("El contenido anterior ha cambiado desde la vista previa. Escritura abortada.")
                _write_block4(conn, new_data)
                verified = _read_block4(conn)
                if verified != new_data:
                    raise OmniError("La escritura se envió, pero la verificación byte a byte no coincide. Comprueba la tarjeta.")
                return {"identity": current, "data": verified}
            def written(result: dict[str, Any]) -> None:
                self.last_data = result["data"]
                self.last_result = {"operation": "write_verified", "uid": expected_uid, "atr": result["identity"]["atr"], "block": LAB_BLOCK, "data_hex": result["data"].hex().upper(), "timestamp": timestamp()}
                self._display_block(result["data"], "ESCRITURA Y VERIFICACIÓN CORRECTAS")
                self._log("Bloque 4 escrito y verificado byte a byte.", "ok")
                self._update_metrics()
                messagebox.showinfo(APP_NAME, "Escritura y verificación completadas correctamente.", parent=self.root)
            self._run_async("Escritura controlada del bloque 4", lambda: self._operate_on_expected_uid(write_task, expected_uid, expected_atr, selected_reader), written)
        self._run_card_task("Preparar escritura controlada", prepare_task, prepared)

    def _operate_on_expected_uid(self, task: Callable[[Any, dict[str, Any]], Any], expected_uid: str, expected_atr: str, selected_reader: Any) -> Any:
        conn = _connect(selected_reader)
        try:
            current = _identity(conn)
            if current.get("uid") != expected_uid or current.get("atr") != expected_atr:
                raise OmniError("La tarjeta o su ATR han cambiado; operación abortada.")
            _require_mifare_confirmation(current)
            return task(conn, current)
        finally:
            _disconnect(conn)

    def _compare_block(self) -> None:
        identity = self._get_selected_identity()
        if not identity:
            return
        expected = simpledialog.askstring("Comparar bloque 4", "Valor esperado HEX (32 caracteres):", parent=self.root)
        if expected is None:
            return
        try:
            expected_data = validate_hex_block(expected)
        except ValueError as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)
            return
        key = self._ask_key()
        if key is None:
            return
        key_type = self._pending_key_type
        def task(conn: Any, current: dict[str, Any]) -> dict[str, Any]:
            _authenticate_block4(conn, key, key_type)
            actual = _read_block4(conn)
            return {"actual": actual, "expected": expected_data, "uid": current["uid"]}
        def done(result: dict[str, Any]) -> None:
            self.last_data = result["actual"]
            self._display_block(result["actual"], "LECTURA PARA COMPARACIÓN")
            if result["actual"] == result["expected"]:
                self._log("Comparación exacta: los 16 bytes coinciden.", "ok")
                messagebox.showinfo(APP_NAME, "Coincidencia exacta: los 16 bytes son idénticos.", parent=self.root)
            else:
                diffs = [f"Byte {i:02d}: leído {a:02X}, esperado {b:02X}" for i, (a, b) in enumerate(zip(result["actual"], result["expected"])) if a != b]
                self._log("Comparación: se han encontrado diferencias.", "warn")
                messagebox.showwarning(APP_NAME, "Los datos no coinciden:\n\n" + "\n".join(diffs), parent=self.root)
        self._run_card_task("Comparar bloque 4", task, done)

    # ---------- Other tools ----------
    def _display_block(self, data: bytes, heading: str) -> None:
        info = _analyse_bytes(data)
        text = (
            f"{heading}\n\n"
            f"Offset  HEX                                         ASCII\n"
            f"00      {info['hex']:<47} {info['ascii']}\n\n"
            f"Longitud: {len(data)} bytes\n"
            f"Texto UTF-8: {info['utf8']}\n"
            f"Bytes nulos: {info['null_bytes']}\n"
            f"ASCII imprimible: {info['printable']}"
        )
        self._set_text(self.block_view, text)
        self.block_status.configure(text=f"Último bloque: {timestamp()}")
        self._navigate("MIFARE")

    def _analyse_last(self) -> None:
        if self.last_data is None:
            messagebox.showinfo(APP_NAME, "Todavía no hay una lectura en esta sesión.", parent=self.root)
            return
        self._show_analysis(_analyse_bytes(self.last_data))
        self._navigate("Analizador")

    def _analyse_hex(self) -> None:
        try:
            data = validate_hex_block(self.hex_input.get())
        except ValueError as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)
            return
        self._show_analysis(_analyse_bytes(data))
        self._log("Análisis HEX local completado (16 bytes).", "ok")

    def _convert_text(self) -> None:
        try:
            data = text_to_block(self.text_input.get())
        except ValueError as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)
            return
        self.hex_input.set(data.hex().upper())
        self._show_analysis(_analyse_bytes(data))
        self._log("Texto convertido a bloque HEX de 16 bytes.", "ok")

    def _show_analysis(self, result: dict[str, Any]) -> None:
        text = (
            f"HEX       {result['hex']}\n"
            f"HEX plano {result['hex_compact']}\n"
            f"ASCII     {result['ascii']}\n"
            f"UTF-8     {result['utf8']}\n"
            f"DECIMAL   {result['decimal']}\n"
            f"BINARIO   {result['binary']}\n\n"
            f"Bytes nulos: {result['null_bytes']}\n"
            f"ASCII imprimible: {result['printable']}"
        )
        self._set_text(self.analysis_view, text)

    def _register_card(self) -> None:
        identity = self._get_selected_identity()
        if not identity:
            return
        alias = simpledialog.askstring("Registrar tarjeta", "Alias para esta tarjeta de laboratorio:", parent=self.root)
        if not alias:
            return
        include_uid = messagebox.askyesno("Privacidad del registro", "¿Quieres incluir el UID en el JSON?\n\nSí = incluir UID\nNo = omitir UID", parent=self.root)
        record = {
            "application": APP_NAME,
            "version": VERSION,
            "alias": alias.strip()[:64],
            "timestamp": timestamp(),
            "atr": identity.get("atr", "No disponible"),
            "technology_profile": identity.get("profile", {}),
            "uid_included": include_uid,
            "note": "Registro local de laboratorio; no contiene claves ni datos de memoria.",
        }
        if include_uid:
            record["uid"] = identity.get("uid")
        try:
            self.registry_dir.mkdir(parents=True, exist_ok=True)
            safe = re.sub(r"[^A-Za-z0-9_-]+", "_", alias.strip()).strip("_") or "tarjeta"
            filename = f"{safe}_{madrid_now().strftime('%Y%m%d_%H%M%S')}.json"
            target = self.registry_dir / filename
            target.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            self._log(f"Tarjeta registrada: {filename}", "ok")
            self._refresh_files()
            messagebox.showinfo(APP_NAME, f"Registro guardado:\n{target}", parent=self.root)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"No se pudo guardar el registro: {exc}", parent=self.root)

    def _export_report(self) -> None:
        if not self.last_result:
            messagebox.showinfo(APP_NAME, "Todavía no hay una operación de memoria para exportar.", parent=self.root)
            return
        include_uid = messagebox.askyesno("Privacidad del informe", "¿Incluir UID en el informe?", parent=self.root)
        report = dict(self.last_result)
        if not include_uid:
            report.pop("uid", None)
        report.update({"application": APP_NAME, "version": VERSION, "timezone": "Europe/Madrid"})
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Guardar informe OMNIDESK", defaultextension=".json",
            initialdir=str(self.reports_dir), initialfile=f"omnidesk_{madrid_now().strftime('%Y%m%d_%H%M%S')}.json",
            filetypes=(("JSON", "*.json"), ("Todos los archivos", "*.*")),
        )
        if not path:
            return
        try:
            Path(path).write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            self._log(f"Informe exportado: {Path(path).name}", "ok")
            messagebox.showinfo(APP_NAME, f"Informe guardado en:\n{path}", parent=self.root)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"No se pudo guardar el informe: {exc}", parent=self.root)

    def _refresh_files(self) -> None:
        if not hasattr(self, "registry_tree"):
            return
        for item in self.registry_tree.get_children():
            self.registry_tree.delete(item)
        for folder in (self.registry_dir, self.reports_dir):
            if folder.exists():
                for path in sorted(folder.glob("*.json"), key=lambda p: p.stat().st_mtime, reverse=True):
                    stat = path.stat()
                    kind = "Registro" if folder == self.registry_dir else "Informe"
                    date = datetime.fromtimestamp(stat.st_mtime).astimezone().strftime("%Y-%m-%d %H:%M:%S")
                    self.registry_tree.insert("", "end", values=(path.name, kind, date, f"{stat.st_size} B"), tags=(str(path),))

    def _open_selected_json(self, _event: Any = None) -> None:
        selected = self.registry_tree.selection()
        if not selected:
            return
        values = self.registry_tree.item(selected[0], "values")
        path = self.registry_dir / values[0]
        if not path.exists():
            path = self.reports_dir / values[0]
        if not path.exists():
            return
        try:
            content = path.read_text(encoding="utf-8")
            messagebox.showinfo(path.name, content[:6000], parent=self.root)
        except OSError as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)

    def _open_folder(self, folder: Path) -> None:
        folder.mkdir(parents=True, exist_ok=True)
        try:
            if sys.platform.startswith("linux"):
                subprocess.Popen(["xdg-open", str(folder)])
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(folder)])
            elif os.name == "nt":
                os.startfile(str(folder))  # type: ignore[attr-defined]
            else:
                messagebox.showinfo(APP_NAME, str(folder), parent=self.root)
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"No se pudo abrir la carpeta: {exc}", parent=self.root)

    def _open_registry_folder(self) -> None:
        self._open_folder(self.registry_dir)

    def _open_reports_folder(self) -> None:
        self._open_folder(self.reports_dir)

    def _run_quick_diagnostic(self) -> None:
        lines = [
            f"{APP_NAME} {VERSION}",
            f"Python: {sys.version.split()[0]}",
            f"Plataforma: {platform.platform()}",
            f"Tkinter: {tk.TkVersion}",
            f"PC/SC disponible: {'Sí' if PCSC_AVAILABLE else 'No'}",
            f"Zona horaria de informes: Europe/Madrid",
            f"Hora local: {timestamp()}",
            "",
        ]
        if not PCSC_AVAILABLE:
            lines.append(f"PySCard no disponible: {PCSC_IMPORT_ERROR}")
        else:
            try:
                devices = list(pcsc_readers())
                lines.append(f"Lectores encontrados: {len(devices)}")
                lines.extend(f"  {i}. {reader}" for i, reader in enumerate(devices, 1))
            except Exception as exc:
                lines.append(f"Error consultando PC/SC: {exc}")
        if sys.platform.startswith("linux") and shutil_which("systemctl"):
            try:
                result = subprocess.run(["systemctl", "is-active", "pcscd"], capture_output=True, text=True, timeout=3, check=False)
                lines.append(f"Servicio pcscd: {(result.stdout or result.stderr).strip() or 'sin respuesta'}")
            except Exception as exc:
                lines.append(f"Estado pcscd: no disponible ({exc})")
        lines += ["", "Seguridad:", "  • Sin fuerza bruta ni recuperación automática de claves.", "  • Lectura/escritura limitadas al bloque 4.", "  • Las claves A/B no se guardan ni se incluyen en informes."]
        self._set_text(self.diag_view, "\n".join(lines))
        self._log("Diagnóstico del entorno completado.", "ok")
        self._navigate("Diagnóstico")

    def _run_self_tests(self) -> None:
        results = _self_test_results()
        passed = sum(1 for _, result in results if result)
        total = len(results)
        lines = ["AUTOPRUEBAS LOCALES · SIN TARJETA", ""]
        for label, result in results:
            lines.append(f"  {'PASS' if result else 'FAIL'}  {label}")
        lines += ["", f"Resultado: {passed}/{total} pruebas superadas.", "Estas pruebas no verifican el hardware físico ni la comunicación real con tarjetas."]
        self._set_text(self.diag_view, "\n".join(lines))
        self._log(f"Autopruebas locales: {passed}/{total}.", "ok" if passed == total else "error")
        self._navigate("Diagnóstico")

    def _presence_summary(self) -> None:
        if self.selected_reader is None:
            self._set_status("Sin lector", "muted")
        else:
            self._set_status("Lector seleccionado", "green")

    def _on_close(self) -> None:
        if self.busy and not messagebox.askyesno(APP_NAME, "Hay una operación en curso. ¿Cerrar igualmente?", parent=self.root):
            return
        self.monitor_enabled = False
        self.root.destroy()


def shutil_which(command: str) -> Optional[str]:
    # Avoid importing shutil solely for this tiny helper.
    for directory in os.getenv("PATH", "").split(os.pathsep):
        candidate = Path(directory) / command
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=f"{APP_NAME} {VERSION} — centro gráfico de operaciones RFID")
    parser.add_argument("--self-test", action="store_true", help="ejecutar autopruebas sin abrir la interfaz")
    parser.add_argument("--version", action="version", version=f"{APP_NAME} {VERSION}")
    args = parser.parse_args()
    if args.self_test:
        passed, total = _self_tests()
        print(f"OMNIDESK {VERSION} · Autopruebas: {passed}/{total}")
        raise SystemExit(0 if passed == total else 1)
    root = tk.Tk()
    app = OmniDesk(root)
    root.mainloop()


if __name__ == "__main__":
    main()
