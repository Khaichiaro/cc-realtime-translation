"""
CC Realtime Translator
=======================
โปรแกรมจับภาพเฉพาะ "กรอบ" บนหน้าจอที่แสดงคำบรรยาย (CC) จาก Zoom/Teams
อ่านข้อความด้วย OCR แล้วแปลภาษาแบบเกือบเรียลไทม์ แสดงเป็นแถบคำบรรยายลอย

ไม่มีการเข้าร่วมประชุมหรือเชื่อมต่อ API ของ Zoom/Teams ใดๆ เป็นการแคปหน้าจอ
เฉพาะบริเวณที่เลือกเองซ้ำๆ เท่านั้น

การติดตั้ง
----------
    pip install -r requirements.txt

ต้องติดตั้ง Tesseract OCR แยกต่างหาก (ดู README.md) และถ้าจะใช้ DeepL/Gemini
ต้องสร้างไฟล์ .env ในโฟลเดอร์เดียวกับไฟล์นี้ ใส่:
    DEEPL_API_KEY=xxxxxxxx
    GEMINI_API_KEY=xxxxxxxx

การใช้งาน
----------
    python cc_realtime_translator.py
"""

import os
import sys
import json
import re
import string
import difflib
import queue
import threading
import time
import tkinter as tk
from tkinter import messagebox

import mss
import pytesseract
import requests
from PIL import Image
from dotenv import load_dotenv
from deep_translator import GoogleTranslator, MyMemoryTranslator
from deep_translator.exceptions import LanguageNotSupportedException

# เก็บข้อมูลเป็น Dict: {'word': {'th': 'คำแปล', 'pos': 'ประเภทคำ'}}
LOCAL_DICT = {}

def load_local_datasets():
    files_to_load = ["th-en1.json", "th-en2.json"]
    for filename in files_to_load:
        if getattr(sys, 'frozen', False):
            base_dir = os.path.dirname(sys.executable)
        else:
            base_dir = os.path.dirname(os.path.abspath(__file__))
            
        filepath = os.path.join(base_dir, filename)
        if os.path.exists(filepath):
            try:
                with open(filepath, 'r', encoding='utf-8-sig') as f:
                    data = json.load(f)
                    for record in data.get("records", []):
                        if len(record) >= 6:
                            eng_word = str(record[2]).strip().lower()
                            
                            # สกัดเอาแค่คำแรก ตัดอักษรหลังเครื่องหมาย ( , / ; ออกให้หมด
                            raw_meaning = str(record[4]).strip()
                            thai_meaning = re.split(r'\(|,|/|;', raw_meaning)[0].strip()
                            
                            pos_tag = str(record[5]).strip().upper()
                            
                            # ถ้าคำแปลยาวเกิน 25 ตัวอักษร (มักจะเป็นประโยคอธิบาย ไม่ใช่คำศัพท์) ให้ข้ามไปเลย
                            if len(thai_meaning) > 25:
                                continue
                                
                            if eng_word not in LOCAL_DICT:
                                LOCAL_DICT[eng_word] = {"th": thai_meaning, "pos": pos_tag}
            except Exception as e:
                print(f"Error loading {filename}: {e}")

# โหลดเข้า RAM ทันทีที่เปิดโปรแกรม
load_local_datasets()

try:
    import keyboard
    _KEYBOARD_AVAILABLE = True
except Exception:
    _KEYBOARD_AVAILABLE = False

import customtkinter as ctk

# ======================================================================
# การตั้งค่าเริ่มต้น / ค่าคงที่
# ======================================================================

load_dotenv()
DEEPL_API_KEY = os.getenv("DEEPL_API_KEY", "").strip()
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()

# แก้ปัญหา DPI scaling บน Windows (ไม่ทำจะทำให้กรอบที่เลือกไปจับภาพผิดตำแหน่ง)
if sys.platform == "win32":
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

# ระบบค้นหา Tesseract อัตโนมัติ (รองรับทั้งตอนเทส .py และตอนเป็น .exe)
if sys.platform == "win32":
    # เช็คว่ารันเป็น .exe (ผ่าน PyInstaller) หรือรันผ่านไฟล์ .py ธรรมดา
    if getattr(sys, 'frozen', False):
        base_dir = os.path.dirname(sys.executable)
    else:
        base_dir = os.path.dirname(os.path.abspath(__file__))

    # 1. หาแบบ Portable ก่อน (โฟลเดอร์ Tesseract-OCR วางอยู่ข้างๆ โปรแกรม)
    portable_tess = os.path.join(base_dir, "Tesseract-OCR", "tesseract.exe")
    # 2. ถ้าไม่เจอ ค่อยไปหาใน Program Files (ท่ามาตรฐาน)
    default_tess = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
    
    if os.path.exists(portable_tess):
        pytesseract.pytesseract.tesseract_cmd = portable_tess
    elif os.path.exists(default_tess):
        pytesseract.pytesseract.tesseract_cmd = default_tess

OCR_LANGS = {
    "อังกฤษ (English)": "eng",
    "ไทย": "tha",
    "จีนตัวย่อ": "chi_sim",
    "ญี่ปุ่น": "jpn",
    "เกาหลี": "kor",
    "เวียดนาม": "vie",
}

TRANSLATE_LANGS = {
    "ไทย": "th",
    "อังกฤษ": "en",
    "จีน (ตัวย่อ)": "zh-CN",
    "ญี่ปุ่น": "ja",
    "เกาหลี": "ko",
    "เวียดนาม": "vi",
}

OCR_TO_MYMEMORY_SRC = {
    "eng": "en", "tha": "th", "chi_sim": "zh-CN",
    "jpn": "ja", "kor": "ko", "vie": "vi",
}

MYMEMORY_SRC_MAP = {
    "eng": "english", "tha": "thai", "chi_sim": "chinese",
    "jpn": "japanese", "kor": "korean", "vie": "vietnamese"
}
MYMEMORY_TGT_MAP = {
    "th": "thai", "en": "english", "zh-CN": "chinese",
    "ja": "japanese", "ko": "korean", "vi": "vietnamese"
}

# code ภาษาที่ DeepL ต้องการ (ไม่เหมือนกับ code ที่ใช้ในแอปเราเป๊ะๆ)
DEEPL_TARGET_LANGS = {
    "th": "TH", "en": "EN-US", "zh-CN": "ZH",
    "ja": "JA", "ko": "KO", "vi": "VI",
}

GEMINI_LANG_NAMES = {
    "th": "Thai", "en": "English", "zh-CN": "Simplified Chinese",
    "ja": "Japanese", "ko": "Korean", "vi": "Vietnamese",
}

ENGINES = ["Google (ฟรี)", "MyMemory (ฟรี)", "Local Dictionary (ออฟไลน์)", "DeepL", "Gemini"]

_MIN_TRANSLATE_GAP = 1.2  # วินาที กันชน rate limit ของ Google Translate แบบฟรี

# ตรวจจับกรณีที่ไลบรารีแปลบางเวอร์ชัน "หลุด" เอารายการภาษาที่รองรับทั้งหมด
# (เช่น 'korean': 'ko-KR', 'lao': 'lo-LA', ...) มาเป็นค่าที่คืนกลับมา แทนที่จะ
# โยน exception ให้จับได้ตามปกติ — ถ้าเจอ pattern นี้ให้ถือว่าแปลไม่สำเร็จ
_LANG_DUMP_PATTERN = re.compile(r"'[a-zA-Z\- ]+':\s*'[a-zA-Z\-]+'")


def looks_like_language_dump(s: str) -> bool:
    if not isinstance(s, str) or len(s) < 200:
        return False
    return len(_LANG_DUMP_PATTERN.findall(s)) >= 5


# สัญลักษณ์ที่ OCR มักอ่านผิดจากไอคอน avatar / บูลเล็ต ฯลฯ
_OCR_NOISE_RE = re.compile(r'(?:^|(?<=\s))[@®©™†‡•●○◦§¶|_~]+(?:(?=\s)|$)')


def clean_ocr_text(text: str) -> str:
    cleaned = _OCR_NOISE_RE.sub(" ", text)
    cleaned = re.sub(r"\s{2,}", " ", cleaned).strip()
    return cleaned


# ======================================================================
# ดีไซน์ / สี (โทน Tailwind slate + blue accent)
# ======================================================================

COLOR_BG = "#0f172a"        # slate-900
COLOR_CARD = "#1e293b"      # slate-800
COLOR_BORDER = "#334155"    # slate-700
COLOR_TEXT = "#f1f5f9"      # slate-100
COLOR_MUTED = "#94a3b8"     # slate-400
COLOR_ACCENT = "#3b82f6"    # blue-500
COLOR_ACCENT_HOVER = "#2563eb"  # blue-600
COLOR_SUCCESS = "#22c55e"   # green-500
COLOR_WARNING = "#f59e0b"   # amber-500
COLOR_ERROR = "#ef4444"     # red-500

FONT_FAMILY = "Segoe UI"

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")


def h_font(size=14, weight="bold"):
    return ctk.CTkFont(family=FONT_FAMILY, size=size, weight=weight)


def n_font(size=12, weight="normal"):
    return ctk.CTkFont(family=FONT_FAMILY, size=size, weight=weight)


# ======================================================================
# หน้าต่างจับภาพ/แสดงผลบนหน้าจอ (คงเป็น tk.Toplevel ธรรมดา เพื่อความเสถียร
# ของการทำโปร่งใส/ไร้กรอบ ข้ามแพลตฟอร์ม)
# ======================================================================

class RegionSelector(tk.Toplevel):
    """หน้าต่างเต็มจอโปร่งใสสำหรับให้ผู้ใช้ลากเลือกกรอบ CC"""

    def __init__(self, master, on_selected):
        super().__init__(master)
        self.on_selected = on_selected
        self.attributes("-fullscreen", True)
        self.attributes("-alpha", 0.3)
        self.configure(bg="black")
        self.attributes("-topmost", True)
        self.config(cursor="crosshair")

        self.canvas = tk.Canvas(self, bg="black", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        info = tk.Label(
            self,
            text="ลากเมาส์ครอบบริเวณคำบรรยาย (CC) แล้วปล่อย   |   กด Esc เพื่อยกเลิก",
            fg="white", bg="black", font=(FONT_FAMILY, 14, "bold"),
        )
        info.place(relx=0.5, y=30, anchor="n")

        self.start_x = self.start_y = 0
        self.rect_id = None

        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.bind("<Escape>", lambda e: self.destroy())

    def _on_press(self, event):
        self.start_x, self.start_y = event.x, event.y
        if self.rect_id:
            self.canvas.delete(self.rect_id)
        self.rect_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y,
            outline=COLOR_ACCENT, width=2
        )

    def _on_drag(self, event):
        self.canvas.coords(self.rect_id, self.start_x, self.start_y, event.x, event.y)

    def _on_release(self, event):
        x1, y1 = min(self.start_x, event.x), min(self.start_y, event.y)
        x2, y2 = max(self.start_x, event.x), max(self.start_y, event.y)
        self.destroy()
        if x2 - x1 > 5 and y2 - y1 > 5:
            self.on_selected({"left": x1, "top": y1, "width": x2 - x1, "height": y2 - y1})


class RegionIndicator(tk.Toplevel):
    """กรอบเส้นค้างไว้รอบบริเวณที่กำลังจับภาพ เพื่อยืนยันตำแหน่งขณะทำงาน"""

    def __init__(self, master, region):
        super().__init__(master)
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        x, y, w, h = region["left"], region["top"], region["width"], region["height"]
        self.geometry(f"{w}x{h}+{x}+{y}")
        

        border = 2
        if sys.platform == "win32":
            trans_color = "magenta"
            try:
                self.configure(bg=trans_color)
                self.attributes("-transparentcolor", trans_color)
                inner_bg = trans_color
            except tk.TclError:
                inner_bg = COLOR_CARD
                try:
                    self.attributes("-alpha", 0.2)
                except tk.TclError:
                    pass
            inner = tk.Frame(
                self, bg=inner_bg, highlightbackground=COLOR_ACCENT,
                highlightcolor=COLOR_ACCENT, highlightthickness=border
            )
            inner.pack(fill="both", expand=True)
        else:
            try:
                self.attributes("-alpha", 0.25)
            except tk.TclError:
                pass
            self.configure(bg=COLOR_ACCENT)
            inner = tk.Frame(self, bg=COLOR_CARD)
            inner.pack(fill="both", expand=True, padx=border, pady=border)


class CaptionOverlay(tk.Toplevel):
    """แถบคำบรรยายลอยเหนือหน้าจอ ลากย้ายตำแหน่งและย่อ/ขยายขนาดได้อิสระ"""

    MIN_W, MIN_H = 240, 80

    def __init__(self, master):
        super().__init__(master)
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.92)
        except tk.TclError:
            pass
        self.configure(bg=COLOR_BG)

        self._drag_offset = (0, 0)
        self._resizing = False
        self._resize_start = (0, 0, 0, 0)

        self.orig_var = tk.StringVar(value="")
        self.trans_var = tk.StringVar(value="รอข้อความ CC...")

        # แถบ accent บางๆ ด้านบน ให้ดูมีดีไซน์ทันสมัยขึ้นนิดหน่อย
        top_bar = tk.Frame(self, bg=COLOR_ACCENT, height=3)
        top_bar.pack(fill="x", side="top")

        body = tk.Frame(self, bg=COLOR_BG)
        body.pack(fill="both", expand=True, padx=18, pady=(10, 14))

        self.orig_label = tk.Label(
            body, textvariable=self.orig_var, fg=COLOR_MUTED, bg=COLOR_BG,
            font=(FONT_FAMILY, 11), wraplength=760, justify="center", cursor="fleur"
        )
        self.orig_label.pack(fill="x", pady=(0, 4))

        self.trans_label = tk.Label(
            body, textvariable=self.trans_var, fg=COLOR_TEXT, bg=COLOR_BG,
            font=(FONT_FAMILY, 18, "bold"), wraplength=760, justify="center", cursor="fleur"
        )
        self.trans_label.pack(fill="x")

        for widget in (self, top_bar, body, self.orig_label, self.trans_label):
            widget.bind("<ButtonPress-1>", self._start_move)
            widget.bind("<B1-Motion>", self._on_move)

        self.grip = tk.Label(self, text="◢", fg=COLOR_MUTED, bg=COLOR_BG, cursor="size_nw_se")
        self.grip.place(relx=1.0, rely=1.0, anchor="se")
        self.grip.bind("<ButtonPress-1>", self._start_resize)
        self.grip.bind("<B1-Motion>", self._on_resize)

        self.update_idletasks()
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        w = 760
        h = self.winfo_reqheight()
        x = (screen_w - w) // 2
        y = screen_h - h - 70
        self.geometry(f"{w}x{h}+{x}+{y}")

    def _start_move(self, event):
        self._drag_offset = (event.x_root - self.winfo_x(), event.y_root - self.winfo_y())

    def _on_move(self, event):
        x = event.x_root - self._drag_offset[0]
        y = event.y_root - self._drag_offset[1]
        self.geometry(f"+{x}+{y}")

    def _start_resize(self, event):
        self._resizing = True
        self._resize_start = (event.x_root, event.y_root, self.winfo_width(), self.winfo_height())

    def _on_resize(self, event):
        if not self._resizing:
            return
        sx, sy, sw, sh = self._resize_start
        new_w = max(self.MIN_W, sw + (event.x_root - sx))
        new_h = max(self.MIN_H, sh + (event.y_root - sy))
        self.geometry(f"{new_w}x{new_h}")
        wrap = max(140, new_w - 40)
        self.orig_label.config(wraplength=wrap)
        self.trans_label.config(wraplength=wrap)

    def set_font_size(self, size: int):
        self.trans_label.config(font=(FONT_FAMILY, size, "bold"))
        self.orig_label.config(font=(FONT_FAMILY, max(8, size - 7)))

    def show_text(self, original: str, translated: str):
        self.orig_var.set(original)
        self.trans_var.set(translated)


# ======================================================================
# แอปหลัก (UI ใหม่ทั้งหมดด้วย customtkinter)
# ======================================================================

class App:
    def __init__(self):
        self.root = ctk.CTk()
        self.root.title("CC Realtime Translator")
        self.root.geometry("620x800")
        self.root.minsize(560, 700)
        self.root.configure(fg_color=COLOR_BG)

        self.region = None
        self.running = False
        self.worker_thread = None
        self.overlay = None
        self.region_indicator = None
        self.ui_queue = queue.Queue()
        self.last_text = ""
        self._translate_lock = threading.Lock()
        self._last_translate_ts = 0.0
        self._cached_gemini_model = None

        self._force_capture = False
        self._current_trigger_mode = "ทั้งคู่ (เวลา + คีย์ลัด)"
        self.current_bound_hotkey = "ctrl+shift+t"
        self._hotkey_ok = False
        self._register_hotkey(self.current_bound_hotkey)

        self._build_ui()
        self.root.after(150, self._poll_queue)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------- Hotkey ----------------
    def _register_hotkey(self, hotkey: str) -> bool:
        if not _KEYBOARD_AVAILABLE:
            self._hotkey_ok = False
            return False
        try:
            keyboard.add_hotkey(hotkey, self._trigger_force_capture)
            self._hotkey_ok = True
            return True
        except Exception:
            self._hotkey_ok = False
            return False

    def _trigger_force_capture(self):
        if self.running:
            self._force_capture = True

    def _start_record_hotkey(self):
        if not _KEYBOARD_AVAILABLE:
            messagebox.showwarning(
                "ใช้งานไม่ได้", "ยังไม่ได้ติดตั้งไลบรารี keyboard\n(pip install keyboard)"
            )
            return
        self.record_btn.configure(text="กำลังรอ... กดปุ่มบนคีย์บอร์ด", state="disabled")
        self.hotkey_label.configure(text="...")
        threading.Thread(target=self._record_hotkey_thread, daemon=True).start()

    def _record_hotkey_thread(self):
        try:
            new_hotkey = keyboard.read_hotkey(suppress=False)
        except Exception:
            new_hotkey = self.current_bound_hotkey
        self.root.after(0, self._apply_recorded_hotkey, new_hotkey)

    def _apply_recorded_hotkey(self, new_hotkey):
        self.record_btn.configure(text="เปลี่ยนคีย์ลัด", state="normal")
        try:
            if self._hotkey_ok:
                keyboard.remove_hotkey(self.current_bound_hotkey)
        except Exception:
            pass
        if self._register_hotkey(new_hotkey):
            self.current_bound_hotkey = new_hotkey
            self.hotkey_label.configure(text=new_hotkey)
        else:
            messagebox.showerror(
                "ตั้งคีย์ลัดไม่สำเร็จ",
                f"ใช้ปุ่ม '{new_hotkey}' เป็นคีย์ลัดไม่ได้\n"
                "บน Windows อาจต้องรันโปรแกรมแบบ Administrator ถึงจะดักคีย์ลัดทั้งระบบได้"
            )
            self.hotkey_label.configure(text=self.current_bound_hotkey)
            self._register_hotkey(self.current_bound_hotkey)
        self._refresh_hotkey_warning()

    def _refresh_hotkey_warning(self):
        if self._hotkey_ok:
            self.hotkey_warning.pack_forget()
        else:
            self.hotkey_warning.pack(anchor="w", pady=(4, 0))

    # ======================================================================
    # UI
    # ======================================================================
    def _card(self, parent, title=None):
        card = ctk.CTkFrame(
            parent, corner_radius=14, fg_color=COLOR_CARD,
            border_width=1, border_color=COLOR_BORDER
        )
        card.pack(fill="x", pady=(0, 16))
        inner = ctk.CTkFrame(card, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)
        if title:
            ctk.CTkLabel(
                inner, text=title, font=h_font(14), text_color=COLOR_ACCENT
            ).pack(anchor="w", pady=(0, 12))
        return inner

    def _row(self, parent):
        row = ctk.CTkFrame(parent, fg_color="transparent")
        row.pack(fill="x", pady=6)
        return row

    def _build_ui(self):
        scroll = ctk.CTkScrollableFrame(self.root, fg_color="transparent")
        scroll.pack(fill="both", expand=True, padx=20, pady=20)

        ctk.CTkLabel(
            scroll, text="CC Realtime Translator", font=h_font(20),
            text_color=COLOR_TEXT
        ).pack(anchor="w", pady=(0, 4))
        ctk.CTkLabel(
            scroll, text="อ่านคำบรรยายจากหน้าจอแล้วแปลแบบเรียลไทม์",
            font=n_font(12), text_color=COLOR_MUTED
        ).pack(anchor="w", pady=(0, 18))

        # ---------------- การ์ด 1: กรอบ + ภาษา ----------------
        c1 = self._card(scroll, "1. กรอบ CC และภาษา")

        r = self._row(c1)
        ctk.CTkLabel(r, text="พื้นที่จับภาพ", font=n_font(), width=130, anchor="w").pack(side="left")
        self.region_label = ctk.CTkLabel(
            r, text="ยังไม่ได้กำหนด", font=n_font(), text_color=COLOR_MUTED, anchor="w"
        )
        self.region_label.pack(side="left", fill="x", expand=True)
        ctk.CTkButton(
            r, text="เลือกกรอบ", width=100, corner_radius=8,
            fg_color=COLOR_ACCENT, hover_color=COLOR_ACCENT_HOVER,
            command=self._select_region
        ).pack(side="right", padx=(6, 0))
        ctk.CTkButton(
            r, text="ทดสอบอ่าน", width=100, corner_radius=8,
            fg_color=COLOR_BORDER, hover_color=COLOR_MUTED,
            command=self._test_ocr
        ).pack(side="right")

        r = self._row(c1)
        ctk.CTkLabel(r, text="ภาษาของ CC", font=n_font(), width=130, anchor="w").pack(side="left")
        self.ocr_lang_menu = ctk.CTkOptionMenu(
            r, values=list(OCR_LANGS.keys()), fg_color=COLOR_BORDER,
            button_color=COLOR_ACCENT, button_hover_color=COLOR_ACCENT_HOVER,
        )
        self.ocr_lang_menu.set("อังกฤษ (English)")
        self.ocr_lang_menu.pack(side="left", fill="x", expand=True)

        r = self._row(c1)
        ctk.CTkLabel(r, text="แปลเป็นภาษา", font=n_font(), width=130, anchor="w").pack(side="left")
        self.target_lang_menu = ctk.CTkOptionMenu(
            r, values=list(TRANSLATE_LANGS.keys()), fg_color=COLOR_BORDER,
            button_color=COLOR_ACCENT, button_hover_color=COLOR_ACCENT_HOVER,
        )
        self.target_lang_menu.set("ไทย")
        self.target_lang_menu.pack(side="left", fill="x", expand=True)

        # ---------------- การ์ด 2: เครื่องมือแปล ----------------
        c2 = self._card(scroll, "2. เครื่องมือแปล (Engine)")

        r = self._row(c2)
        ctk.CTkLabel(r, text="ผู้ให้บริการ", font=n_font(), width=130, anchor="w").pack(side="left")
        self.engine_menu = ctk.CTkOptionMenu(
            r, values=ENGINES, fg_color=COLOR_BORDER,
            button_color=COLOR_ACCENT, button_hover_color=COLOR_ACCENT_HOVER,
            command=lambda _=None: self._refresh_engine_status(),
        )
        self.engine_menu.set("Google (ฟรี)")
        self.engine_menu.pack(side="left", fill="x", expand=True)
        self.test_api_btn = ctk.CTkButton(
            r, text="ทดสอบ API", width=100, corner_radius=8,
            fg_color=COLOR_BORDER, hover_color=COLOR_MUTED,
            command=self._test_api
        )
        self.test_api_btn.pack(side="right")

        self.engine_status_label = ctk.CTkLabel(
            c2, text="", font=n_font(11), text_color=COLOR_MUTED, anchor="w", justify="left"
        )
        self.engine_status_label.pack(anchor="w", pady=(4, 0))
        self._refresh_engine_status()

        # ---------------- การ์ด 3: การทำงาน ----------------
        c3 = self._card(scroll, "3. การทำงาน")

        r = self._row(c3)
        ctk.CTkLabel(r, text="รูปแบบคำสั่ง", font=n_font(), width=130, anchor="w").pack(side="left")
        self.trigger_mode_menu = ctk.CTkOptionMenu(
            r, values=["เวลาอย่างเดียว", "คีย์ลัดอย่างเดียว", "ทั้งคู่ (เวลา + คีย์ลัด)"],
            fg_color=COLOR_BORDER, button_color=COLOR_ACCENT,
            button_hover_color=COLOR_ACCENT_HOVER,
            command=lambda v: setattr(self, "_current_trigger_mode", v),
        )
        self.trigger_mode_menu.set(self._current_trigger_mode)
        self.trigger_mode_menu.pack(side="left", fill="x", expand=True)

        r = self._row(c3)
        ctk.CTkLabel(r, text="คีย์ลัดฉุกเฉิน", font=n_font(), width=130, anchor="w").pack(side="left")
        self.hotkey_label = ctk.CTkLabel(
            r, text=self.current_bound_hotkey, font=n_font(weight="bold"), text_color=COLOR_ACCENT
        )
        self.hotkey_label.pack(side="left", padx=(0, 12))
        self.record_btn = ctk.CTkButton(
            r, text="เปลี่ยนคีย์ลัด", width=120, corner_radius=8,
            fg_color=COLOR_BORDER, hover_color=COLOR_MUTED,
            command=self._start_record_hotkey
        )
        self.record_btn.pack(side="left")

        self.hotkey_warning = ctk.CTkLabel(
            c3,
            text="⚠ คีย์ลัดยังไม่ทำงาน — บน Windows ต้องคลิกขวาไฟล์/Terminal แล้วเลือก "
                 "'Run as administrator' ถึงจะดักคีย์ลัดทั้งระบบได้",
            font=n_font(11), text_color=COLOR_WARNING, anchor="w", justify="left",
            wraplength=520,
        )
        self._refresh_hotkey_warning()

        r = self._row(c3)
        ctk.CTkLabel(r, text="ความเร็วอ่านจอ", font=n_font(), width=130, anchor="w").pack(side="left")
        self.interval_value = 2.0
        self.interval_display = ctk.CTkLabel(r, text="2.0 วิ", font=n_font(), width=50)
        self.interval_slider = ctk.CTkSlider(
            r, from_=0.5, to=5.0, number_of_steps=45,
            progress_color=COLOR_ACCENT, button_color=COLOR_ACCENT,
            button_hover_color=COLOR_ACCENT_HOVER,
            command=self._on_interval_change,
        )
        self.interval_slider.set(2.0)
        self.interval_slider.pack(side="left", fill="x", expand=True, padx=(0, 10))
        self.interval_display.pack(side="left")

        r = self._row(c3)
        ctk.CTkLabel(r, text="ขนาดตัวอักษร", font=n_font(), width=130, anchor="w").pack(side="left")
        self.font_size_value = 18
        self.font_size_display = ctk.CTkLabel(r, text="18 px", font=n_font(), width=50)
        self.font_size_slider = ctk.CTkSlider(
            r, from_=10, to=40, number_of_steps=30,
            progress_color=COLOR_ACCENT, button_color=COLOR_ACCENT,
            button_hover_color=COLOR_ACCENT_HOVER,
            command=self._on_font_size_change,
        )
        self.font_size_slider.set(18)
        self.font_size_slider.pack(side="left", fill="x", expand=True, padx=(0, 10))
        self.font_size_display.pack(side="left")

        # ---------------- ปุ่มควบคุมหลัก ----------------
        ctrl = ctk.CTkFrame(scroll, fg_color="transparent")
        ctrl.pack(fill="x", pady=(4, 16))
        self.start_btn = ctk.CTkButton(
            ctrl, text="▶  เริ่มทำงาน", height=42, corner_radius=10,
            font=h_font(14), fg_color=COLOR_SUCCESS, hover_color="#16a34a",
            command=self._start
        )
        self.start_btn.pack(side="left", expand=True, fill="x", padx=(0, 6))
        self.stop_btn = ctk.CTkButton(
            ctrl, text="■  หยุด", height=42, corner_radius=10,
            font=h_font(14), fg_color=COLOR_ERROR, hover_color="#dc2626",
            state="disabled", command=self._stop
        )
        self.stop_btn.pack(side="left", expand=True, fill="x", padx=(6, 0))

        # ---------------- การ์ด 4: Log ----------------
        c4 = self._card(scroll, "ประวัติ / ข้อผิดพลาดล่าสุด")
        self.log_text = ctk.CTkTextbox(
            c4, height=160, corner_radius=8, fg_color=COLOR_BG,
            text_color=COLOR_MUTED, font=("Consolas", 11), wrap="word",
        )
        self.log_text.pack(fill="both", expand=True)
        self.log_text.configure(state="disabled")

        self.status_var = tk.StringVar(value="พร้อมใช้งาน")
        self.status_label = ctk.CTkLabel(
            scroll, textvariable=self.status_var, font=n_font(weight="bold"),
            text_color=COLOR_ACCENT
        )
        self.status_label.pack(anchor="w", pady=(4, 0))

    def _on_interval_change(self, value):
        self.interval_value = float(value)
        self.interval_display.configure(text=f"{self.interval_value:.1f} วิ")

    def _on_font_size_change(self, value):
        self.font_size_value = int(value)
        self.font_size_display.configure(text=f"{self.font_size_value} px")
        if self.overlay:
            self.overlay.set_font_size(self.font_size_value)

    def _refresh_engine_status(self):
        engine = self.engine_menu.get()
        if engine == "DeepL":
            txt = "✔ พบ DEEPL_API_KEY ในไฟล์ .env" if DEEPL_API_KEY else \
                  "✖ ยังไม่ได้ตั้งค่า DEEPL_API_KEY ในไฟล์ .env"
            color = COLOR_SUCCESS if DEEPL_API_KEY else COLOR_WARNING
        elif engine == "Gemini":
            txt = "✔ พบ GEMINI_API_KEY ในไฟล์ .env" if GEMINI_API_KEY else \
                  "✖ ยังไม่ได้ตั้งค่า GEMINI_API_KEY ในไฟล์ .env"
            color = COLOR_SUCCESS if GEMINI_API_KEY else COLOR_WARNING
        else:
            txt = "ผู้ให้บริการฟรี ไม่ต้องใช้ API Key"
            color = COLOR_MUTED
        self.engine_status_label.configure(text=txt, text_color=color)

    # ---------------- Region selection ----------------
    def _select_region(self):
        self.root.withdraw()
        self.root.after(200, self._open_selector)

    def _open_selector(self):
        def done(region):
            self.region = region
            self.region_label.configure(
                text=f"{region['width']}x{region['height']} px @ ({region['left']}, {region['top']})",
                text_color=COLOR_TEXT,
            )
            self.root.deiconify()

        selector = RegionSelector(self.root, done)
        selector.grab_set()
        self.root.wait_window(selector)
        self.root.deiconify()

    # ---------------- ทดสอบอ่านข้อความ ----------------
    def _test_ocr(self):
        if not self.region:
            messagebox.showwarning("ยังไม่ได้เลือกกรอบ", "กรุณาเลือกกรอบ CC ก่อน")
            return
        ocr_lang = OCR_LANGS[self.ocr_lang_menu.get()]
        target_lang = TRANSLATE_LANGS[self.target_lang_menu.get()]
        try:
            with mss.MSS() as sct:
                shot = sct.grab(self.region)
                img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
            text = pytesseract.image_to_string(img, lang=ocr_lang).strip()
            text = clean_ocr_text(" ".join(text.split()))
            if not text:
                messagebox.showinfo(
                    "ผลทดสอบ",
                    "OCR ไม่พบข้อความในกรอบนี้เลย\n\n"
                    "สาเหตุที่พบบ่อย:\n"
                    "- กรอบไม่ได้ครอบตัวอักษร CC จริงๆ\n"
                    "- ตอนทดสอบยังไม่มีคำบรรยายขึ้นบนจอ"
                )
                return
            translated = self._safe_translate(text, ocr_lang, target_lang)
            messagebox.showinfo("ผลทดสอบ", f"ข้อความที่ OCR อ่านได้:\n{text}\n\nคำแปล:\n{translated}")
        except pytesseract.pytesseract.TesseractNotFoundError:
            messagebox.showerror(
                "ไม่พบ Tesseract OCR",
                "ยังไม่ได้ติดตั้ง Tesseract OCR หรือยังไม่ได้ตั้งค่าพาธถูกต้อง\nดูวิธีติดตั้งใน README.md"
            )
        except Exception as e:
            messagebox.showerror("เกิดข้อผิดพลาด", str(e))

    # ---------------- ทดสอบ API (รันบน background thread) ----------------
    def _test_api(self):
        engine = self.engine_menu.get()
        if engine in ("Google (ฟรี)", "MyMemory (ฟรี)"):
            messagebox.showinfo("ทดสอบ API", f"{engine} ไม่ต้องใช้ API Key ใช้งานได้ทันที")
            return

        self.status_var.set(f"กำลังทดสอบเชื่อมต่อ {engine}...")
        self.test_api_btn.configure(state="disabled")

        def worker():
            try:
                result = self._safe_translate("Hello, testing connection.", "eng", "th")
                self.ui_queue.put(("apitest_ok", engine, result))
            except Exception as e:
                self.ui_queue.put(("apitest_err", engine, str(e)))

        threading.Thread(target=worker, daemon=True).start()

    # ---------------- Translate: dispatch + rate-limit guard ----------------
    @staticmethod
    def _is_rate_limit_error(e: Exception) -> bool:
        msg = str(e).lower()
        return "too many requests" in msg or "429" in msg or "server error" in msg

    def _safe_translate(self, text: str, ocr_lang: str, target_lang: str) -> str:
        engine = self.engine_menu.get() if hasattr(self, "engine_menu") else "Google (ฟรี)"
        with self._translate_lock:
            if engine == "Google (ฟรี)":
                wait = _MIN_TRANSLATE_GAP - (time.time() - self._last_translate_ts)
                if wait > 0:
                    time.sleep(wait)
            try:
                if engine == "MyMemory (ฟรี)":
                    # ใช้ _mymemory_translate ข้ามบั๊กของ deep-translator
                    src = OCR_TO_MYMEMORY_SRC.get(ocr_lang, "en")
                    result = self._mymemory_translate(text, src, target_lang)
                elif engine == "DeepL":
                    result = self._deepl_translate(text, target_lang)
                elif engine == "Gemini":
                    result = self._gemini_translate(text, target_lang)
                elif engine == "Local Dictionary (ออฟไลน์)":
                    result = self._local_grammar_translate(text)
                else:
                    result = GoogleTranslator(source="auto", target=target_lang).translate(text)
                    
            except Exception as e:
                if engine == "Google (ฟรี)" and self._is_rate_limit_error(e):
                    # ถ้าระบบ Google โดนจำกัดโควตา ให้สลับไปยิง API ตรงของ MyMemory
                    src = OCR_TO_MYMEMORY_SRC.get(ocr_lang, "en")
                    try:
                        result = self._mymemory_translate(text, src, target_lang)
                    except Exception:
                        self._last_translate_ts = time.time()
                        raise RuntimeError(
                            "ระบบแปลฟรีเต็มโควตาทั้งคู่ (Google และ MyMemory) "
                            "กรุณารอสักครู่ หรือสลับไปใช้ DeepL/Gemini"
                        )
                else:
                    self._last_translate_ts = time.time()
                    raise
            self._last_translate_ts = time.time()

            # ตัวกันสุดท้าย: ถ้าค่าที่ได้กลับมาหน้าตาเหมือนลิสต์รหัสภาษาที่รองรับ
            # ทั้งหมด (บั๊กที่เคยเจอ) ให้ถือว่าแปลไม่สำเร็จ แทนที่จะโชว์ขยะให้เห็น
            if looks_like_language_dump(result):
                raise RuntimeError(
                    f"engine '{engine}' คืนค่าผิดปกติ (ดูเหมือนรายการภาษาที่รองรับ "
                    "ไม่ใช่คำแปลจริง) กรุณาลองเปลี่ยน engine หรือภาษาแล้วลองใหม่"
                )
            return result

    def _deepl_translate(self, text: str, target_lang: str) -> str:
        if not DEEPL_API_KEY:
            raise RuntimeError("ยังไม่ได้ตั้งค่า DEEPL_API_KEY ในไฟล์ .env")
        url = ("https://api-free.deepl.com/v2/translate" if ":fx" in DEEPL_API_KEY
               else "https://api.deepl.com/v2/translate")
        target = DEEPL_TARGET_LANGS.get(target_lang, target_lang.upper())
        payload = {"text": [text], "target_lang": target}
        headers = {"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"}
        try:
            resp = requests.post(url, json=payload, headers=headers, timeout=15)
        except requests.exceptions.RequestException as e:
            raise RuntimeError(f"เชื่อมต่อ DeepL ไม่ได้: {e}")
        if resp.status_code == 403:
            raise RuntimeError("DeepL API Key ไม่ถูกต้องหรือไม่มีสิทธิ์ใช้งาน")
        if resp.status_code == 456:
            raise RuntimeError("โควตา DeepL เต็มสำหรับรอบนี้แล้ว")
        resp.raise_for_status()
        return resp.json()["translations"][0]["text"]

    def _detect_gemini_model(self) -> str:
        fallback = "models/gemini-2.5-flash"
        try:
            resp = requests.get(
                f"https://generativelanguage.googleapis.com/v1beta/models?key={GEMINI_API_KEY}",
                timeout=15,
            )
        except requests.exceptions.RequestException:
            return fallback
        if resp.status_code != 200:
            return fallback
        models_data = resp.json().get("models", [])
        available = [
            m["name"] for m in models_data
            if "generateContent" in m.get("supportedGenerationMethods", [])
        ]
        preferred = [
        'models/gemini-3.6-flash', 'models/gemini-3.5-flash',
        'models/gemini-3.0-flash', 'models/gemini-2.5-flash', 
        'models/gemini-1.5-flash'
        ]
        for p in preferred:
            if p in available:
                return p
        return available[0] if available else fallback

    def _gemini_translate(self, text: str, target_lang: str) -> str:
        if not GEMINI_API_KEY:
            raise RuntimeError("ยังไม่ได้ตั้งค่า GEMINI_API_KEY ในไฟล์ .env")

        if not self._cached_gemini_model:
            self._cached_gemini_model = self._detect_gemini_model()

        lang_name = GEMINI_LANG_NAMES.get(target_lang, target_lang)
        prompt = (
            f"Translate the following live-meeting caption text into {lang_name}. "
            "If a speaker's initials or name appears at the start of a line, keep it as a label. "
            "Output ONLY the translated text, no explanation:\n\n" + text
        )
        payload = {"contents": [{"parts": [{"text": prompt}]}]}

        max_retries = 2
        last_err = "ไม่ทราบสาเหตุ"
        for attempt in range(max_retries + 1):
            url = (
                f"https://generativelanguage.googleapis.com/v1beta/{self._cached_gemini_model}"
                f":generateContent?key={GEMINI_API_KEY}"
            )
            try:
                resp = requests.post(url, json=payload, timeout=20)
            except requests.exceptions.RequestException as e:
                last_err = f"เชื่อมต่อ Gemini ไม่ได้: {e}"
                time.sleep(1.5)
                continue

            if resp.status_code == 200:
                data = resp.json()
                try:
                    return data["candidates"][0]["content"]["parts"][0]["text"].strip()
                except (KeyError, IndexError):
                    raise RuntimeError(f"Gemini ส่งข้อมูลกลับมาผิดรูปแบบ: {data}")

            try:
                err_msg = resp.json().get("error", {}).get("message", resp.text)
            except ValueError:
                err_msg = resp.text
            err_lower = str(err_msg).lower()

            # key ผิด/ไม่มีสิทธิ์ -> ฟ้องทันที ไม่ retry ไม่สลับเงียบๆ
            if resp.status_code in (400, 401, 403) and (
                "api key" in err_lower or "permission" in err_lower or "invalid" in err_lower
            ):
                raise RuntimeError(f"Gemini API Key ไม่ถูกต้องหรือไม่มีสิทธิ์ใช้งาน: {err_msg}")

            if resp.status_code == 404 and "not found" in err_lower:
                self._cached_gemini_model = self._detect_gemini_model()
                continue

            if resp.status_code in (429, 503) or "overloaded" in err_lower or "high demand" in err_lower:
                last_err = err_msg
                if attempt < max_retries:
                    time.sleep(2.0)
                    continue

            last_err = err_msg
            break

        raise RuntimeError(f"Gemini ไม่พร้อมใช้งานชั่วคราว ({last_err}) ลองใหม่ หรือสลับเป็น Google/DeepL")
    
    def _mymemory_translate(self, text: str, src: str, tgt: str) -> str:
        url = "https://api.mymemory.translated.net/get"
        params = {"q": text, "langpair": f"{src}|{tgt}"}
        try:
            resp = requests.get(url, params=params, timeout=10)
            resp.raise_for_status()
            data = resp.json()
            if data.get("responseStatus") == 200:
                return data["responseData"]["translatedText"]
            else:
                raise RuntimeError(data.get("responseDetails", "เกิดข้อผิดพลาดจากเซิร์ฟเวอร์ MyMemory"))
        except Exception as e:
            raise RuntimeError(f"เชื่อมต่อ MyMemory ล้มเหลว: {e}")
        
        
    def _local_grammar_translate(self, text: str) -> str:
        if not LOCAL_DICT:
            raise RuntimeError("ไม่พบไฟล์พจนานุกรม JSON หรือโหลดข้อมูลไม่สำเร็จ")

        # จัดการตัวย่อภาษาอังกฤษก่อน เพื่อไม่ให้ระบบหั่น I'm เป็น I กับ m
        text = re.sub(r"(?i)\bi'm\b", "I am", text)
        text = re.sub(r"(?i)\bit's\b", "it is", text)
        text = re.sub(r"(?i)\bcan't\b", "cannot", text)
        text = re.sub(r"(?i)\bdon't\b", "do not", text)
        text = re.sub(r"(?i)\bdoesn't\b", "does not", text)
        text = re.sub(r"(?i)\bthat's\b", "that is", text)
        text = re.sub(r"(?i)\bthere's\b", "there is", text)
        text = re.sub(r"(?i)\bwhat's\b", "what is", text)

        # 1. แยกประโยคออกเป็นคำๆ และเก็บเครื่องหมายวรรคตอนไว้
        raw_tokens = re.findall(r'\b\w+\b|[^\w\s]', text)
        words_data = []

        # 2. ค้นหาคำศัพท์และ POS
        for w in raw_tokens:
            if re.match(r'[^\w\s]', w):
                words_data.append({"word": w, "th": w, "pos": "PUNCT"})
                continue
                
            lw = w.lower()
            
            # กฎข้อที่ 1: ข้ามคำนำหน้า (a, an, the) ภาษาไทยไม่ต้องแปลทุกคำ
            if lw in ['a', 'an', 'the']:
                continue

            entry = LOCAL_DICT.get(lw)
            if entry:
                words_data.append({"word": w, "th": entry["th"], "pos": entry["pos"]})
            else:
                # ถ้าหาไม่เจอ ให้ทับศัพท์
                words_data.append({"word": w, "th": w, "pos": "UNKNOWN"})

        # 3. จัดไวยากรณ์ (Grammar Rules) โดยใช้ POS
        i = 0
        while i < len(words_data) - 1:
            curr_pos = words_data[i]["pos"]
            next_pos = words_data[i+1]["pos"]

            # กฎข้อที่ 2: Adjective + Noun -> สลับเป็น Noun + Adjective (เช่น Good boy -> Boy good)
            if curr_pos == "ADJ" and next_pos in ["N", "PRON"]:
                words_data[i], words_data[i+1] = words_data[i+1], words_data[i]
                i += 2  # ข้ามไป 2 คำเลยเพราะสลับเสร็จแล้ว
                
            # กฎข้อที่ 3: Adverb + Verb -> สลับเป็น Verb + Adverb (เช่น Quickly run -> Run quickly)
            elif curr_pos == "ADV" and next_pos == "V":
                words_data[i], words_data[i+1] = words_data[i+1], words_data[i]
                i += 2
                
            else:
                i += 1

        # 4. นำคำแปลมาต่อกัน (ภาษาไทยไม่ต้องเว้นวรรคระหว่างคำ)
        translated_text = "".join([item["th"] for item in words_data])
        
        return translated_text

    # ---------------- Start / Stop ----------------
    def _start(self):
        if not self.region:
            messagebox.showwarning("ยังไม่ได้เลือกกรอบ", "กรุณาเลือกกรอบ CC ก่อนเริ่มแปล")
            return

        self.running = True
        self.last_text = ""
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.status_var.set("กำลังทำงาน...")

        self.overlay = CaptionOverlay(self.root)
        self.overlay.set_font_size(self.font_size_value)
        self.region_indicator = RegionIndicator(self.root, self.region)

        ocr_lang = OCR_LANGS[self.ocr_lang_menu.get()]
        target_lang = TRANSLATE_LANGS[self.target_lang_menu.get()]

        self.worker_thread = threading.Thread(
            target=self._capture_loop, args=(ocr_lang, target_lang), daemon=True
        )
        self.worker_thread.start()

    def _stop(self):
        self.running = False
        self.start_btn.configure(state="normal")
        self.stop_btn.configure(state="disabled")
        self.status_var.set("หยุดทำงาน")
        if self.overlay:
            self.overlay.destroy()
            self.overlay = None
        if self.region_indicator:
            self.region_indicator.destroy()
            self.region_indicator = None

    # ---------------- Background worker ----------------
    def _capture_loop(self, ocr_lang, target_lang):
        timer_count = 0.0
        with mss.MSS() as sct:
            while self.running:
                time.sleep(0.1)
                timer_count += 0.1

                mode = self._current_trigger_mode
                should_capture = False
                if mode == "คีย์ลัดอย่างเดียว":
                    should_capture = self._force_capture
                elif mode == "เวลาอย่างเดียว":
                    should_capture = timer_count >= self.interval_value
                else:
                    should_capture = self._force_capture or timer_count >= self.interval_value

                if not should_capture:
                    continue

                timer_count = 0.0
                self._force_capture = False

                try:
                    shot = sct.grab(self.region)
                    img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
                    text = pytesseract.image_to_string(img, lang=ocr_lang).strip()
                    text = clean_ocr_text(" ".join(text.split()))

                    if text and self._is_new_text(text):
                        try:
                            translated = self._safe_translate(text, ocr_lang, target_lang)
                        except Exception as e:
                            translated = f"[แปลไม่สำเร็จ: {e}]"
                        self.ui_queue.put(("caption", text, translated))
                except Exception as e:
                    self.ui_queue.put(("error", str(e), ""))

    def _is_new_text(self, text: str) -> bool:
        translator = str.maketrans("", "", string.punctuation)
        clean_new = text.translate(translator).replace(" ", "").lower()
        clean_old = self.last_text.translate(translator).replace(" ", "").lower()
        if len(clean_new) < 2:
            return False
        ratio = difflib.SequenceMatcher(None, clean_new, clean_old).ratio()
        if ratio < 0.85:
            self.last_text = text
            return True
        return False

    # ---------------- UI thread queue polling ----------------
    def _poll_queue(self):
        try:
            while True:
                kind, a, b = self.ui_queue.get_nowait()
                if kind == "caption":
                    if self.overlay:
                        self.overlay.show_text(a, b)
                    self._append_log(f"อ่าน: {a}\nแปล: {b}\n\n")
                elif kind == "error":
                    self.status_var.set(f"พบปัญหา: {a}")
                    self._append_log(f"[ข้อผิดพลาด] {a}\n\n")
                elif kind == "apitest_ok":
                    self.test_api_btn.configure(state="normal")
                    self.status_var.set("เชื่อมต่อ API สำเร็จ")
                    messagebox.showinfo("ทดสอบ API สำเร็จ", f"เชื่อมต่อ {a} สำเร็จ\nผลการแปล: {b}")
                elif kind == "apitest_err":
                    self.test_api_btn.configure(state="normal")
                    self.status_var.set("ทดสอบ API ล้มเหลว")
                    messagebox.showerror("ทดสอบ API ล้มเหลว", f"{a}:\n{b}")
        except queue.Empty:
            pass
        self.root.after(150, self._poll_queue)

    def _append_log(self, text):
        self.log_text.configure(state="normal")
        self.log_text.insert("end", text)
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def run(self):
        self.root.mainloop()
        
    def _on_close(self):
            self.running = False
            self.status_var.set("กำลังปิดโปรแกรม...")
            self.root.update()
            
            # 1. คืนค่าปุ่มคีย์ลัดทั้งหมดให้ระบบ (ป้องกันปุ่มค้าง)
            try:
                if _KEYBOARD_AVAILABLE:
                    keyboard.unhook_all()
            except Exception:
                pass
                
            # 2. ปิดหน้าต่าง UI ทั้งหมด
            self.root.destroy()
            
            # 3. บังคับจบ Process ทิ้ง 100% (ป้องกัน Background Thread ค้างเติ่ง)
            sys.exit(0)


if __name__ == "__main__":
    App().run()