"""
CC Realtime Translator
=======================
โปรแกรมสำหรับจับภาพเฉพาะ "กรอบ" บนหน้าจอที่แสดงคำบรรยาย (CC / Closed Caption)
จาก Zoom, Microsoft Teams หรือโปรแกรมประชุมอื่นๆ แล้วอ่านข้อความด้วย OCR
และแปลภาษาแบบเกือบเรียลไทม์ แสดงผลเป็นแถบคำบรรยายลอย (overlay) บนหน้าจอ

**ไม่มีการเข้าร่วมประชุมใดๆ ทั้งสิ้น** โปรแกรมนี้แค่ "ถ่ายภาพหน้าจอ" ในบริเวณ
ที่คุณเลือกเองซ้ำๆ ทุก 1-2 วินาที เหมือนการแคปหน้าจอ ไม่ได้เชื่อมต่อกับ
Zoom/Teams API หรือแอบดักข้อมูลใดๆ

การทำงานคร่าวๆ
----------------
1. เลือกกรอบ (region) บนหน้าจอที่ตำแหน่ง CC ของ Zoom/Teams ปรากฏอยู่
2. ระหว่างทำงานจะมี "กรอบเส้นเขียว" ค้างอยู่รอบบริเวณที่กำลังจับภาพ เพื่อยืนยันตำแหน่ง
3. โปรแกรมแคปภาพเฉพาะกรอบนั้นซ้ำๆ ตามรอบเวลาที่ตั้งไว้ แล้วอ่านข้อความด้วย OCR
4. เทียบกับข้อความล่าสุด ถ้าเป็นข้อความใหม่ -> ส่งไปแปล
5. แสดงคำแปลบนแถบ overlay ลอยเหนือหน้าจอ (คล้ายซับไตเติล) ลากย้าย/ย่อขยายได้อิสระ

การติดตั้ง (ทำครั้งเดียว)
--------------------------
1. ติดตั้ง Python 3.9 ขึ้นไป
2. ติดตั้งไลบรารี Python:
       pip install -r requirements.txt
3. ติดตั้งตัวโปรแกรม Tesseract OCR (แยกจาก pip เพราะเป็นโปรแกรมระบบ):
   - Windows: ดาวน์โหลดตัวติดตั้งจาก
       https://github.com/UB-Mannheim/tesseract/wiki
     ติดตั้งแล้วจดพาธ เช่น C:\\Program Files\\Tesseract-OCR\\tesseract.exe
     แล้วใส่ในตัวแปร TESSERACT_CMD ด้านล่าง (หรือปล่อยว่างถ้า auto-detect เจอ)
   - macOS:  brew install tesseract tesseract-lang
   - Ubuntu/Debian: sudo apt install tesseract-ocr tesseract-ocr-tha tesseract-ocr-eng

การใช้งาน
----------
    python cc_realtime_translator.py

แล้วกด "เลือกกรอบ CC" -> ลากกรอบสี่เหลี่ยมครอบตำแหน่งคำบรรยายบนหน้าจอ
กด "ทดสอบอ่านข้อความ" เพื่อเช็คว่ากรอบ/OCR ทำงานถูกต้องก่อน แล้วค่อยกด "เริ่มแปล"
"""

import sys
import difflib
import queue
import re
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox

import mss
import pytesseract
from PIL import Image
from deep_translator import GoogleTranslator, MyMemoryTranslator

import os
from dotenv import load_dotenv
import google.generativeai as genai
import requests
import string
import keyboard
import sv_ttk

# โหลดตัวแปรจากไฟล์ .env ทันทีที่เริ่มโปรแกรม
load_dotenv()

# ==========================================
# ดึง API KEY จากระบบ (ซึ่งโหลดมาจาก .env แล้ว)
# ถ้าไม่เจอไฟล์ .env หรือไม่ได้ตั้งค่าไว้ จะได้ค่าว่าง ("")
# ==========================================
DEEPL_API_KEY = os.getenv("DEEPL_API_KEY", "")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "")

if GEMINI_API_KEY:
    genai.configure(api_key=GEMINI_API_KEY)
# ==========================================

# แปลง code ภาษาที่ OCR ใช้ -> code ภาษาที่ MyMemoryTranslator (ตัวแปลสำรอง) ต้องการ
OCR_TO_MYMEMORY_SRC = {
    "eng": "en", "tha": "th", "chi_sim": "zh-CN",
    "jpn": "ja", "kor": "ko", "vie": "vi",
}

# ระยะห่างขั้นต่ำระหว่างการยิงคำขอแปลแต่ละครั้ง (วินาที) กันชนโควตา
# Google Translate แบบไม่ใช้ API key (5 คำขอ/วินาที) ของ deep-translator
_MIN_TRANSLATE_GAP = 1.2

# ----------------------------------------------------------------------
# แก้ปัญหา DPI scaling บน Windows: ถ้าไม่ทำตรงนี้ พิกัดที่ tkinter รายงาน
# (ตอนลากเลือกกรอบ) จะไม่ตรงกับพิกัดพิกเซลจริงที่ mss ใช้จับภาพ เวลาจอตั้งค่า
# scale เกิน 100% (พบบ่อยมาก) ผลคือกรอบที่เลือกไปจับภาพผิดตำแหน่ง/ว่างเปล่า
# ทำให้ OCR ไม่เจอข้อความและไม่แปลตลอด ต้องเรียกก่อนสร้างหน้าต่างใดๆ ทั้งหมด
if sys.platform == "win32":
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(2)  # PER_MONITOR_DPI_AWARE
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

# ----------------------------------------------------------------------
# ถ้า pytesseract หา tesseract.exe ไม่เจอเอง (มักเกิดบน Windows)
# ให้ใส่พาธเต็มตรงนี้ เช่น:
TESSERACT_CMD = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
# TESSERACT_CMD = ""
if TESSERACT_CMD:
    pytesseract.pytesseract.tesseract_cmd = TESSERACT_CMD

# รายการภาษาที่ให้เลือก (แสดงผล -> รหัสสำหรับ OCR, รหัสสำหรับแปล)
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

# สัญลักษณ์ที่ OCR มักอ่านผิดจากไอคอนวงกลม (avatar), ตราสัญลักษณ์, บูลเล็ต ฯลฯ
# ที่ไม่ใช่ตัวอักษรจริงในคำบรรยาย ตัดทิ้งก่อนส่งไปแปล ลดความมั่วของข้อความ
_OCR_NOISE_RE = re.compile(r'(?:^|(?<=\s))[@®©™†‡•●○◦§¶|_~]+(?:(?=\s)|$)')


def clean_ocr_text(text: str) -> str:
    """ตัดสัญลักษณ์ขยะที่มักเกิดจาก OCR อ่านไอคอน/avatar ผิด แล้วยุบช่องว่างซ้ำ"""
    cleaned = _OCR_NOISE_RE.sub(" ", text)
    cleaned = re.sub(r"\s{2,}", " ", cleaned).strip()
    return cleaned


class RegionSelector(tk.Toplevel):
    """หน้าต่างเต็มจอโปร่งใสสำหรับให้ผู้ใช้ลากเลือกกรอบ CC"""

    def __init__(self, master, on_selected):
        super().__init__(master)
        self.on_selected = on_selected
        self.attributes("-fullscreen", True)
        self.attributes("-alpha", 0.25)
        self.configure(bg="black")
        self.attributes("-topmost", True)
        self.config(cursor="crosshair")

        self.canvas = tk.Canvas(self, bg="black", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        info = tk.Label(
            self,
            text="ลากเมาส์ครอบบริเวณคำบรรยาย (CC) แล้วปล่อย   |   กด Esc เพื่อยกเลิก",
            fg="white",
            bg="black",
            font=("Tahoma", 14, "bold"),
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
            outline="#00ff88", width=3
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

        border = 3
        if sys.platform == "win32":
            # ใช้เทคนิค transparentcolor ให้ "ข้างใน" กรอบโปร่งใสจริง เห็น CC ปกติ
            # เหลือแค่เส้นขอบสีเขียวให้เห็นตำแหน่ง
            trans_color = "magenta"
            try:
                self.configure(bg=trans_color)
                self.attributes("-transparentcolor", trans_color)
                inner_bg = trans_color
            except tk.TclError:
                inner_bg = "#101010"
                try:
                    self.attributes("-alpha", 0.2)
                except tk.TclError:
                    pass
            inner = tk.Frame(
                self, bg=inner_bg, highlightbackground="#00ff88",
                highlightcolor="#00ff88", highlightthickness=border
            )
            inner.pack(fill="both", expand=True)
        else:
            # macOS/Linux: tkinter ไม่รองรับ transparentcolor แบบ Windows
            # จึงใช้กรอบโปร่งแสงบางๆ แทน (ไม่บังข้อความมากนัก)
            try:
                self.attributes("-alpha", 0.25)
            except tk.TclError:
                pass
            self.configure(bg="#00ff88")
            inner = tk.Frame(self, bg="#101010")
            inner.pack(fill="both", expand=True, padx=border, pady=border)


class CaptionOverlay(tk.Toplevel):
    """แถบคำบรรยายลอยเหนือหน้าจอ ลากย้ายตำแหน่งและย่อ/ขยายขนาดได้อิสระ"""

    MIN_W, MIN_H = 240, 80

    def __init__(self, master):
        super().__init__(master)
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.88)
        except tk.TclError:
            pass
        self.configure(bg="#101010")

        self._drag_offset = (0, 0)
        self._resizing = False
        self._resize_start = (0, 0, 0, 0)

        self.orig_var = tk.StringVar(value="")
        self.trans_var = tk.StringVar(value="รอข้อความ CC...")

        # แถบลากย้ายด้านบน (ลากตรงไหนของกล่องก็ย้ายได้ ไม่ใช่แค่แถบนี้)
        self.drag_bar = tk.Frame(self, bg="#2a2a2a", height=14, cursor="fleur")
        self.drag_bar.pack(fill="x", side="top")

        body = tk.Frame(self, bg="#101010")
        body.pack(fill="both", expand=True)

        self.orig_label = tk.Label(
            body, textvariable=self.orig_var, fg="#9a9a9a", bg="#101010",
            font=("Tahoma", 11), wraplength=760, justify="center", cursor="fleur"
        )
        self.orig_label.pack(padx=16, pady=(8, 2), fill="x")

        self.trans_label = tk.Label(
            body, textvariable=self.trans_var, fg="#ffffff", bg="#101010",
            font=("Tahoma", 18, "bold"), wraplength=760, justify="center", cursor="fleur"
        )
        self.trans_label.pack(padx=16, pady=(2, 8), fill="x")

        # ลากย้ายตำแหน่งได้จากทุกจุดของกล่อง (ยกเว้นมุมจับปรับขนาด)
        for widget in (self, self.drag_bar, body, self.orig_label, self.trans_label):
            widget.bind("<ButtonPress-1>", self._start_move)
            widget.bind("<B1-Motion>", self._on_move)

        # มุมจับปรับขนาดที่มุมขวาล่าง
        self.grip = tk.Label(self, text="◢", fg="#777", bg="#101010", cursor="size_nw_se")
        self.grip.place(relx=1.0, rely=1.0, anchor="se")
        self.grip.bind("<ButtonPress-1>", self._start_resize)
        self.grip.bind("<B1-Motion>", self._on_resize)

        self.update_idletasks()
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        w = 760
        h = self.winfo_reqheight()
        x = (screen_w - w) // 2
        y = screen_h - h - 60
        self.geometry(f"{w}x{h}+{x}+{y}")

    # ---- ลากย้ายตำแหน่ง ----
    def _start_move(self, event):
        self._drag_offset = (event.x_root - self.winfo_x(), event.y_root - self.winfo_y())

    def _on_move(self, event):
        x = event.x_root - self._drag_offset[0]
        y = event.y_root - self._drag_offset[1]
        self.geometry(f"+{x}+{y}")

    # ---- ปรับขนาด ----
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

        font_size = max(10, min(30, new_h // 5))
        # self.trans_label.config(font=("Tahoma", font_size, "bold"))
        # self.orig_label.config(font=("Tahoma", max(8, font_size - 7)))

    def show_text(self, original: str, translated: str):
        self.orig_var.set(original)
        self.trans_var.set(translated)


class App:
    def _trigger_force_capture(self):
        if self.running:
            self._force_capture = True
    
    def _start_record_hotkey(self):
        # เปลี่ยนสถานะปุ่มและข้อความ เพื่อบอกให้ผู้ใช้รู้ว่ากำลังรอรับคำสั่ง
        self.record_btn.config(text="กำลังรอ... (กดปุ่มที่ต้องการ)", state="disabled")
        self.hotkey_var.set("กำลังบันทึก...")
        
        # ต้องรันใน Thread เพื่อไม่ให้หน้าต่าง UI ค้างระหว่างรอผู้ใช้กดคีย์บอร์ด
        threading.Thread(target=self._record_hotkey_thread, daemon=True).start()

    def _record_hotkey_thread(self):
        try:
            # ฟังก์ชันนี้จะรอจนกว่าผู้ใช้จะกดปุ่ม (หรือคอมโบ) แล้วปล่อย
            # เช่น ถ้าผู้ใช้กด Ctrl ค้างไว้ แล้วกด T มันจะคืนค่า "ctrl+t"
            new_hotkey = keyboard.read_hotkey(suppress=False)
            
            # เมื่อได้ปุ่มมาแล้ว ให้ส่งกลับไปจัดการต่อใน Main Thread (UI Thread)
            self.root.after(0, self._apply_recorded_hotkey, new_hotkey)
        except Exception:
            self.root.after(0, self._apply_recorded_hotkey, self.current_bound_hotkey)

    def _apply_recorded_hotkey(self, new_hotkey):
        # คืนสถานะปุ่มกลับมาเป็นปกติ
        self.record_btn.config(text="เปลี่ยนคีย์ลัด (Record)", state="normal")
        
        try:
            # ยกเลิกปุ่มเก่า
            if self.current_bound_hotkey:
                keyboard.remove_hotkey(self.current_bound_hotkey)
            
            # ผูกปุ่มใหม่
            keyboard.add_hotkey(new_hotkey, self._trigger_force_capture)
            self.current_bound_hotkey = new_hotkey
            self.hotkey_var.set(new_hotkey)
            
        except Exception as e:
            messagebox.showerror("ข้อผิดพลาด", f"ปุ่มนี้ไม่สามารถใช้เป็นคีย์ลัดได้\n\n{e}")
            # ถ้ามี Error ให้ดึงปุ่มเดิมกลับมาใช้
            self.hotkey_var.set(self.current_bound_hotkey)
            keyboard.add_hotkey(self.current_bound_hotkey, self._trigger_force_capture)
            
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("CC Realtime Translator")
        self.root.geometry("550x720") 
        self.root.resizable(True, True)
        self.root.minsize(550, 720)

        # ====== เปิดใช้งาน UI สไตล์ Windows 11 ======
        sv_ttk.set_theme("dark")  # เปลี่ยนเป็น "light" ได้ถ้าชอบโทนสว่าง
        # =======================================

        self.region = None
        
        # กำหนดขนาดเริ่มต้นตอนเปิดโปรแกรม
        self.root.geometry("550x780") 
        
        # อนุญาตให้ย่อ/ขยายหน้าต่างได้อิสระ (True, True = ขยายได้ทั้งแกน X และ Y)
        self.root.resizable(True, True)

        self.running = False
        
        # ตั้งคีย์ลัดเป็น Ctrl + Shift + T สำหรับสั่งแปลทันที
        self._force_capture = False
        # keyboard.add_hotkey('ctrl+shift+t', self._trigger_force_capture)
        self._current_trigger_mode = "ทั้งคู่ (เวลา + คีย์ลัด)" # เพิ่มบรรทัดนี้
        # --- เพิ่มตัวแปรสำหรับคีย์ลัดที่ปรับแก้ได้ ---
        self.current_bound_hotkey = "ctrl+shift+t"
        try:
            keyboard.add_hotkey(self.current_bound_hotkey, self._trigger_force_capture)
        except Exception:
            pass

        self.region = None
        self.running = False
        self.worker_thread = None
        self.overlay = None
        self.region_indicator = None
        self.ui_queue = queue.Queue()
        self.last_text = ""
        self._translate_lock = threading.Lock()
        self._last_translate_ts = 0.0

        self._build_ui()
        self.root.after(150, self._poll_queue)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------- UI ----------------
    def _build_ui(self):
        pad = {"padx": 14, "pady": 8}

        frm_region = ttk.LabelFrame(self.root, text="1) กรอบ CC บนหน้าจอ")
        frm_region.pack(fill="x", **pad)
        self.region_label = ttk.Label(frm_region, text="ยังไม่ได้เลือกกรอบ")
        self.region_label.pack(side="left", padx=10, pady=10)
        btns = ttk.Frame(frm_region)
        btns.pack(side="right", padx=10, pady=6)
        ttk.Button(btns, text="เลือกกรอบ CC", command=self._select_region).pack(
            side="top", fill="x", pady=(0, 4)
        )
        ttk.Button(btns, text="ทดสอบอ่านข้อความ", command=self._test_ocr).pack(
            side="top", fill="x"
        )

        frm_lang = ttk.LabelFrame(self.root, text="2) ภาษา")
        frm_lang.pack(fill="x", **pad)

        ttk.Label(frm_lang, text="ภาษาต้นฉบับ (ภาษาของ CC):").grid(
            row=0, column=0, sticky="w", padx=10, pady=6
        )
        self.ocr_lang_var = tk.StringVar(value="อังกฤษ (English)")
        ttk.Combobox(
            frm_lang, textvariable=self.ocr_lang_var, values=list(OCR_LANGS.keys()),
            state="readonly", width=20
        ).grid(row=0, column=1, padx=10, pady=6)

        ttk.Label(frm_lang, text="แปลเป็นภาษา:").grid(
            row=1, column=0, sticky="w", padx=10, pady=6
        )
        self.target_lang_var = tk.StringVar(value="ไทย")
        ttk.Combobox(
            frm_lang, textvariable=self.target_lang_var, values=list(TRANSLATE_LANGS.keys()),
            state="readonly", width=20
        ).grid(row=1, column=1, padx=10, pady=6)
        
        ttk.Label(frm_lang, text="ระบบแปลภาษา:").grid(
            row=2, column=0, sticky="w", padx=10, pady=6
        )
        self.engine_var = tk.StringVar(value="Google (Free)")
        ttk.Combobox(
            frm_lang, textvariable=self.engine_var, 
            values=["Google (Free)", "DeepL", "Gemini"],
            state="readonly", width=20
        ).grid(row=2, column=1, padx=10, pady=6)
        
        # เพิ่มปุ่ม Test API หลังจากเลือก Engine
        ttk.Button(frm_lang, text="ทดสอบ API", command=self._test_api).grid(
            row=2, column=2, padx=10, pady=6
        )

        frm_speed = ttk.LabelFrame(self.root, text="3) ความถี่ในการอ่านหน้าจอ")
        frm_speed.pack(fill="x", **pad)
        self.interval_var = tk.DoubleVar(value=3.0)

        # ====== โค้ดที่ต้องเพิ่มใหม่ (Dropdown เลือกโหมด) ======
        ttk.Label(frm_speed, text="โหมดการสั่งแปล:").pack(padx=10, anchor="w", pady=(5, 0))
        
        self.trigger_mode_var = tk.StringVar(value="ทั้งคู่ (เวลา + คีย์ลัด)")
        ttk.Combobox(
            frm_speed, textvariable=self.trigger_mode_var,
            values=["เวลาอย่างเดียว", "คีย์ลัดอย่างเดียว", "ทั้งคู่ (เวลา + คีย์ลัด)"],
            state="readonly"
        ).pack(fill="x", padx=10, pady=(0, 10))
        
        # อัปเดตตัวแปรเมื่อมีการเปลี่ยนโหมด (เพื่อให้ Thread อ่านได้ปลอดภัย)
        self.trigger_mode_var.trace_add(
            "write", 
            lambda *_: setattr(self, '_current_trigger_mode', self.trigger_mode_var.get())
        )
        # ===============================================
        
        # ====== โค้ดส่วนตั้งค่าคีย์ลัด (แบบดักจับการกดปุ่มจริง) ======
        ttk.Label(frm_speed, text="คีย์ลัดสั่งแปลทันที:").pack(padx=10, anchor="w", pady=(5, 0))
        hotkey_frame = ttk.Frame(frm_speed)
        hotkey_frame.pack(fill="x", padx=10, pady=(0, 10))
        
        self.hotkey_var = tk.StringVar(value=self.current_bound_hotkey)
        self.hotkey_lbl = ttk.Label(
            hotkey_frame, textvariable=self.hotkey_var, 
            font=("Tahoma", 10, "bold"), foreground="#0078D7"
        )
        self.hotkey_lbl.pack(side="left", padx=(0, 15))
        
        self.record_btn = ttk.Button(
            hotkey_frame, text="เปลี่ยนคีย์ลัด (Record)", command=self._start_record_hotkey
        )
        self.record_btn.pack(side="left")
        # =======================================================
        
        ttk.Scale(
            frm_speed, from_=0.5, to=4.0, variable=self.interval_var, orient="horizontal"
        ).pack(fill="x", padx=10, pady=(10, 0))
        self.interval_display = ttk.Label(frm_speed, text="ทุก 3.0 วินาที")
        self.interval_display.pack(padx=10, pady=(0, 10))
        self.interval_var.trace_add(
            "write",
            lambda *_: self.interval_display.config(
                text=f"ทุก {self.interval_var.get():.1f} วินาที"
            ),
        )
        
        # เพิ่มตัวปรับขนาดฟอนต์
        self.font_size_var = tk.IntVar(value=18)
        ttk.Label(frm_speed, text="ขนาดฟอนต์คำแปล:").pack(padx=10, anchor="w")
        ttk.Scale(
            frm_speed, from_=10, to=40, variable=self.font_size_var, orient="horizontal",
            command=self._update_font_size
        ).pack(fill="x", padx=10, pady=(0, 10))

        frm_ctrl = ttk.Frame(self.root)
        frm_ctrl.pack(fill="x", **pad)
        self.start_btn = ttk.Button(frm_ctrl, text="▶ เริ่มแปล", command=self._start)
        self.start_btn.pack(side="left", expand=True, fill="x", padx=(0, 5))
        self.stop_btn = ttk.Button(
            frm_ctrl, text="■ หยุด", command=self._stop, state="disabled"
        )
        self.stop_btn.pack(side="left", expand=True, fill="x", padx=(5, 0))

        frm_log = ttk.LabelFrame(self.root, text="ประวัติ / ข้อผิดพลาดล่าสุด")
        frm_log.pack(fill="both", expand=True, **pad)
        self.log_text = tk.Text(frm_log, height=8, wrap="word", state="disabled")
        self.log_text.pack(fill="both", expand=True, padx=8, pady=8)

        # self.status_var = tk.StringVar(value="พร้อมใช้งาน")
        # ttk.Label(self.root, textvariable=self.status_var, foreground="#555").pack(
        #     anchor="w", padx=16, pady=(0, 8)
        # )
        
        # ลบ foreground="#555" ออก และเพิ่มตัวหนาให้ดูชัดเจนขึ้น
        self.status_var = tk.StringVar(value="พร้อมใช้งาน")
        ttk.Label(self.root, textvariable=self.status_var, font=("Tahoma", 10, "bold")).pack(
            anchor="w", padx=16, pady=(0, 8)
        )

    # ---------------- Region selection ----------------
    def _select_region(self):
        self.root.withdraw()
        self.root.after(200, self._open_selector)

    def _open_selector(self):
        def done(region):
            self.region = region
            self.region_label.config(
                text=f"กรอบ: {region['width']}x{region['height']} px "
                     f"@ ({region['left']}, {region['top']})"
            )
            self.root.deiconify()

        selector = RegionSelector(self.root, done)
        selector.grab_set()
        self.root.wait_window(selector)
        self.root.deiconify()

    # ---------------- ทดสอบอ่านข้อความ (ก่อนเริ่มจริง) ----------------
    def _test_ocr(self):
        if not self.region:
            messagebox.showwarning("ยังไม่ได้เลือกกรอบ", "กรุณาเลือกกรอบ CC ก่อน")
            return
        ocr_lang = OCR_LANGS[self.ocr_lang_var.get()]
        target_lang = TRANSLATE_LANGS[self.target_lang_var.get()]
        try:
            with mss.MSS() as sct:
                shot = sct.grab(self.region)
                img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
            text = pytesseract.image_to_string(img, lang=ocr_lang).strip()
            text = " ".join(text.split())
            text = clean_ocr_text(text)
            if not text:
                messagebox.showinfo(
                    "ผลทดสอบ",
                    "OCR ไม่พบข้อความในกรอบนี้เลย\n\n"
                    "สาเหตุที่พบบ่อย:\n"
                    "- กรอบไม่ได้ครอบตัวอักษร CC จริงๆ (พิกัดเพี้ยนจาก DPI scaling)\n"
                    "- ตอนทดสอบยังไม่มีคำบรรยายขึ้นบนจอ\n\n"
                    "ลองเปิด CC ให้ขึ้นข้อความก่อน แล้วเลือกกรอบใหม่ให้แคบพอดีตัวอักษร"
                )
                return
            translated = self._safe_translate(text, ocr_lang, target_lang)
            messagebox.showinfo("ผลทดสอบ", f"ข้อความที่ OCR อ่านได้:\n{text}\n\nคำแปล:\n{translated}")
        except pytesseract.pytesseract.TesseractNotFoundError:
            messagebox.showerror(
                "ไม่พบ Tesseract OCR",
                "ยังไม่ได้ติดตั้ง Tesseract OCR หรือยังไม่ได้ตั้งค่า TESSERACT_CMD "
                "ในไฟล์ cc_realtime_translator.py\n\nดูวิธีติดตั้งใน README.md"
            )
        except Exception as e:
            messagebox.showerror("เกิดข้อผิดพลาด", str(e))

    # ---------------- แปลแบบมีตัวจำกัดความถี่ + ตัวสำรองถ้าโดน rate limit ----------------
    def _safe_translate(self, text: str, ocr_lang: str, target_lang: str) -> str:
        engine = self.engine_var.get()
        
        with self._translate_lock:
            # หน่วงเวลาเฉพาะ Google เพื่อกันโดนแบน
            if engine == "Google (Free)":
                wait = _MIN_TRANSLATE_GAP - (time.time() - self._last_translate_ts)
                if wait > 0:
                    time.sleep(wait)

            try:
                if engine == "DeepL":
                    if not DEEPL_API_KEY:
                        raise ValueError("ยังไม่ได้ใส่ DEEPL_API_KEY ในโค้ด")
                    
                    url = "https://api-free.deepl.com/v2/translate" if ":fx" in DEEPL_API_KEY else "https://api.deepl.com/v2/translate"
                    # DeepL ใช้รหัสภาษาต่างออกไปเล็กน้อย เช่น EN, TH (ตัวพิมพ์ใหญ่)
                    target = "EN-US" if target_lang == "en" else target_lang.upper()
                    
                    payload = {"text": [text], "target_lang": target}
                    headers = {"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}", "Content-Type": "application/json"}
                    
                    resp = requests.post(url, json=payload, headers=headers)
                    resp.raise_for_status()
                    result = resp.json()["translations"][0]["text"]

                elif engine == "Gemini":
                    if not GEMINI_API_KEY:
                        raise ValueError("ยังไม่ได้ใส่ GEMINI_API_KEY ในโค้ดหรือไฟล์ .env")
                    
                    # 1. เช็ครายชื่อโมเดล (โค้ดส่วนนี้เหมือนเดิม)
                    if not hasattr(self, '_cached_gemini_model'):
                        list_url = f"https://generativelanguage.googleapis.com/v1beta/models?key={GEMINI_API_KEY}"
                        list_resp = requests.get(list_url)
                        if list_resp.status_code == 200:
                            models_data = list_resp.json().get('models', [])
                            available_models = [m['name'] for m in models_data if 'generateContent' in m.get('supportedGenerationMethods', [])]
                            if available_models:
                                preferred = [
                                    'models/gemini-3.6-flash', 'models/gemini-3.5-flash',
                                    'models/gemini-3.0-flash', 'models/gemini-2.5-flash', 
                                    'models/gemini-1.5-flash'
                                ]
                                selected_model = available_models[0]
                                for p in preferred:
                                    if p in available_models:
                                        selected_model = p
                                        break
                                self._cached_gemini_model = selected_model
                                self.root.after(0, self._append_log, f"[ระบบ] ตรวจพบโมเดลและเลือกใช้: {selected_model}\n\n")
                            else:
                                raise ValueError("API Key นี้ไม่มีโมเดลที่รองรับเลย")
                        else:
                            # ถ้าเช็คโมเดลไม่ได้ ให้เดาใช้รุ่นล่าสุดไปก่อน
                            self._cached_gemini_model = 'models/gemini-3.6-flash'

                    # 2. เตรียมข้อมูลส่งให้ Gemini
                    url = f"https://generativelanguage.googleapis.com/v1beta/{self._cached_gemini_model}:generateContent?key={GEMINI_API_KEY}"
                    headers = {'Content-Type': 'application/json'}
                    prompt = (
                        f"Translate the following text to {target_lang}. "
                        "This is a live meeting transcription. If you see initials or names at the beginning of lines, "
                        "keep them to indicate who is speaking and format it clearly with line breaks. "
                        f"Only provide the translated text:\n\n{text}"
                    )
                    payload = {"contents": [{"parts": [{"text": prompt}]}]}
                    
                    # 3. ระบบ Retry และ Fallback (แก้ปัญหา High Demand)
                    max_retries = 2
                    for attempt in range(max_retries):
                        resp = requests.post(url, json=payload, headers=headers)
                        
                        if resp.status_code == 200:
                            data = resp.json()
                            try:
                                return data['candidates'][0]['content']['parts'][0]['text'].strip()
                            except (KeyError, IndexError):
                                raise RuntimeError(f"โครงสร้างข้อมูลที่ส่งกลับมาผิดปกติ: {data}")
                        
                        error_msg = resp.json().get('error', {}).get('message', resp.text)
                        
                        # ถ้าเซิร์ฟเวอร์เต็ม (High demand) หรือโดนจำกัดโควตา (429 / 503) ให้ลองใหม่
                        if "high demand" in error_msg.lower() or resp.status_code in [429, 503]:
                            if attempt < max_retries - 1:
                                time.sleep(2.0)  # รอ 2 วินาทีแล้วลองส่งใหม่
                                continue
                        
                        # ถ้าวนลูปจนครบแล้วเซิร์ฟเวอร์ยังไม่ว่าง หรือเป็น Error อื่นๆ
                        if hasattr(self, '_cached_gemini_model') and "not found" in error_msg.lower():
                            delattr(self, '_cached_gemini_model') # ลบแคชทิ้งเผื่อชื่อโมเดลผิด
                        
                        # สลับไปใช้ Google Translate (Free) ชั่วคราว เพื่อไม่ให้ซับไตเติลขาดตอน
                        self.root.after(0, self._append_log, f"[Gemini ไม่ว่าง] สลับไปใช้ Google แทนชั่วคราว: {error_msg}\n\n")
                        return GoogleTranslator(source="auto", target=target_lang).translate(text)

                else:
                    # ท่ามาตรฐาน GoogleTranslator (deep-translator)
                    result = GoogleTranslator(source="auto", target=target_lang).translate(text)

            except Exception as e:
                # ระบบสำรอง กรณี Google พังกลางทาง
                if engine == "Google (Free)" and ("too many requests" in str(e).lower() or "429" in str(e)):
                    src = OCR_TO_MYMEMORY_SRC.get(ocr_lang, "en")
                    try:
                        result = MyMemoryTranslator(source=src, target=target_lang).translate(text)
                    except:
                        self._last_translate_ts = time.time()
                        raise RuntimeError("เกินโควตา Google ชั่วคราว แนะนำให้สลับไปใช้ Gemini หรือ DeepL")
                else:
                    raise e

            self._last_translate_ts = time.time()
            return result

    # ---------------- Start / Stop ----------------
    def _start(self):
        if not self.region:
            messagebox.showwarning("ยังไม่ได้เลือกกรอบ", "กรุณาเลือกกรอบ CC ก่อนเริ่มแปล")
            return

        self.running = True
        self.last_text = ""
        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.status_var.set("กำลังทำงาน... กำลังอ่านหน้าจอ")

        self.overlay = CaptionOverlay(self.root)
        self.region_indicator = RegionIndicator(self.root, self.region)

        ocr_lang = OCR_LANGS[self.ocr_lang_var.get()]
        target_lang = TRANSLATE_LANGS[self.target_lang_var.get()]
        interval = self.interval_var.get()

        self.worker_thread = threading.Thread(
            target=self._capture_loop, args=(ocr_lang, target_lang, interval), daemon=True
        )
        self.worker_thread.start()

    def _stop(self):
        self.running = False
        self.start_btn.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.status_var.set("หยุดแล้ว")
        if self.overlay:
            self.overlay.destroy()
            self.overlay = None
        if self.region_indicator:
            self.region_indicator.destroy()
            self.region_indicator = None

    def _on_close(self):
        self.running = False
        self.root.destroy()

    # ---------------- Background worker ----------------
    def _capture_loop(self, ocr_lang, target_lang, interval):
        self._timer_count = 0.0
        with mss.MSS() as sct:
            while self.running:
                # หน่วงเวลาสั้นๆ เพื่อให้ตอบสนองคีย์ลัดได้ไว และใช้นับเวลา
                time.sleep(0.1)
                self._timer_count += 0.1

                mode = self._current_trigger_mode
                should_capture = False

                # ตรวจสอบเงื่อนไขตามโหมดที่เลือก
                if mode == "คีย์ลัดอย่างเดียว":
                    if getattr(self, '_force_capture', False):
                        should_capture = True
                elif mode == "เวลาอย่างเดียว":
                    if self._timer_count >= self.interval_var.get():
                        should_capture = True
                else:  # โหมด "ทั้งคู่ (เวลา + คีย์ลัด)"
                    if getattr(self, '_force_capture', False) or (self._timer_count >= self.interval_var.get()):
                        should_capture = True

                # ถ้ายังไม่ถึงรอบเวลา และไม่ได้กดคีย์ลัด ให้ข้ามไปรอต่อ
                if not should_capture:
                    continue
                    
                # รีเซ็ตตัวนับเวลาและสถานะปุ่มกดเมื่อเริ่มจับภาพ
                self._timer_count = 0.0
                self._force_capture = False

                try:
                    shot = sct.grab(self.region)
                    img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
                    text = pytesseract.image_to_string(img, lang=ocr_lang).strip()
                    text = " ".join(text.split())  # normalize whitespace
                    text = clean_ocr_text(text)  # ตัดขยะจากไอคอน/avatar ที่ OCR อ่านผิด

                    if text and self._is_new_text(text):
                        try:
                            translated = self._safe_translate(text, ocr_lang, target_lang)
                        except Exception as e:
                            translated = f"[แปลไม่สำเร็จ: {e}]"
                        self.ui_queue.put(("caption", text, translated))
                except Exception as e:
                    self.ui_queue.put(("error", str(e), ""))

    def _is_new_text(self, text: str) -> bool:
        # ตัดช่องว่างและเครื่องหมายวรรคตอนออกให้หมดก่อนเปรียบเทียบ
        # เพื่อลดปัญหา OCR อ่านเครื่องหมายผิดๆ ถูกๆ แล้วทำให้เปลืองโควตาแปล
        translator = str.maketrans('', '', string.punctuation)
        clean_new = text.translate(translator).replace(" ", "").lower()
        clean_old = self.last_text.translate(translator).replace(" ", "").lower()
        
        # ถ้าข้อความสั้นมาก ไม่ต้องแปล (กันขยะ)
        if len(clean_new) < 2:
            return False

        ratio = difflib.SequenceMatcher(None, clean_new, clean_old).ratio()
        
        # เพิ่ม Threshold ให้สูงขึ้น (0.85) ถ้าความเหมือนต่ำกว่านี้ถือว่าเป็นข้อความใหม่
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
                    self._append_log(f"CC: {a}\n=> {b}\n\n")
                elif kind == "error":
                    self.status_var.set(f"ข้อผิดพลาด: {a}")
                    self._append_log(f"[ข้อผิดพลาด] {a}\n\n")
        except queue.Empty:
            pass
        self.root.after(150, self._poll_queue)

    def _append_log(self, text):
        self.log_text.config(state="normal")
        self.log_text.insert("end", text)
        self.log_text.see("end")
        self.log_text.config(state="disabled")

    def run(self):
        self.root.mainloop()
        
    # ---------------- Font updating Test api ----------------
    def _test_api(self):
        engine = self.engine_var.get()
        if engine == "Google (Free)":
            messagebox.showinfo("Test API", "Google Free ไม่ต้องใช้ API Key ใช้งานได้เลยครับ")
            return
            
        try:
            self.status_var.set(f"กำลังทดสอบเชื่อมต่อ {engine}...")
            self.root.update()
            # ลองส่งคำง่ายๆ ไปแปล
            res = self._safe_translate("Hello, testing connection.", "eng", "th")
            messagebox.showinfo("API Test Success", f"เชื่อมต่อสำเร็จ!\nผลการแปล: {res}")
            self.status_var.set("พร้อมใช้งาน")
        except Exception as e:
            messagebox.showerror("API Test Error", f"ทดสอบล้มเหลว:\n{str(e)}")
            self.status_var.set("ทดสอบ API ล้มเหลว")

    def _update_font_size(self, *args):
        if self.overlay:
            size = self.font_size_var.get()
            self.overlay.trans_label.config(font=("Tahoma", size, "bold"))
            self.overlay.orig_label.config(font=("Tahoma", max(8, size - 7)))


if __name__ == "__main__":
    App().run()