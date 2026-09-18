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

load_dotenv()

DEEPL_API_KEY = os.getenv("DEEPL_API_KEY", "")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "")

if GEMINI_API_KEY:
    genai.configure(api_key=GEMINI_API_KEY)

OCR_TO_MYMEMORY_SRC = {
    "eng": "en", "tha": "th", "chi_sim": "zh-CN",
    "jpn": "ja", "kor": "ko", "vie": "vi",
}

_MIN_TRANSLATE_GAP = 1.2

if sys.platform == "win32":
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

TESSERACT_CMD = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
if TESSERACT_CMD:
    pytesseract.pytesseract.tesseract_cmd = TESSERACT_CMD

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

_OCR_NOISE_RE = re.compile(r'(?:^|(?<=\s))[@®©™†‡•●○◦§¶|_~]+(?:(?=\s)|$)')

def clean_ocr_text(text: str) -> str:
    cleaned = _OCR_NOISE_RE.sub(" ", text)
    cleaned = re.sub(r"\s{2,}", " ", cleaned).strip()
    return cleaned


class RegionSelector(tk.Toplevel):
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
            fg="white", bg="black", font=("Segoe UI", 14, "bold"),
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
            outline="#00a8ff", width=2
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
                inner_bg = "#1e1e1e"
                try:
                    self.attributes("-alpha", 0.2)
                except tk.TclError:
                    pass
            inner = tk.Frame(
                self, bg=inner_bg, highlightbackground="#00a8ff",
                highlightcolor="#00a8ff", highlightthickness=border
            )
            inner.pack(fill="both", expand=True)
        else:
            try:
                self.attributes("-alpha", 0.25)
            except tk.TclError:
                pass
            self.configure(bg="#00a8ff")
            inner = tk.Frame(self, bg="#1e1e1e")
            inner.pack(fill="both", expand=True, padx=border, pady=border)


class CaptionOverlay(tk.Toplevel):
    MIN_W, MIN_H = 240, 80

    def __init__(self, master):
        super().__init__(master)
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.90) # ปรับให้โปร่งแสงนิดหน่อยดูคลีนขึ้น
        except tk.TclError:
            pass
        self.configure(bg="#1c1c1c") # ใช้สีเทาเข้มแทนสีดำสนิท

        self._drag_offset = (0, 0)
        self._resizing = False
        self._resize_start = (0, 0, 0, 0)

        self.orig_var = tk.StringVar(value="")
        self.trans_var = tk.StringVar(value="รอข้อความ CC...")

        # ถอดแถบ drag_bar ออก เพื่อความ Minimal แล้วจับ drag ที่ตัว body แทน
        body = tk.Frame(self, bg="#1c1c1c")
        body.pack(fill="both", expand=True, padx=10, pady=10)

        self.orig_label = tk.Label(
            body, textvariable=self.orig_var, fg="#a0a0a0", bg="#1c1c1c",
            font=("Segoe UI", 11), wraplength=760, justify="center", cursor="fleur"
        )
        self.orig_label.pack(fill="x", pady=(0, 4))

        self.trans_label = tk.Label(
            body, textvariable=self.trans_var, fg="#ffffff", bg="#1c1c1c",
            font=("Segoe UI", 18, "bold"), wraplength=760, justify="center", cursor="fleur"
        )
        self.trans_label.pack(fill="x")

        # ผูก event ลากหน้าต่างเข้ากับตัวพื้นหลังและข้อความได้เลย
        for widget in (self, body, self.orig_label, self.trans_label):
            widget.bind("<ButtonPress-1>", self._start_move)
            widget.bind("<B1-Motion>", self._on_move)

        self.grip = tk.Label(self, text="◢", fg="#555", bg="#1c1c1c", cursor="size_nw_se")
        self.grip.place(relx=1.0, rely=1.0, anchor="se")
        self.grip.bind("<ButtonPress-1>", self._start_resize)
        self.grip.bind("<B1-Motion>", self._on_resize)

        self.update_idletasks()
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        w = 760
        h = self.winfo_reqheight() + 20
        x = (screen_w - w) // 2
        y = screen_h - h - 80
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

    def show_text(self, original: str, translated: str):
        self.orig_var.set(original)
        self.trans_var.set(translated)


class App:
    def _trigger_force_capture(self):
        if self.running:
            self._force_capture = True
    
    def _start_record_hotkey(self):
        self.record_btn.config(text="กำลังรอ... (กดปุ่มบนคีย์บอร์ด)", state="disabled")
        self.hotkey_var.set("...")
        threading.Thread(target=self._record_hotkey_thread, daemon=True).start()

    def _record_hotkey_thread(self):
        try:
            new_hotkey = keyboard.read_hotkey(suppress=False)
            self.root.after(0, self._apply_recorded_hotkey, new_hotkey)
        except Exception:
            self.root.after(0, self._apply_recorded_hotkey, self.current_bound_hotkey)

    def _apply_recorded_hotkey(self, new_hotkey):
        self.record_btn.config(text="เปลี่ยนคีย์ลัด", state="normal")
        try:
            if self.current_bound_hotkey:
                keyboard.remove_hotkey(self.current_bound_hotkey)
            keyboard.add_hotkey(new_hotkey, self._trigger_force_capture)
            self.current_bound_hotkey = new_hotkey
            self.hotkey_var.set(new_hotkey)
        except Exception as e:
            messagebox.showerror("ข้อผิดพลาด", f"ปุ่มนี้ไม่สามารถใช้เป็นคีย์ลัดได้\n\n{e}")
            self.hotkey_var.set(self.current_bound_hotkey)
            keyboard.add_hotkey(self.current_bound_hotkey, self._trigger_force_capture)
            
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("CC Realtime Translator")
        self.root.geometry("580x760") 
        self.root.resizable(True, True)
        self.root.minsize(500, 700)

        # ธีม Windows 11
        sv_ttk.set_theme("dark")

        self.region = None
        self.running = False
        
        self._force_capture = False
        self._current_trigger_mode = "ทั้งคู่ (เวลา + คีย์ลัด)"
        self.current_bound_hotkey = "ctrl+shift+t"
        try:
            keyboard.add_hotkey(self.current_bound_hotkey, self._trigger_force_capture)
        except Exception:
            pass

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

    # ---------------- UI (ดีไซน์ใหม่แบบ Minimal) ----------------
    def _build_ui(self):
        # ฟอนต์มาตรฐาน
        ui_font = ("Segoe UI", 10)
        h_font = ("Segoe UI", 11, "bold")
        accent_color = "#4db8ff" # สีฟ้าน้ำทะเลเข้ากับ Dark mode

        # Container หลัก เพิ่ม Padding กว้างๆ ให้ดูไม่อึดอัด
        main_container = ttk.Frame(self.root, padding="24 24 24 24")
        main_container.pack(fill="both", expand=True)

        # --- Section 1: การตั้งค่าพื้นฐาน ---
        ttk.Label(main_container, text="ตั้งค่าหน้าจอและภาษา", font=h_font, foreground=accent_color).pack(anchor="w", pady=(0, 12))
        
        frm_basic = ttk.Frame(main_container)
        frm_basic.pack(fill="x", pady=(0, 20))
        frm_basic.columnconfigure(1, weight=1)

        # แถว 1: กรอบหน้าจอ
        ttk.Label(frm_basic, text="กรอบ CC:", font=ui_font).grid(row=0, column=0, sticky="w", pady=8, padx=(0, 10))
        self.region_label = ttk.Label(frm_basic, text="ยังไม่ได้กำหนดพื้นที่", font=ui_font, foreground="#888")
        self.region_label.grid(row=0, column=1, sticky="w", pady=8)
        
        btn_box = ttk.Frame(frm_basic)
        btn_box.grid(row=0, column=2, sticky="e")
        ttk.Button(btn_box, text="เลือกกรอบ", command=self._select_region).pack(side="left", padx=(0, 5))
        ttk.Button(btn_box, text="ทดสอบอ่าน", command=self._test_ocr).pack(side="left")

        # แถว 2: ภาษาต้นฉบับ
        ttk.Label(frm_basic, text="ภาษาของวิดีโอ:", font=ui_font).grid(row=1, column=0, sticky="w", pady=8)
        self.ocr_lang_var = tk.StringVar(value="อังกฤษ (English)")
        ttk.Combobox(
            frm_basic, textvariable=self.ocr_lang_var, values=list(OCR_LANGS.keys()), 
            state="readonly", width=25, font=ui_font
        ).grid(row=1, column=1, columnspan=2, sticky="we", pady=8)

        # แถว 3: แปลเป็นภาษา
        ttk.Label(frm_basic, text="แปลเป็นภาษา:", font=ui_font).grid(row=2, column=0, sticky="w", pady=8)
        self.target_lang_var = tk.StringVar(value="ไทย")
        ttk.Combobox(
            frm_basic, textvariable=self.target_lang_var, values=list(TRANSLATE_LANGS.keys()), 
            state="readonly", width=25, font=ui_font
        ).grid(row=2, column=1, columnspan=2, sticky="we", pady=8)

        # แถว 4: ระบบแปล
        ttk.Label(frm_basic, text="ระบบแปล (Engine):", font=ui_font).grid(row=3, column=0, sticky="w", pady=8)
        engine_box = ttk.Frame(frm_basic)
        engine_box.grid(row=3, column=1, columnspan=2, sticky="we", pady=8)
        engine_box.columnconfigure(0, weight=1)
        
        self.engine_var = tk.StringVar(value="Google (Free)")
        ttk.Combobox(
            engine_box, textvariable=self.engine_var, values=["Google (Free)", "DeepL", "Gemini"], 
            state="readonly", font=ui_font
        ).grid(row=0, column=0, sticky="we", padx=(0, 10))
        ttk.Button(engine_box, text="ทดสอบ API", command=self._test_api).grid(row=0, column=1)

        ttk.Separator(main_container, orient="horizontal").pack(fill="x", pady=(0, 20))

        # --- Section 2: การควบคุมและการแสดงผล ---
        ttk.Label(main_container, text="การทำงานและการแสดงผล", font=h_font, foreground=accent_color).pack(anchor="w", pady=(0, 12))
        
        frm_adv = ttk.Frame(main_container)
        frm_adv.pack(fill="x", pady=(0, 24))
        frm_adv.columnconfigure(1, weight=1)

        # แถว 1: โหมด
        ttk.Label(frm_adv, text="รูปแบบคำสั่ง:", font=ui_font).grid(row=0, column=0, sticky="w", pady=8, padx=(0, 10))
        self.trigger_mode_var = tk.StringVar(value="ทั้งคู่ (เวลา + คีย์ลัด)")
        ttk.Combobox(
            frm_adv, textvariable=self.trigger_mode_var,
            values=["เวลาอย่างเดียว", "คีย์ลัดอย่างเดียว", "ทั้งคู่ (เวลา + คีย์ลัด)"],
            state="readonly", font=ui_font
        ).grid(row=0, column=1, sticky="we", pady=8)
        self.trigger_mode_var.trace_add("write", lambda *_: setattr(self, '_current_trigger_mode', self.trigger_mode_var.get()))

        # แถว 2: คีย์ลัด
        ttk.Label(frm_adv, text="คีย์ลัดฉุกเฉิน:", font=ui_font).grid(row=1, column=0, sticky="w", pady=8)
        hk_box = ttk.Frame(frm_adv)
        hk_box.grid(row=1, column=1, sticky="we", pady=8)
        
        self.hotkey_var = tk.StringVar(value=self.current_bound_hotkey)
        self.hotkey_lbl = ttk.Label(hk_box, textvariable=self.hotkey_var, font=("Segoe UI", 10, "bold"), foreground=accent_color)
        self.hotkey_lbl.pack(side="left", padx=(0, 15))
        self.record_btn = ttk.Button(hk_box, text="เปลี่ยนคีย์ลัด", command=self._start_record_hotkey)
        self.record_btn.pack(side="left")

        # แถว 3: ความถี่
        ttk.Label(frm_adv, text="ความเร็วในการอ่าน:", font=ui_font).grid(row=2, column=0, sticky="w", pady=12)
        spd_box = ttk.Frame(frm_adv)
        spd_box.grid(row=2, column=1, sticky="we", pady=12)
        spd_box.columnconfigure(0, weight=1)
        
        self.interval_var = tk.DoubleVar(value=3.0)
        ttk.Scale(spd_box, from_=0.5, to=4.0, variable=self.interval_var, orient="horizontal").grid(row=0, column=0, sticky="we", padx=(0, 15))
        self.interval_display = ttk.Label(spd_box, text="ทุก 3.0 วิ", font=ui_font)
        self.interval_display.grid(row=0, column=1, sticky="e")
        self.interval_var.trace_add("write", lambda *_: self.interval_display.config(text=f"ทุก {self.interval_var.get():.1f} วิ"))

        # แถว 4: ฟอนต์
        ttk.Label(frm_adv, text="ขนาดตัวอักษร:", font=ui_font).grid(row=3, column=0, sticky="w", pady=12)
        self.font_size_var = tk.IntVar(value=18)
        ttk.Scale(
            frm_adv, from_=10, to=40, variable=self.font_size_var, orient="horizontal", command=self._update_font_size
        ).grid(row=3, column=1, sticky="we", pady=12)

        # --- Section 3: Action Buttons ---
        frm_ctrl = ttk.Frame(main_container)
        frm_ctrl.pack(fill="x", pady=(0, 20))
        
        # ใช้ปุ่มใหญ่เต็มพื้นที่
        self.start_btn = ttk.Button(frm_ctrl, text="▶ เริ่มทำงาน (Start)", command=self._start, style="Accent.TButton")
        self.start_btn.pack(side="left", expand=True, fill="x", padx=(0, 5), ipady=5)
        self.stop_btn = ttk.Button(frm_ctrl, text="■ หยุด (Stop)", command=self._stop, state="disabled")
        self.stop_btn.pack(side="left", expand=True, fill="x", padx=(5, 0), ipady=5)

        # --- Section 4: Logs & Status ---
        self.log_text = tk.Text(
            main_container, height=5, wrap="word", state="disabled", 
            font=("Consolas", 9), bg="#1e1e1e", fg="#aaa", relief="flat", padx=10, pady=10
        )
        self.log_text.pack(fill="both", expand=True, pady=(0, 10))

        # Status Bar ด้านล่างสุด
        status_bar = ttk.Frame(main_container)
        status_bar.pack(fill="x")
        self.status_var = tk.StringVar(value="พร้อมใช้งาน")
        ttk.Label(status_bar, textvariable=self.status_var, font=("Segoe UI", 9, "bold"), foreground=accent_color).pack(side="left")

    # ---------------- Region selection ----------------
    def _select_region(self):
        self.root.withdraw()
        self.root.after(200, self._open_selector)

    def _open_selector(self):
        def done(region):
            self.region = region
            self.region_label.config(text=f"{region['width']}x{region['height']} px  @ ({region['left']}, {region['top']})", foreground="#ffffff")
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
                    "OCR ไม่พบข้อความในกรอบนี้เลย\n\nสาเหตุที่พบบ่อย:\n- กรอบไม่ได้ครอบตัวอักษร CC จริงๆ\n- ตอนทดสอบยังไม่มีคำบรรยายขึ้นบนจอ"
                )
                return
            translated = self._safe_translate(text, ocr_lang, target_lang)
            messagebox.showinfo("ผลทดสอบ", f"ข้อความที่ OCR อ่านได้:\n{text}\n\nคำแปล:\n{translated}")
        except pytesseract.pytesseract.TesseractNotFoundError:
            messagebox.showerror(
                "ไม่พบ Tesseract OCR",
                "ยังไม่ได้ติดตั้ง Tesseract OCR หรือตั้งค่า Path ไม่ถูกต้อง"
            )
        except Exception as e:
            messagebox.showerror("เกิดข้อผิดพลาด", str(e))

    # ---------------- แปลแบบมีตัวจำกัดความถี่ + ตัวสำรองถ้าโดน rate limit ----------------
    def _safe_translate(self, text: str, ocr_lang: str, target_lang: str) -> str:
        engine = self.engine_var.get()
        
        with self._translate_lock:
            if engine == "Google (Free)":
                wait = _MIN_TRANSLATE_GAP - (time.time() - self._last_translate_ts)
                if wait > 0:
                    time.sleep(wait)

            try:
                if engine == "DeepL":
                    if not DEEPL_API_KEY:
                        raise ValueError("ยังไม่ได้ใส่ DEEPL_API_KEY ในโค้ด")
                    url = "https://api-free.deepl.com/v2/translate" if ":fx" in DEEPL_API_KEY else "https://api.deepl.com/v2/translate"
                    target = "EN-US" if target_lang == "en" else target_lang.upper()
                    payload = {"text": [text], "target_lang": target}
                    headers = {"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}", "Content-Type": "application/json"}
                    
                    resp = requests.post(url, json=payload, headers=headers)
                    resp.raise_for_status()
                    result = resp.json()["translations"][0]["text"]

                elif engine == "Gemini":
                    if not GEMINI_API_KEY:
                        raise ValueError("ยังไม่ได้ใส่ GEMINI_API_KEY")
                    
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
                                self.root.after(0, self._append_log, f"[ระบบ] ตรวจพบโมเดล: {selected_model}\n\n")
                            else:
                                raise ValueError("API Key นี้ไม่มีโมเดลที่รองรับเลย")
                        else:
                            self._cached_gemini_model = 'models/gemini-3.6-flash'

                    url = f"https://generativelanguage.googleapis.com/v1beta/{self._cached_gemini_model}:generateContent?key={GEMINI_API_KEY}"
                    headers = {'Content-Type': 'application/json'}
                    prompt = (
                        f"Translate the following text to {target_lang}. "
                        "This is a live meeting transcription. If you see initials or names at the beginning of lines, "
                        "keep them to indicate who is speaking and format it clearly with line breaks. "
                        f"Only provide the translated text:\n\n{text}"
                    )
                    payload = {"contents": [{"parts": [{"text": prompt}]}]}
                    
                    max_retries = 2
                    for attempt in range(max_retries):
                        resp = requests.post(url, json=payload, headers=headers)
                        if resp.status_code == 200:
                            data = resp.json()
                            try:
                                return data['candidates'][0]['content']['parts'][0]['text'].strip()
                            except (KeyError, IndexError):
                                raise RuntimeError(f"ข้อมูลส่งกลับผิดปกติ: {data}")
                        
                        error_msg = resp.json().get('error', {}).get('message', resp.text)
                        
                        if "high demand" in error_msg.lower() or resp.status_code in [429, 503]:
                            if attempt < max_retries - 1:
                                time.sleep(2.0)
                                continue
                        
                        if hasattr(self, '_cached_gemini_model') and "not found" in error_msg.lower():
                            delattr(self, '_cached_gemini_model')
                        
                        self.root.after(0, self._append_log, f"[Gemini ไม่ว่าง] สลับใช้ Google แปลชั่วคราว\n")
                        return GoogleTranslator(source="auto", target=target_lang).translate(text)
                else:
                    result = GoogleTranslator(source="auto", target=target_lang).translate(text)

            except Exception as e:
                if engine == "Google (Free)" and ("too many requests" in str(e).lower() or "429" in str(e)):
                    src = OCR_TO_MYMEMORY_SRC.get(ocr_lang, "en")
                    try:
                        result = MyMemoryTranslator(source=src, target=target_lang).translate(text)
                    except:
                        self._last_translate_ts = time.time()
                        raise RuntimeError("เกินโควตา แนะนำให้สลับไปใช้ Gemini/DeepL")
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
        self.status_var.set("กำลังทำงาน...")

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
        self.status_var.set("หยุดทำงาน")
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
                time.sleep(0.1)
                self._timer_count += 0.1

                mode = self._current_trigger_mode
                should_capture = False

                if mode == "คีย์ลัดอย่างเดียว":
                    if getattr(self, '_force_capture', False):
                        should_capture = True
                elif mode == "เวลาอย่างเดียว":
                    if self._timer_count >= self.interval_var.get():
                        should_capture = True
                else: 
                    if getattr(self, '_force_capture', False) or (self._timer_count >= self.interval_var.get()):
                        should_capture = True

                if not should_capture:
                    continue
                    
                self._timer_count = 0.0
                self._force_capture = False

                try:
                    shot = sct.grab(self.region)
                    img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
                    text = pytesseract.image_to_string(img, lang=ocr_lang).strip()
                    text = " ".join(text.split()) 
                    text = clean_ocr_text(text) 

                    if text and self._is_new_text(text):
                        try:
                            translated = self._safe_translate(text, ocr_lang, target_lang)
                        except Exception as e:
                            translated = f"[แปลไม่สำเร็จ: {e}]"
                        self.ui_queue.put(("caption", text, translated))
                except Exception as e:
                    self.ui_queue.put(("error", str(e), ""))

    def _is_new_text(self, text: str) -> bool:
        translator = str.maketrans('', '', string.punctuation)
        clean_new = text.translate(translator).replace(" ", "").lower()
        clean_old = self.last_text.translate(translator).replace(" ", "").lower()
        
        if len(clean_new) < 2:
            return False
        ratio = difflib.SequenceMatcher(None, clean_new, clean_old).ratio()
        if ratio < 0.85:
            self.last_text = text
            return True
        return False

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
                    self._append_log(f"[Error] {a}\n\n")
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
        
    def _test_api(self):
        engine = self.engine_var.get()
        if engine == "Google (Free)":
            messagebox.showinfo("Test API", "Google Free ไม่ต้องใช้ API Key ใช้งานได้เลยครับ")
            return
            
        try:
            self.status_var.set(f"กำลังทดสอบเชื่อมต่อ {engine}...")
            self.root.update()
            res = self._safe_translate("Hello, testing connection.", "eng", "th")
            messagebox.showinfo("API Test Success", f"เชื่อมต่อสำเร็จ!\nผลการแปล: {res}")
            self.status_var.set("เชื่อมต่อ API สำเร็จ")
        except Exception as e:
            messagebox.showerror("API Test Error", f"ทดสอบล้มเหลว:\n{str(e)}")
            self.status_var.set("ทดสอบ API ล้มเหลว")

    def _update_font_size(self, *args):
        if self.overlay:
            size = self.font_size_var.get()
            self.overlay.trans_label.config(font=("Segoe UI", size, "bold"))
            self.overlay.orig_label.config(font=("Segoe UI", max(8, size - 7)))

if __name__ == "__main__":
    App().run()