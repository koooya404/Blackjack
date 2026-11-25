"""ブラックジャック(Streamlit版・1ファイル)。スマホ・タブレット向けに、すべてボタン操作で遊べる。

親(ディーラー)はコンピューター、子はCPU3人+あなた。チップ付き、ユーザー登録つき。

■ 遊び方
  - 初回は「新規登録」。ユーザー名は登録順に 0001〜9999 が自動で付き、パスワードは任意の4桁の数字
  - ベットはチップボタンで決めて「ディール」。操作はヒット / スタンド / ダブル
  - ブラックジャックは 3:2、通常勝ちは 1:1、引き分けはベット返却。ディーラーは17以上でスタンド
  - チップはラウンドごとに自動保存(CPUのチップは保存されません)

■ 起動
  pip install -r requirements.txt
  streamlit run app.py
  同じWi-Fi上のスマホからは、起動時に表示される Network URL を開く。

■ Streamlit Community Cloud で公開
  GitHubにプッシュ → https://share.streamlit.io で「New app」→ このリポジトリの app.py を選ぶ。

■ ユーザーデータの保存について(重要)
  ユーザー情報は data/users.json に保存する(場所は環境変数 BJ_DB_PATH で変更可)。
  Community Cloud はディスクが永続しないため、再起動・再デプロイ・一定期間の停止でユーザーとチップが消える。
  長く使うなら「ユーザー管理」節の _load / _save を外部DB(Supabase、Google Sheets 等)に差し替えること。
  自分のPCやVPSで動かす分にはそのままでよい。

■ セキュリティ
  パスワードは4桁(1万通り)なので、データファイルを読める人には破られる。ソルト付きハッシュ化と
  ログイン失敗のロック(5回で10分)は入れているが、チップに価値のない遊び用途が前提。

■ 構成(このファイルの中身)
  1. ゲームロジック  2. ユーザー管理  3. 画面(Streamlit)
  ※ Streamlit は操作のたびにこのファイル全体を実行し直す。クラスは毎回「別物」になり、モジュール変数も
    作り直されるので、(a) エラーの判定は型でなく名前で行う (b) ロックは st.cache_resource で1つに保つ。
"""
from __future__ import annotations

import hashlib
import hmac
import inspect
import json
import os
import random
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime

import streamlit as st

# ================================================================ 1. ゲームロジック
SUITS = ["♠", "♥", "♦", "♣"]
RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]

NUM_DECKS = 6
START_CHIPS = 1000
MIN_BET = 10
CPU_NAMES = ["CPU-1", "CPU-2", "CPU-3"]
DEALER_STAND = 17  # ソフト17でもスタンド


class GameError(Exception):
    """不正な操作(ベット額が範囲外、今は操作できない、など)"""


@dataclass(frozen=True)
class Card:
    rank: str
    suit: str

    @property
    def value(self) -> int:
        if self.rank == "A":
            return 11
        if self.rank in ("J", "Q", "K"):
            return 10
        return int(self.rank)

    @property
    def is_red(self) -> bool:
        return self.suit in ("♥", "♦")

    def __str__(self) -> str:
        return f"{self.suit}{self.rank}"


class Shoe:
    def __init__(self, num_decks: int = NUM_DECKS):
        self.num_decks = num_decks
        self.cards: list[Card] = []
        self.shuffle()

    def shuffle(self) -> None:
        self.cards = [Card(r, s) for _ in range(self.num_decks) for s in SUITS for r in RANKS]
        random.shuffle(self.cards)

    def needs_shuffle(self) -> bool:
        return len(self.cards) < 52 * self.num_decks * 0.25

    def draw(self) -> Card:
        if not self.cards:
            self.shuffle()
        return self.cards.pop()


def hand_value(cards: list[Card]) -> tuple[int, bool]:
    """(合計, ソフトハンドか)。Aは必要に応じて11→1に下げる。"""
    total = sum(c.value for c in cards)
    aces = sum(1 for c in cards if c.rank == "A")
    while total > 21 and aces:
        total -= 10
        aces -= 1
    return total, aces > 0


def cpu_decide(cards: list[Card], upcard: Card, can_double: bool) -> str:
    """ベーシックストラテジー(スプリット無し版)。'h' / 's' / 'd' を返す。"""
    total, soft = hand_value(cards)
    up = upcard.value  # Aは11

    def dbl(fallback: str) -> str:
        return "d" if can_double else fallback

    if soft:
        if total >= 19:
            return "s"
        if total == 18:
            if up <= 6:
                return dbl("s")
            return "s" if up in (7, 8) else "h"
        if total in (15, 16, 17):
            return dbl("h") if 4 <= up <= 6 else "h"
        return dbl("h") if 5 <= up <= 6 else "h"  # ソフト13-14

    if total >= 17:
        return "s"
    if 13 <= total <= 16:
        return "s" if up <= 6 else "h"
    if total == 12:
        return "s" if 4 <= up <= 6 else "h"
    if total == 11:
        return dbl("h")
    if total == 10:
        return dbl("h") if up <= 9 else "h"
    if total == 9:
        return dbl("h") if 3 <= up <= 6 else "h"
    return "h"


def cpu_bet(chips: int) -> int:
    """チップの2〜10%程度をランダムに賭ける(MIN_BET単位)。"""
    low = max(MIN_BET, chips // 50)
    high = max(low, chips // 10)
    bet = random.randint(low, high) // MIN_BET * MIN_BET
    return max(MIN_BET, min(bet, chips))


@dataclass
class Seat:
    name: str
    chips: int
    is_human: bool = False
    cards: list[Card] = field(default_factory=list)
    bet: int = 0
    doubled: bool = False
    outcome: str = ""  # "blackjack" / "win" / "push" / "lose" / "bust"(結果確定後)
    net: int = 0       # このラウンドの損益(負けは -bet)

    def reset(self) -> None:
        self.cards = []
        self.bet = 0
        self.doubled = False
        self.outcome = ""
        self.net = 0

    @property
    def total(self) -> int:
        return hand_value(self.cards)[0]

    @property
    def soft(self) -> bool:
        return hand_value(self.cards)[1]

    @property
    def is_blackjack(self) -> bool:
        return len(self.cards) == 2 and self.total == 21

    @property
    def is_bust(self) -> bool:
        return self.total > 21


class Game:
    """phase: "betting" → "playing" → "result" → (new_round) → "betting" ...
    席の順番は CPU-1, CPU-2, CPU-3, あなた(最後)。CPUは deal() の中で自動的にプレイを終える。"""

    def __init__(self, human_name: str, human_chips: int):
        self.shoe = Shoe()
        self.human = Seat(human_name, human_chips, is_human=True)
        self.cpus = [Seat(n, START_CHIPS) for n in CPU_NAMES]
        self.dealer_cards: list[Card] = []
        self.dealer_bj = False
        self.phase = "betting"
        self.round_no = 0
        self.events: list[str] = []  # 画面に出す一言(シャッフル、CPU補充など)

    # ---- 参照用
    @property
    def seats(self) -> list[Seat]:
        return self.cpus + [self.human]

    @property
    def dealer_up(self) -> Card:
        return self.dealer_cards[0]

    @property
    def dealer_total(self) -> int:
        return hand_value(self.dealer_cards)[0]

    @property
    def dealer_bust(self) -> bool:
        return self.dealer_total > 21

    @property
    def can_double(self) -> bool:
        h = self.human
        return self.phase == "playing" and len(h.cards) == 2 and h.chips >= h.bet

    # ---- ラウンド進行
    def new_round(self) -> None:
        """結果画面からベット画面へ戻す。"""
        self.phase = "betting"
        for s in self.seats:
            s.reset()
        self.dealer_cards = []
        self.dealer_bj = False
        self.events = []

    def deal(self, bet: int) -> None:
        if self.phase != "betting":
            raise GameError("今はベットできません。")
        if not (MIN_BET <= bet <= self.human.chips):
            raise GameError(f"ベットは {MIN_BET}〜{self.human.chips} で指定してください。")

        self.round_no += 1
        self.events = []
        if self.shoe.needs_shuffle():
            self.shoe.shuffle()
            self.events.append("シューをシャッフルしました")

        for s in self.cpus:
            if s.chips < MIN_BET:  # 破産したCPUは新しい持ち金で再参加
                s.chips = START_CHIPS
                self.events.append(f"{s.name} がチップを補充しました")
            s.bet = cpu_bet(s.chips)
            s.chips -= s.bet
        self.human.bet = bet
        self.human.chips -= bet

        for _ in range(2):
            for s in self.seats:
                s.cards.append(self.shoe.draw())
            self.dealer_cards.append(self.shoe.draw())

        # ディーラーがA/10点札を見せているときは、先にブラックジャックを確認(ピーク)
        self.dealer_bj = self.dealer_up.value in (10, 11) and self.dealer_total == 21
        if self.dealer_bj:
            self._finish()
            return

        for s in self.cpus:
            self._cpu_turn(s)
        self.phase = "playing"
        if self.human.is_blackjack:
            self._finish()

    def hit(self) -> None:
        self._require_playing()
        self.human.cards.append(self.shoe.draw())
        if self.human.total >= 21:  # バースト or 21で自動スタンド
            self._finish()

    def stand(self) -> None:
        self._require_playing()
        self._finish()

    def double(self) -> None:
        self._require_playing()
        if not self.can_double:
            raise GameError("ダブルダウンできません。")
        h = self.human
        h.chips -= h.bet
        h.bet *= 2
        h.doubled = True
        h.cards.append(self.shoe.draw())
        self._finish()

    # ---- 内部処理
    def _require_playing(self) -> None:
        if self.phase != "playing":
            raise GameError("今は操作できません。")

    def _cpu_turn(self, s: Seat) -> None:
        while not s.is_bust and s.total < 21:
            can_double = len(s.cards) == 2 and s.chips >= s.bet
            action = cpu_decide(s.cards, self.dealer_up, can_double)
            if action == "s":
                break
            if action == "d":
                s.chips -= s.bet
                s.bet *= 2
                s.doubled = True
                s.cards.append(self.shoe.draw())
                break
            s.cards.append(self.shoe.draw())

    def _finish(self) -> None:
        live = any(not s.is_bust and not s.is_blackjack for s in self.seats)
        if not self.dealer_bj and live:
            while self.dealer_total < DEALER_STAND:
                self.dealer_cards.append(self.shoe.draw())
        for s in self.seats:
            self._settle(s)
        self.phase = "result"

    def _settle(self, s: Seat) -> None:
        """損益を確定してチップに反映する(ベットは配札時に引き落とし済み)。"""
        if s.is_blackjack:
            if self.dealer_bj:
                s.outcome, s.net = "push", 0
            else:
                s.outcome, s.net = "blackjack", s.bet * 3 // 2
        elif s.is_bust:
            s.outcome, s.net = "bust", -s.bet
        elif self.dealer_bj:
            s.outcome, s.net = "lose", -s.bet
        elif self.dealer_bust or s.total > self.dealer_total:
            s.outcome, s.net = "win", s.bet
        elif s.total == self.dealer_total:
            s.outcome, s.net = "push", 0
        else:
            s.outcome, s.net = "lose", -s.bet
        s.chips += s.bet + s.net


# ================================================================ 2. ユーザー管理
DB_PATH = os.environ.get("BJ_DB_PATH") or os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "data", "users.json"
)
MAX_USERS = 9999
MAX_FAILS = 5
LOCK_SECONDS = 600
PBKDF2_ROUNDS = 100_000
BAD_LOGIN = "ユーザー名またはパスワードが違います。"


class UserStoreError(Exception):
    pass


@st.cache_resource
def _get_lock():
    """全セッション共通のロック(再実行のたびに作り直されないよう cache_resource で保持)。"""
    return threading.RLock()


def _load() -> dict:
    try:
        with open(DB_PATH, encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return {"users": {}}


def _save(db: dict) -> None:
    os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
    tmp = DB_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(db, f, ensure_ascii=False, indent=2)
    os.replace(tmp, DB_PATH)  # 書き込み途中で壊れないよう置き換え


def _hash_pw(pw: str, salt_hex: str) -> str:
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt_hex), PBKDF2_ROUNDS).hex()


def valid_pin(pw: str) -> bool:
    return len(pw) == 4 and pw.isascii() and pw.isdigit()


def normalize_id(raw: str) -> str:
    """'1' → '0001'。数字以外はそのまま返す(存在しないIDとして扱われる)。"""
    raw = (raw or "").strip()
    return raw.zfill(4) if raw.isascii() and raw.isdigit() else raw


def register(pw: str) -> str:
    """新規登録して、割り当てたユーザー名(例 '0001')を返す。"""
    if not valid_pin(pw):
        raise UserStoreError("パスワードは4桁の数字です。")
    with _get_lock():
        db = _load()
        next_id = max((int(k) for k in db["users"]), default=0) + 1
        if next_id > MAX_USERS:
            raise UserStoreError("登録人数の上限(9999人)に達しています。")
        uid = f"{next_id:04d}"
        salt = os.urandom(16).hex()
        db["users"][uid] = {
            "salt": salt,
            "hash": _hash_pw(pw, salt),
            "chips": START_CHIPS,
            "created": datetime.now().isoformat(timespec="seconds"),
        }
        _save(db)
        return uid


def authenticate(raw_id: str, pw: str) -> tuple[bool, str]:
    """(成功か, 失敗時のメッセージ)。"""
    uid = normalize_id(raw_id)
    with _get_lock():
        db = _load()
        user = db["users"].get(uid)
        if user is None:
            _hash_pw(pw, "00" * 16)  # 存在有無で応答時間が変わらないように
            return False, BAD_LOGIN

        now = time.time()
        if user.get("locked_until", 0) > now:
            minutes = int((user["locked_until"] - now) // 60) + 1
            return False, f"試行回数が多すぎます。約{minutes}分後にもう一度お試しください。"

        if hmac.compare_digest(_hash_pw(pw, user["salt"]), user["hash"]):
            if user.get("fails") or user.get("locked_until"):
                user["fails"], user["locked_until"] = 0, 0
                _save(db)
            return True, ""

        user["fails"] = user.get("fails", 0) + 1
        if user["fails"] >= MAX_FAILS:
            user["fails"] = 0
            user["locked_until"] = now + LOCK_SECONDS
        _save(db)
        return False, BAD_LOGIN


def get_chips(uid: str) -> int:
    with _get_lock():
        return int(_load()["users"][uid]["chips"])


def set_chips(uid: str, chips: int) -> None:
    with _get_lock():
        db = _load()
        db["users"][uid]["chips"] = int(chips)
        _save(db)


# ================================================================ 3. 画面(Streamlit)
def _wide(fn) -> dict:
    """ボタンを横幅いっぱいにする引数(Streamlitのバージョン差を吸収)。"""
    return {"width": "stretch"} if "width" in inspect.signature(fn).parameters else {"use_container_width": True}


WIDE = _wide(st.button)
WIDE_FORM = _wide(st.form_submit_button)

# HTMLブロックの途中に空行やインデントを入れない(Markdownに解釈されるため)
CSS = """<style>
.block-container{max-width:600px;padding:1rem .8rem 3rem}
footer{visibility:hidden}
.hdr{display:flex;justify-content:space-between;align-items:center;font-weight:700;margin-bottom:.4rem}
.hdr .bal{background:rgba(0,0,0,.3);border-radius:2rem;padding:.15rem .8rem;color:#ffd54f}
.nm{display:flex;justify-content:space-between;font-size:.78rem;opacity:.85;margin-bottom:.2rem}
.tot{font-size:.85rem;font-weight:700;min-height:1.3rem;margin-top:.1rem}
.dealer,.me{background:rgba(0,0,0,.22);border-radius:.8rem;padding:.5rem .7rem;margin-bottom:.5rem}
.me{border:2px solid rgba(255,213,79,.55)}
.cpus{display:grid;grid-template-columns:repeat(3,1fr);gap:.4rem;margin-bottom:.5rem}
.seat{background:rgba(0,0,0,.22);border-radius:.7rem;padding:.35rem .4rem;min-width:0}
.seat .bet{font-size:.7rem;opacity:.8}
.hand{display:flex;flex-wrap:wrap}
.ph{opacity:.5;font-size:.8rem}
.card{display:inline-flex;flex-direction:column;align-items:center;justify-content:center;background:#fff;color:#111;border-radius:.45rem;border:1px solid #ccc;box-shadow:0 2px 4px rgba(0,0,0,.35);margin:0 .15rem .3rem 0;font-family:Georgia,serif;line-height:1}
.card.red{color:#c62828}
.card b{font-weight:700}
.card i{font-style:normal;font-size:1.2em}
.card.lg{width:3.6rem;height:5.1rem;font-size:1.5rem}
.card.md{width:2.9rem;height:4.1rem;font-size:1.2rem}
.card.sm{width:2.05rem;height:2.9rem;font-size:.85rem}
.card.back{background:repeating-linear-gradient(45deg,#1e4fa3,#1e4fa3 4px,#2a62c4 4px,#2a62c4 8px);border:2px solid #fff}
@media (min-width:768px){.card.lg{width:4.4rem;height:6.2rem;font-size:1.8rem}.card.md{width:3.4rem;height:4.8rem;font-size:1.4rem}.card.sm{width:2.4rem;height:3.4rem;font-size:1rem}}
.tag{display:inline-block;border-radius:.35rem;padding:0 .35rem;font-size:.72rem;font-weight:700;color:#fff}
.tag.win{background:#2e7d32}
.tag.lose{background:#c62828}
.tag.push{background:#546e7a}
.banner{text-align:center;border-radius:.8rem;padding:.6rem;margin:.2rem 0 .6rem;font-size:1.4rem;font-weight:800;color:#fff}
.banner small{display:block;font-size:.9rem;font-weight:600;opacity:.95}
.banner.win{background:#2e7d32}
.banner.lose{background:#c62828}
.banner.push{background:#546e7a}
.betbox{display:flex;justify-content:space-between;align-items:center;background:rgba(0,0,0,.28);border-radius:.8rem;padding:.5rem .9rem;margin-bottom:.5rem}
.betbox b{font-size:1.8rem;color:#ffd54f}
.welcome{text-align:center;background:rgba(0,0,0,.25);border-radius:1rem;padding:1.2rem;margin:1rem 0}
.uid{font-size:3rem;font-weight:800;letter-spacing:.3rem;color:#ffd54f;margin:.4rem 0}
div[data-testid="stHorizontalBlock"]{flex-wrap:nowrap !important;gap:.5rem !important}
div[data-testid="stHorizontalBlock"]>div{min-width:0 !important;flex:1 1 0 !important;width:auto !important}
.stButton>button,.stFormSubmitButton>button{min-height:3.1rem;font-size:1.05rem;font-weight:700;border-radius:.8rem}
button[kind="primary"],button[kind="primaryFormSubmit"],button[data-testid="stBaseButton-primary"],button[data-testid="stBaseButton-primaryFormSubmit"]{color:#1b1b1b !important}
</style>"""

# outcome → (小さなタグ, バナー, 色)
OUTCOME = {
    "blackjack": ("BJ", "ブラックジャック!", "win"),
    "win": ("勝ち", "勝ち!", "win"),
    "push": ("引分", "引き分け", "push"),
    "lose": ("負け", "負け…", "lose"),
    "bust": ("バースト", "バースト…", "lose"),
}


# ---------------------------------------------------------------- 描画パーツ
def card_html(card: Card | None, size: str) -> str:
    if card is None:
        return f'<span class="card back {size}"></span>'
    red = " red" if card.is_red else ""
    return f'<span class="card {size}{red}"><b>{card.rank}</b><i>{card.suit}</i></span>'


def hand_html(cards: list[Card], size: str, hide_hole: bool = False) -> str:
    if not cards:
        return '<div class="hand"><span class="ph">—</span></div>'
    parts = [card_html(None if (hide_hole and i == 1) else c, size) for i, c in enumerate(cards)]
    return '<div class="hand">' + "".join(parts) + "</div>"


def net_text(n: int) -> str:
    if n > 0:
        return f"+{n:,}"
    if n < 0:
        return f"−{-n:,}"
    return "±0"


def total_label(seat: Seat) -> str:
    if not seat.cards:
        return ""
    total = seat.total
    return f"{total}" + ("(ソフト)" if seat.soft and total <= 21 else "")


def tag_html(seat: Seat, phase: str) -> str:
    if phase == "result" and seat.outcome:
        label, _, cls = OUTCOME[seat.outcome]
        return f'<span class="tag {cls}">{label} {net_text(seat.net)}</span>'
    if seat.is_blackjack:
        return '<span class="tag win">BJ</span>'
    if seat.is_bust:
        return '<span class="tag lose">バースト</span>'
    if seat.doubled:
        return '<span class="tag push">ダブル</span>'
    return ""


def dealer_html(g: Game) -> str:
    hide = g.phase == "playing"
    total, tag = "", ""
    if g.dealer_cards:
        total = "?" if hide else str(g.dealer_total)
        if not hide:
            if g.dealer_bj:
                tag = '<span class="tag win">BJ</span>'
            elif g.dealer_bust:
                tag = '<span class="tag lose">バースト</span>'
    return (
        '<div class="dealer"><div class="nm"><span>ディーラー</span></div>'
        + hand_html(g.dealer_cards, "md", hide_hole=hide)
        + f'<div class="tot">{total} {tag}</div></div>'
    )


def cpu_html(seat: Seat, g: Game) -> str:
    body = hand_html(seat.cards, "sm") if seat.cards else '<div class="hand"><span class="ph">待機中</span></div>'
    bet = f'<div class="bet">ベット {seat.bet:,}</div>' if seat.bet else '<div class="bet">&nbsp;</div>'
    return (
        f'<div class="seat"><div class="nm"><span>{seat.name}</span><span>🪙{seat.chips:,}</span></div>'
        f'{bet}{body}<div class="tot">{total_label(seat)} {tag_html(seat, g.phase)}</div></div>'
    )


def me_html(g: Game) -> str:
    me = g.human
    bet = f"ベット {me.bet:,}" if me.bet else ""
    return (
        f'<div class="me"><div class="nm"><span>あなた({me.name})</span><span>{bet}</span></div>'
        + hand_html(me.cards, "lg")
        + f'<div class="tot">{total_label(me)} {tag_html(me, g.phase)}</div></div>'
    )


# ---------------------------------------------------------------- ボタンの処理
def _g() -> Game:
    return st.session_state.game


def _persist() -> None:
    set_chips(st.session_state.user, _g().human.chips)


def _after_action() -> None:
    if _g().phase == "result":  # ラウンドが終わったらチップを保存
        _persist()


def _try(action) -> bool:
    """ゲーム操作を実行する。不正な操作(GameError)は無視して False を返す。
    再実行のたびに GameError のクラスが別物になるため、型ではなく名前で判定する。"""
    try:
        action()
    except Exception as e:  # noqa: BLE001
        if type(e).__name__ != "GameError":
            raise
        return False
    return True


def _clamp_bet(bet: int, chips: int) -> int:
    return max(MIN_BET, min(bet, chips))


def add_bet(n: int) -> None:
    st.session_state.bet = min(st.session_state.bet + n, _g().human.chips)


def clear_bet() -> None:
    st.session_state.bet = 0


def all_in() -> None:
    st.session_state.bet = _g().human.chips


def do_deal() -> None:
    bet = st.session_state.bet
    if _try(lambda: _g().deal(bet)):
        st.session_state.last_bet = bet
        _after_action()


def do_hit() -> None:
    if _try(lambda: _g().hit()):
        _after_action()


def do_stand() -> None:
    if _try(lambda: _g().stand()):
        _after_action()


def do_double() -> None:
    if _try(lambda: _g().double()):
        _after_action()


def next_round() -> None:
    g = _g()
    if g.human.chips < MIN_BET:  # 破産したら初期チップで再開
        g.human.chips = START_CHIPS
        _persist()
    g.new_round()
    st.session_state.bet = _clamp_bet(st.session_state.last_bet, g.human.chips)


def start_session(uid: str) -> None:
    chips = get_chips(uid)
    if chips < MIN_BET:
        chips = START_CHIPS
        set_chips(uid, chips)
    st.session_state.user = uid
    st.session_state.game = Game(uid, chips)
    st.session_state.bet = min(50, chips)
    st.session_state.last_bet = st.session_state.bet


def begin_after_register(uid: str) -> None:
    del st.session_state["new_user"]
    start_session(uid)


def logout() -> None:
    for key in ("user", "game", "bet", "last_bet"):
        if key in st.session_state:
            del st.session_state[key]


# ---------------------------------------------------------------- 画面
def auth_screen() -> None:
    st.markdown("## 🃏 ブラックジャック")
    tab_login, tab_reg = st.tabs(["ログイン", "新規登録"])

    with tab_login:
        with st.form("login_form"):
            uid = st.text_input("ユーザー名(4桁)", max_chars=4, key="login_id", placeholder="0001")
            pw = st.text_input("パスワード(4桁の数字)", type="password", max_chars=4, key="login_pw")
            submitted = st.form_submit_button("ログイン", type="primary", **WIDE_FORM)
        if submitted:
            if not valid_pin(pw):
                st.error("パスワードは4桁の数字です。")
            else:
                ok, msg = authenticate(uid, pw)
                if ok:
                    start_session(normalize_id(uid))
                    st.rerun()
                else:
                    st.error(msg)

    with tab_reg:
        st.caption("ユーザー名は登録順に自動で割り当てられます(0001〜9999)。")
        with st.form("register_form"):
            pw1 = st.text_input("パスワード(4桁の数字)", type="password", max_chars=4, key="reg_pw1")
            pw2 = st.text_input("パスワード(確認)", type="password", max_chars=4, key="reg_pw2")
            submitted = st.form_submit_button("登録する", type="primary", **WIDE_FORM)
        if submitted:
            if not valid_pin(pw1):
                st.error("パスワードは4桁の数字です。")
            elif pw1 != pw2:
                st.error("確認用のパスワードが一致しません。")
            else:
                try:
                    st.session_state.new_user = register(pw1)
                except UserStoreError as e:
                    st.error(str(e))
                else:
                    st.rerun()


def welcome_screen() -> None:
    uid = st.session_state.new_user
    st.markdown(
        '<div class="welcome">登録しました!<br>あなたのユーザー名'
        f'<div class="uid">{uid}</div>'
        "ログインに必要です。メモ(スクリーンショット)しておいてください。</div>",
        unsafe_allow_html=True,
    )
    st.button("ゲームを始める", key="start", type="primary", on_click=begin_after_register, args=(uid,), **WIDE)


def controls_betting(g: Game) -> None:
    bet, chips = st.session_state.bet, g.human.chips
    st.markdown(
        f'<div class="betbox"><span>ベット額</span><b>🪙 {bet:,}</b></div>',
        unsafe_allow_html=True,
    )
    cols = st.columns(4)
    for col, amount in zip(cols, (10, 50, 100, 500)):
        with col:
            st.button(f"+{amount}", key=f"add{amount}", on_click=add_bet, args=(amount,), disabled=bet >= chips, **WIDE)
    c1, c2 = st.columns(2)
    with c1:
        st.button("クリア", key="clear", on_click=clear_bet, **WIDE)
    with c2:
        st.button("オールイン", key="allin", on_click=all_in, **WIDE)
    st.button(
        f"ディール(ベット {bet:,})",
        key="deal",
        type="primary",
        on_click=do_deal,
        disabled=bet < MIN_BET,
        **WIDE,
    )


def controls_playing(g: Game) -> None:
    c1, c2, c3 = st.columns(3)
    with c1:
        st.button("ヒット", key="hit", type="primary", on_click=do_hit, **WIDE)
    with c2:
        st.button("スタンド", key="stand", on_click=do_stand, **WIDE)
    with c3:
        st.button("ダブル", key="double", on_click=do_double, disabled=not g.can_double, **WIDE)
    st.caption("ダブル: ベットを2倍にして1枚だけ引き、そのまま勝負")


def controls_result(g: Game) -> None:
    _, banner, cls = OUTCOME[g.human.outcome]
    st.markdown(
        f'<div class="banner {cls}">{banner}<small>{net_text(g.human.net)} チップ</small></div>',
        unsafe_allow_html=True,
    )
    if g.human.chips < MIN_BET:
        st.error("チップが尽きました。")
        st.button(f"チップ {START_CHIPS:,} で再開", key="next", type="primary", on_click=next_round, **WIDE)
    else:
        st.button("次のラウンド", key="next", type="primary", on_click=next_round, **WIDE)


def game_screen() -> None:
    g: Game = st.session_state.game
    uid = st.session_state.user

    st.markdown(
        f'<div class="hdr"><span>🃏 ユーザー {uid}</span><span class="bal">🪙 {g.human.chips:,}</span></div>',
        unsafe_allow_html=True,
    )
    table = dealer_html(g) + '<div class="cpus">' + "".join(cpu_html(s, g) for s in g.cpus) + "</div>"
    if g.phase != "betting":
        table += me_html(g)
    st.markdown(table, unsafe_allow_html=True)

    if g.events:
        st.caption(" / ".join(g.events))

    if g.phase == "betting":
        controls_betting(g)
    elif g.phase == "playing":
        controls_playing(g)
    else:
        controls_result(g)

    st.caption(f"ラウンド {g.round_no} ・ シュー残り {len(g.shoe.cards)} 枚")
    with st.expander("メニュー・ルール"):
        st.button("ログアウト", key="logout", on_click=logout, **WIDE)
        st.markdown(
            "- ブラックジャックは 3:2、通常の勝ちは 1:1、引き分けはベット返却\n"
            "- ディーラーは17以上でスタンド(ソフト17も)\n"
            "- ダブルダウンは最初の2枚のときだけ\n"
            "- チップはラウンドごとに自動保存されます\n"
            "- CPUのチップは保存されません(ログインごとに1,000から)"
        )


def main() -> None:
    st.set_page_config(
        page_title="ブラックジャック",
        page_icon="🃏",
        layout="centered",
        initial_sidebar_state="collapsed",
    )
    st.markdown(CSS, unsafe_allow_html=True)
    if st.session_state.get("new_user"):
        welcome_screen()
    elif "user" not in st.session_state:
        auth_screen()
    else:
        game_screen()


if __name__ == "__main__":  # Streamlit はこの形でスクリプトを実行する
    main()
