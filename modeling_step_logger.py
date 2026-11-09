# SPDX-License-Identifier: GPL-3.0-or-later
"""
モデリング操作記録 (Modeling Step Logger) v1.2

卒業研究「Blenderにおける3Dモデリング手法の効率比較」用の記録アドオン（Blender 4.5 LTS 用）。

■ 記録するもの
- 制作時間（記録開始〜記録終了）
- 操作ステップ数 ＝ モデリング操作 ＋ 数値変更
    - モデリング操作: Blender が「操作」として記録したもの（押し出し、ループカット、
      モディファイアの追加・適用、移動など）。WindowManager.operators を 0.1 秒ごとに確認する。
    - 数値変更: 操作として記録されない変更。オブジェクトの位置・回転・拡大縮小、
      モディファイアの設定値、編集モード中の頂点の位置を見張り、操作なしで値が変わって
      1 秒間落ち着いたら 1 回と数える。F9 での調整し直しも数値変更として数える。
    - 選択・モード切替・視点の操作は数えない（ログには残す）。
- 取り消し回数（Ctrl+Z）。取り消した操作も操作ステップ数には残る。
- 作業部分（本体／取手／つなぎ・全体）ごとの時間と操作ステップ数
- 完成時の面数（モディファイア適用後）、部品の数、穴の数、高さ、直径

■ 出力（作業中のファイルと同じ場所の「操作記録」フォルダ）
- まとめ.csv          記録 1 回につき 1 行
- 操作ログ_*.csv      1 つひとつの操作（確認用）
- 操作内訳_*.csv      操作の種類ごとの回数
"""

bl_info = {
    "name": "モデリング操作記録 (Modeling Step Logger)",
    "author": "Igi Misato",
    "version": (1, 2, 0),
    "blender": (4, 2, 0),
    "location": "3Dビューポート > サイドバー(N) > 操作記録",
    "description": "制作時間・操作ステップ数・取り消し回数・面数・寸法を作業部分ごとにCSVへ記録する",
    "category": "System",
}

import csv
import math
import os
import time
from datetime import datetime

import bmesh
import bpy
from bpy.app.handlers import persistent
from bpy.props import EnumProperty, IntProperty, StringProperty

POLL_INTERVAL = 0.1   # 確認の間隔（秒）
SETTLE_TIME = 1.0     # 数値がこの秒数変わらなかったら、1 回の数値変更として数える

METHOD_ITEMS = [
    ("BOX", "ボックスモデリング", ""),
    ("SPIN", "回転体モデリング (Spin)", ""),
    ("PRIMITIVE", "プリミティブ＋Boolean", ""),
    ("OTHER", "その他", ""),
]
PART_ITEMS = [
    ("BODY", "本体", "本体だけを作っている"),
    ("HANDLE", "取手", "取手だけを作っている"),
    ("JOIN", "つなぎ・全体", "本体と取手の両方にまたがる作業・全体にかかる作業"),
]
METHOD_LABELS = {k: label for k, label, _ in METHOD_ITEMS}
PART_LABELS = {k: label for k, label, _ in PART_ITEMS}
PART_KEYS = [k for k, _, _ in PART_ITEMS]

MODELING = "モデリング操作"
VALUE_CHANGE = "数値変更"
SELECT = "選択"
MODE = "モード切替"
VIEW = "視点・表示"
OTHER = "その他"

LOG_HEADER = ["経過秒", "時刻", "作業部分", "分類", "内容", "モード", "オブジェクト"]
SUMMARY_HEADER = (
    ["記録日時", "手法", "試行番号", "メモ",
     "制作時間(秒)", "操作ステップ数", "うちモデリング操作", "うち数値変更", "取り消し回数"]
    + [h for k in PART_KEYS for h in (f"{PART_LABELS[k]}の時間(秒)", f"{PART_LABELS[k]}の操作ステップ数")]
    + ["面数", "部品の数", "穴の数", "高さ(mm)", "直径(mm)", "操作ログファイル"]
)

MODE_IDS = {"OBJECT_OT_mode_set", "OBJECT_OT_editmode_toggle", "MESH_OT_select_mode"}
VIEW_PREFIXES = ("VIEW3D_OT_view", "SCREEN_OT_", "WM_OT_context_")
VIEW_IDS = {"VIEW3D_OT_rotate", "VIEW3D_OT_zoom", "VIEW3D_OT_move", "VIEW3D_OT_dolly",
            "VIEW3D_OT_localview", "VIEW3D_OT_toggle_shading", "VIEW3D_OT_toggle_xray",
            "VIEW3D_OT_zoom_border", "VIEW3D_OT_navigate", "VIEW3D_OT_fly", "VIEW3D_OT_walk"}
OTHER_PREFIXES = ("WM_OT_", "ED_OT_", "FILE_OT_", "INFO_OT_", "PREFERENCES_OT_", "VIEW3D_OT_",
                  "UI_OT_", "OUTLINER_OT_", "BUTTONS_OT_")
# モディファイアの設定のうち、形に関係しない表示用の項目
SKIP_MODIFIER_PROPS = {"rna_type", "name", "is_active", "is_override_data", "execution_time",
                       "persistent_uid", "use_pin_to_last", "show_expanded"}


def classify(idname):
    """操作 ID を分類する。None は記録しない操作（BlenderKit とこのアドオン自身）。"""
    upper = idname.upper()
    if "BLENDERKIT" in upper or idname.startswith("MSLOG_"):
        return None
    if idname in MODE_IDS:
        return MODE
    if idname in VIEW_IDS or idname.startswith(VIEW_PREFIXES) or "HIDE" in upper or "REVEAL" in upper:
        return VIEW
    if "SELECT" in upper:
        return SELECT
    if idname.startswith(OTHER_PREFIXES):
        return OTHER
    return MODELING


# ---------------------------------------------------------------- 記録中の状態

class _State:
    running = False
    start_time = 0.0
    start_dt = None
    out_dir = ""
    log_path = ""
    method = ""
    trial = 0
    note = ""
    part = "BODY"
    part_since = 0.0
    part_time = {}
    part_steps = {}
    breakdown = {}          # {(分類, 内容): {部分: 回数}}
    modeling = 0
    value_changes = 0
    undo = 0
    prev_ops = []
    last_op_props = None
    after_undo = False
    baseline_sig = None
    seen_sig = None
    pending_since = None
    pending_kind = ""
    pending_undos = 0       # まだ判定していない取り消しの数
    undo_target = None      # 取り消す前の最後の操作（左下のパネルでの調整を見分けるため）
    undo_sig = None         # 取り消した直後の形
    undo_props = None       # 取り消した直後の最後の操作の設定値


S = _State()


def _elapsed():
    return round(time.monotonic() - S.start_time, 2)


# ---------------------------------------------------------------- 書き出し

def _output_dir():
    base = os.path.dirname(bpy.data.filepath) if bpy.data.filepath else os.path.expanduser("~")
    path = os.path.join(base, "操作記録")
    os.makedirs(path, exist_ok=True)
    return path


def _append_row(path, row, header):
    is_new = not os.path.exists(path)
    with open(path, "a", newline="", encoding="utf-8-sig" if is_new else "utf-8") as f:
        writer = csv.writer(f)
        if is_new:
            writer.writerow(header)
        writer.writerow(row)


def _log(category, content):
    mode, obj = "", ""
    try:
        mode = bpy.context.mode
        active = bpy.context.view_layer.objects.active
        obj = active.name if active else ""
    except Exception:
        pass
    _append_row(S.log_path, [_elapsed(), datetime.now().strftime("%H:%M:%S"),
                             PART_LABELS.get(S.part, ""), category, content, mode, obj], LOG_HEADER)


def _count_step(category, content):
    """操作ステップ 1 回を、今の作業部分に足して記録する。"""
    if category == MODELING:
        S.modeling += 1
    else:
        S.value_changes += 1
    S.part_steps[S.part] = S.part_steps.get(S.part, 0) + 1
    per_part = S.breakdown.setdefault((category, content), {})
    per_part[S.part] = per_part.get(S.part, 0) + 1
    _log(category, content)


# ---------------------------------------------------------------- 設定値の読み取り

def _value(v, depth=0):
    if isinstance(v, float):
        return round(v, 6)
    if isinstance(v, (int, bool, str)) or v is None:
        return v
    if isinstance(v, bpy.types.ID):
        return v.name
    if hasattr(v, "bl_rna") and depth < 3:
        return _rna_sig(v, depth + 1)
    try:
        return tuple(_value(x, depth) for x in v)
    except TypeError:
        return str(v)


def _rna_sig(data, depth=0, skip=()):
    items = []
    for prop in data.bl_rna.properties:
        key = prop.identifier
        if key == "rna_type" or key in skip or prop.type == "COLLECTION":
            continue
        try:
            items.append((key, _value(getattr(data, key), depth)))
        except Exception:
            pass
    return tuple(items)


def _edit_verts_sig(obj):
    """編集モード中の頂点の位置（数値入力での変更を見つけるため）。"""
    try:
        bm = bmesh.from_edit_mesh(obj.data)  # 編集中のメッシュ。free() してはいけない
        return (len(bm.verts),
                tuple(round(c, 5) for v in bm.verts for c in v.co))
    except Exception:
        return None


def _shape_sig():
    """形に関わる設定値（オブジェクトの位置・回転・拡大縮小、モディファイア、編集中の頂点）。"""
    objs = []
    for obj in bpy.context.scene.objects:
        if obj.type != "MESH":
            continue
        mods = tuple((m.type, _rna_sig(m, skip=SKIP_MODIFIER_PROPS)) for m in obj.modifiers)
        verts = _edit_verts_sig(obj) if obj.mode == "EDIT" else None
        objs.append((obj.name, _value(obj.location), _value(obj.rotation_euler),
                     _value(obj.scale), mods, verts))
    return tuple(sorted(objs, key=lambda x: x[0]))


def _change_kind(old, new):
    """何が変わったかを、ログ用の短い言葉にする。"""
    if old is None:
        return "パネルで数値を変更"
    old_d = {o[0]: o for o in old}
    for o in new:
        before = old_d.get(o[0])
        if before is None:
            continue
        if o[5] != before[5]:
            return f"{o[0]} の頂点を数値で変更"
        if o[4] != before[4]:
            return f"{o[0]} のモディファイアの数値を変更"
        if o[1:4] != before[1:4]:
            return f"{o[0]} の位置・回転・拡大縮小を数値で変更"
    return "パネルで数値を変更"


# ---------------------------------------------------------------- 操作の取得

def _snapshot():
    return [(op.as_pointer(), op.bl_idname, op.name) for op in bpy.context.window_manager.operators]


def _last_op_props():
    ops = bpy.context.window_manager.operators
    if not len(ops):
        return None
    op = ops[-1]
    try:
        return (op.as_pointer(), op.bl_idname, op.name, _rna_sig(op.properties))
    except Exception:
        return (op.as_pointer(), op.bl_idname, op.name, None)


def _new_operators(prev, cur):
    """前回の一覧 prev と今回の一覧 cur から、増えた操作を返す（古い順）。"""
    if not prev:
        return list(cur)
    last = prev[-1][:2]
    for i in range(len(cur) - 1, -1, -1):
        if cur[i][:2] == last:
            return list(cur[i + 1:])
    prev_keys = {p[:2] for p in prev}
    return [c for c in cur if c[:2] not in prev_keys]


def _is_adjustment(prev, cur, new_op):
    """F9 で調整し直した操作か（直前と同じ種類の操作で、直前の記録が置き換わった）。"""
    if not prev or S.after_undo:
        return False
    last_ptr, last_id = prev[-1][:2]
    return new_op[1] == last_id and last_ptr not in {c[0] for c in cur}


def _modal_running():
    try:
        return any(len(w.modal_operators) for w in bpy.context.window_manager.windows)
    except Exception:
        return False


# ---------------------------------------------------------------- 見張り

def _poll():
    if not S.running:
        return None
    try:
        _check()
    except Exception:
        pass
    _redraw_sidebars()
    return POLL_INTERVAL


def _check():
    if S.pending_undos:
        _resolve_undo()
        return
    cur = _snapshot()
    new_ops = _new_operators(S.prev_ops, cur)
    counted = False

    for op in new_ops:
        category = classify(op[1])
        if category is None:
            continue
        if category == MODELING and _is_adjustment(S.prev_ops, cur, op):
            _count_step(VALUE_CHANGE, f"{op[2]} を調整（F9）")
        elif category == MODELING:
            _count_step(MODELING, op[2])
        else:
            _log(category, op[2])
        counted = True
        S.after_undo = False

    # 同じ操作のまま設定値だけ変わった＝F9 で直前の操作を調整した
    props = _last_op_props()
    if (not new_ops and props and S.last_op_props and props[:2] == S.last_op_props[:2]
            and props[3] != S.last_op_props[3] and classify(props[1]) == MODELING):
        _count_step(VALUE_CHANGE, f"{props[2]} を調整（F9）")
        counted = True
    S.prev_ops = cur
    S.last_op_props = props

    # 操作として記録されない数値の変更
    sig = _shape_sig()
    now = time.monotonic()
    if counted:
        S.baseline_sig = S.seen_sig = sig
        S.pending_since = None
        return
    if sig != S.seen_sig:
        if S.pending_since is None:
            S.pending_kind = _change_kind(S.baseline_sig, sig)
        S.seen_sig = sig
        S.pending_since = now
    if (S.pending_since is not None and now - S.pending_since >= SETTLE_TIME
            and not _modal_running()):
        _settle()


def _settle():
    """落ち着いた数値変更を確定する（元の値に戻っていたら数えない）。"""
    if S.seen_sig != S.baseline_sig:
        _count_step(VALUE_CHANGE, S.pending_kind or "パネルで数値を変更")
    S.baseline_sig = S.seen_sig
    S.pending_since = None


def _redraw_sidebars():
    try:
        for window in bpy.context.window_manager.windows:
            for area in window.screen.areas:
                if area.type == "VIEW_3D":
                    area.tag_redraw()
    except Exception:
        pass


def _resync(after_undo=True):
    """取り消し・やり直しの後は、その時点の状態を基準にし直す。"""
    S.prev_ops = _snapshot()
    S.last_op_props = _last_op_props()
    S.baseline_sig = S.seen_sig = _shape_sig()
    S.pending_since = None
    S.after_undo = after_undo


@persistent
def _on_undo(*_args):
    """取り消しが起きたら、すぐには数えずに「取り消し待ち」にする。

    左下のパネル（F9）で数値を直すと、Blender は 1 回の処理の中で
    「取り消し → 新しい数値でやり直し」を行う。人が次の操作をするには新しい入力が必要で、
    それは必ず次の処理の回になる。そこで、取り消しの直後の最初の確認で、
    同じ操作がもうやり直されていれば「パネルでの調整」、そうでなければ本物の取り消しとする。
    """
    if not S.running:
        return
    if S.pending_undos == 0:
        S.undo_target = S.last_op_props
    S.pending_undos += 1
    try:
        S.undo_sig = _shape_sig()
        S.undo_props = _last_op_props()
    except Exception:
        S.undo_sig = S.undo_props = None
    if not bpy.app.timers.is_registered(_resolve_undo_timer):
        bpy.app.timers.register(_resolve_undo_timer, first_interval=0.0)


def _resolve_undo_timer():
    if S.running and S.pending_undos:
        try:
            _resolve_undo()
        except Exception:
            S.pending_undos = 0
    return None


def _resolve_undo():
    """たまった取り消し待ちを判定する。パネルでの調整は、最後の 1 回だけ。"""
    pending, S.pending_undos = S.pending_undos, 0
    if not pending:
        return
    target, props = S.undo_target, _last_op_props()
    redone = False
    if target and props and props[1] == target[1] and classify(props[1]) == MODELING:
        undo_props = S.undo_props[3] if S.undo_props else None
        redone = _shape_sig() != S.undo_sig or props[3] != undo_props
    real = pending - 1 if redone else pending
    for _ in range(real):
        S.undo += 1
        _log("取り消し", "Ctrl+Z")
    if redone:
        _count_step(VALUE_CHANGE, f"{props[2]} を左下のパネルで調整")
    _resync(after_undo=real > 0)


@persistent
def _on_redo(*_args):
    if S.running:
        _log("やり直し", "Shift+Ctrl+Z")
        _resync()


@persistent
def _on_load_pre(*_args):
    if S.running:
        _finish("（別のファイルを開いたため終了）")


# ---------------------------------------------------------------- 作業部分の切り替え

def _close_part_time():
    now = time.monotonic()
    S.part_time[S.part] = S.part_time.get(S.part, 0.0) + (now - S.part_since)
    S.part_since = now


def _on_part_changed(wm, _context):
    if not S.running or wm.mslog_part == S.part:
        return
    try:
        _check()  # 切り替える前の操作は前の部分に数える
        if S.pending_since is not None:
            _settle()
    except Exception:
        pass
    _close_part_time()
    old = PART_LABELS[S.part]
    S.part = wm.mslog_part
    _log("作業切替", f"{old} → {PART_LABELS[S.part]}")


# ---------------------------------------------------------------- 完成時の計測

def _count_islands(bm):
    parent = list(range(len(bm.verts)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    bm.verts.index_update()
    for e in bm.edges:
        a, b = find(e.verts[0].index), find(e.verts[1].index)
        if a != b:
            parent[a] = b
    return len({find(i) for i in range(len(parent))})


RIM_DEPTH_MM = 10.0   # 直径を測る範囲：上端から 10mm 以内（取手が付かない口の部分）


def _max_width(points_xy):
    """横の幅を 0.5 度ずつ向きを変えて測り、一番広い幅を返す。

    口の部分だけの頂点で測るので取手は入らない。多角形の角から角まで（＝設計上の直径）を測る。
    """
    if not points_xy:
        return None
    best = 0.0
    for step in range(360):
        a = math.radians(step * 0.5)
        ca, sa = math.cos(a), math.sin(a)
        proj = [x * ca + y * sa for x, y in points_xy]
        best = max(best, max(proj) - min(proj))
    return best


def _mesh_stats(context):
    objects = [o for o in context.view_layer.objects if o.type == "MESH" and o.visible_get()]
    for obj in objects:
        if obj.mode == "EDIT":
            obj.update_from_editmode()  # 編集モード中の変更を反映してから測る
    depsgraph = context.evaluated_depsgraph_get()
    depsgraph.update()
    scale_mm = context.scene.unit_settings.scale_length * 1000.0

    faces = islands = holes = 0
    points = []
    z_lo, z_hi = float("inf"), float("-inf")
    for obj in objects:
        obj_eval = obj.evaluated_get(depsgraph)
        mesh = obj_eval.to_mesh()
        try:
            faces += len(mesh.polygons)
            for v in mesh.vertices:
                co = obj.matrix_world @ v.co
                points.append((co.x, co.y, co.z))
                z_lo, z_hi = min(z_lo, co.z), max(z_hi, co.z)
            bm = bmesh.new()
            try:
                bm.from_mesh(mesh)
                holes += sum(1 for e in bm.edges if not e.is_manifold)
                islands += _count_islands(bm)
            finally:
                bm.free()
        finally:
            obj_eval.to_mesh_clear()

    rim_floor = z_hi - RIM_DEPTH_MM / scale_mm
    width = _max_width([(x, y) for x, y, z in points if z >= rim_floor])
    return {
        "faces": faces, "islands": islands, "holes": holes,
        "height": round((z_hi - z_lo) * scale_mm, 2) if points else "",
        "diameter": round(width * scale_mm, 2) if width is not None else "",
    }


# ---------------------------------------------------------------- 開始・終了

def _start(context):
    wm = context.window_manager
    S.running = True
    S.start_time = time.monotonic()
    S.start_dt = datetime.now()
    S.method = METHOD_LABELS.get(wm.mslog_method, wm.mslog_method)
    S.trial = wm.mslog_trial
    S.note = wm.mslog_note
    S.part = "BODY"
    wm.mslog_part = "BODY"   # 開始時は「本体」
    S.part_since = S.start_time
    S.part_time = {k: 0.0 for k in PART_KEYS}
    S.part_steps = {k: 0 for k in PART_KEYS}
    S.breakdown = {}
    S.modeling = S.value_changes = S.undo = S.pending_undos = 0
    S.out_dir = _output_dir()
    stamp = S.start_dt.strftime("%Y%m%d_%H%M%S")
    S.log_path = os.path.join(S.out_dir, f"操作ログ_{S.method}_試行{S.trial}_{stamp}.csv")
    _resync(after_undo=False)

    _log("開始", S.note)
    for handlers, func in ((bpy.app.handlers.undo_post, _on_undo),
                           (bpy.app.handlers.redo_post, _on_redo)):
        if func not in handlers:
            handlers.append(func)
    bpy.app.timers.register(_poll, first_interval=POLL_INTERVAL)


def _write_breakdown():
    stamp = S.start_dt.strftime("%Y%m%d_%H%M%S")
    path = os.path.join(S.out_dir, f"操作内訳_{S.method}_試行{S.trial}_{stamp}.csv")
    header = ["分類", "内容"] + [PART_LABELS[k] for k in PART_KEYS] + ["合計"]
    rows = []
    for (category, content), per_part in S.breakdown.items():
        counts = [per_part.get(k, 0) for k in PART_KEYS]
        rows.append([category, content] + counts + [sum(counts)])
    rows.sort(key=lambda r: (r[0] != MODELING, -r[-1]))
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def _finish(note_suffix="", context=None):
    context = context or bpy.context
    try:
        if S.pending_undos:
            _resolve_undo()
        _check()  # 終了直前の操作を取りこぼさない
        if S.pending_since is not None:
            _settle()
    except Exception:
        pass
    _close_part_time()
    S.running = False
    seconds = _elapsed()
    for handlers, func in ((bpy.app.handlers.undo_post, _on_undo),
                           (bpy.app.handlers.redo_post, _on_redo)):
        if func in handlers:
            handlers.remove(func)
    if bpy.app.timers.is_registered(_poll):
        bpy.app.timers.unregister(_poll)

    try:
        stats = _mesh_stats(context)
    except Exception as exc:
        stats = {"faces": "", "islands": "", "holes": "", "height": "", "diameter": ""}
        note_suffix += f"（計測エラー: {exc}）"

    _log("終了", note_suffix)
    _write_breakdown()
    part_cols = [v for k in PART_KEYS
                 for v in (round(S.part_time.get(k, 0.0), 2), S.part_steps.get(k, 0))]
    _append_row(os.path.join(S.out_dir, "まとめ.csv"), [
        S.start_dt.strftime("%Y-%m-%d %H:%M:%S"), S.method, S.trial, S.note + note_suffix,
        seconds, S.modeling + S.value_changes, S.modeling, S.value_changes, S.undo,
        *part_cols,
        stats["faces"], stats["islands"], stats["holes"], stats["height"], stats["diameter"],
        os.path.basename(S.log_path),
    ], SUMMARY_HEADER)
    return seconds, stats


# ---------------------------------------------------------------- ボタン

class MSLOG_OT_start(bpy.types.Operator):
    bl_idname = "mslog.start"
    bl_label = "記録開始"
    bl_description = "制作時間と操作の記録を始める"

    @classmethod
    def poll(cls, context):
        return not S.running

    def execute(self, context):
        _start(context)
        self.report({"INFO"}, f"記録を開始しました：{S.method} 試行{S.trial}")
        return {"FINISHED"}


class MSLOG_OT_stop(bpy.types.Operator):
    bl_idname = "mslog.stop"
    bl_label = "記録終了"
    bl_description = "記録を終了し、まとめをCSVに書き出す"

    @classmethod
    def poll(cls, context):
        return S.running

    def execute(self, context):
        seconds, stats = _finish("", context)
        self.report({"INFO"}, f"記録しました：{seconds:.0f}秒、面数{stats['faces']}")
        return {"FINISHED"}


class MSLOG_OT_open_folder(bpy.types.Operator):
    bl_idname = "mslog.open_folder"
    bl_label = "記録フォルダを開く"

    def execute(self, context):
        bpy.ops.wm.path_open(filepath=_output_dir())
        return {"FINISHED"}


class MSLOG_PT_panel(bpy.types.Panel):
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "操作記録"
    bl_label = "モデリング操作記録"

    def draw(self, context):
        layout = self.layout
        wm = context.window_manager

        col = layout.column()
        col.enabled = not S.running
        col.prop(wm, "mslog_method", text="手法")
        col.prop(wm, "mslog_trial", text="試行番号")
        col.prop(wm, "mslog_note", text="メモ")

        layout.label(text="今の作業：")
        row = layout.row(align=True)
        row.scale_y = 1.5
        row.prop(wm, "mslog_part", expand=True)

        layout.separator()
        if S.running:
            box = layout.box()
            box.label(text=f"● 記録中  {_elapsed():.0f} 秒", icon="REC")
            big = box.row()
            big.scale_y = 1.4
            big.label(text=f"今の作業：{PART_LABELS[S.part]}")
            box.label(text=f"操作ステップ数: {S.modeling + S.value_changes}")
            box.label(text=f"（モデリング操作 {S.modeling}・数値変更 {S.value_changes}）")
            box.label(text=f"取り消し: {S.undo}")
            layout.operator("mslog.stop", icon="SNAP_FACE")
        else:
            layout.operator("mslog.start", icon="REC")
        layout.operator("mslog.open_folder", icon="FILE_FOLDER")


# ---------------------------------------------------------------- 登録

CLASSES = (MSLOG_OT_start, MSLOG_OT_stop, MSLOG_OT_open_folder, MSLOG_PT_panel)
WM_PROPS = ("mslog_method", "mslog_trial", "mslog_note", "mslog_part")


def register():
    for cls in CLASSES:
        bpy.utils.register_class(cls)
    wm = bpy.types.WindowManager
    wm.mslog_method = EnumProperty(name="手法", items=METHOD_ITEMS, default="BOX")
    wm.mslog_trial = IntProperty(name="試行番号", default=1, min=0)
    wm.mslog_note = StringProperty(name="メモ", default="")
    wm.mslog_part = EnumProperty(name="今の作業", items=PART_ITEMS, default="BODY",
                                 update=_on_part_changed)
    if _on_load_pre not in bpy.app.handlers.load_pre:
        bpy.app.handlers.load_pre.append(_on_load_pre)


def unregister():
    if S.running:
        _finish("（アドオンを無効化したため終了）")
    if _on_load_pre in bpy.app.handlers.load_pre:
        bpy.app.handlers.load_pre.remove(_on_load_pre)
    wm = bpy.types.WindowManager
    for name in WM_PROPS:
        if hasattr(wm, name):
            delattr(wm, name)
    for cls in reversed(CLASSES):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
