# SPDX-License-Identifier: GPL-3.0-or-later
"""
モデリング操作記録 (Modeling Step Logger) v2.0.1

卒業研究用の記録アドオン（Blender 4.5 LTS 用）。
Blender の操作を「形を変える・面を増やす・滑らかにする・その他」の4つに分けて、
時間と回数を記録し、グラフで比べられるようにする。

■ 時間の数え方（B）
  1つの操作の時間 ＝ 操作を始めた時刻 〜 その操作の数字を最後に直した時刻
  - キーを押してから確定までのあいだ（G・R・S・E・I・ループカット・ベベルなど）を測る
  - 確定のあと、左下のパネルやモディファイア・マテリアルの欄でその操作の数字を直したら、
    直し終わった時刻まで時間をのばす（次の操作をした時点で確定）
  - 「その他」の時間 ＝ 制作時間 − 3種類の時間（選ぶ・視点・考える時間など）
  - 操作ログには「開始・確定・最後に直した」の3つの時刻を残す

■ 出力（作業中のファイルと同じ場所の「操作記録」フォルダ）
  - まとめ.csv       記録1回につき1行。「グラフに使う」を × にするとグラフから外れる
  - 操作ログ_*.csv   1つひとつの操作（時系列グラフと「その他」の一覧に使う）
  - グラフ.html      「グラフを見る」で作られる。ブラウザで開く
"""

bl_info = {
    "name": "モデリング操作記録 (Modeling Step Logger)",
    "author": "Igi Misato",
    "version": (2, 0, 1),
    "blender": (4, 2, 0),
    "location": "3Dビューポート > サイドバー(N) > 操作記録",
    "description": "操作を4つに分けて時間と回数を記録し、グラフで比べる",
    "category": "System",
}

import csv
import io
import json
import math
import os
import shutil
import time
import webbrowser
from datetime import datetime

import bmesh
import bpy
from bpy.app.handlers import persistent
from bpy.app.translations import pgettext_iface
from bpy.props import EnumProperty, IntProperty, StringProperty

VERSION = "2.0.1"
POLL_INTERVAL = 0.1   # 確認の間隔（秒）
SETTLE_TIME = 1.0     # 数字の変更が、この秒数落ち着いたら確定する
MODAL_LINK = 0.35     # 動かす操作が終わってから、この秒数以内に記録された操作をつなげる

METHOD_ITEMS = [
    ("EXTRUDE", "①円から押し出し", ""),
    ("SPIN", "②回転体", ""),
    ("CYLINDER", "③円柱をくぼませる", ""),
    ("OTHER", "その他", ""),
]
PART_ITEMS = [
    ("BODY", "本体", "本体だけを作っている"),
    ("HANDLE", "取手", "取手だけを作っている"),
    ("JOIN", "つなぎ・全体", "本体と取手の両方にまたがる作業・仕上げなど全体にかかる作業"),
]
METHOD_LABELS = {k: label for k, label, _ in METHOD_ITEMS}
PART_LABELS = {k: label for k, label, _ in PART_ITEMS}
PART_KEYS = [k for k, _, _ in PART_ITEMS]

SHAPE, FACES, SMOOTH, OTHER = "形を変える", "面を増やす", "滑らかにする", "その他"
CATS = [SHAPE, FACES, SMOOTH, OTHER]
TIMED = [SHAPE, FACES, SMOOTH]

# ---------------------------------------------------------------- 操作の分け方

FACES_IDS = {
    "MESH_OT_inset", "MESH_OT_loopcut", "MESH_OT_loopcut_slide", "MESH_OT_offset_edge_loops",
    "MESH_OT_offset_edge_loops_slide", "MESH_OT_knife_tool", "MESH_OT_bisect", "MESH_OT_subdivide",
    "MESH_OT_bridge_edge_loops", "MESH_OT_spin", "MESH_OT_screw", "MESH_OT_fill_grid",
    "MESH_OT_fill", "MESH_OT_edge_face_add", "MESH_OT_solidify", "MESH_OT_dupli_extrude_cursor",
}
SMOOTH_IDS = {
    "MESH_OT_bevel", "OBJECT_OT_shade_smooth", "OBJECT_OT_shade_auto_smooth",
    "OBJECT_OT_shade_smooth_by_angle", "MESH_OT_faces_shade_smooth", "MATERIAL_OT_new",
    "OBJECT_OT_material_slot_add", "OBJECT_OT_subdivision_set", "MESH_OT_vertices_smooth",
}
SMOOTH_MODIFIERS = {"SUBSURF", "BEVEL", "SMOOTH", "CORRECTIVE_SMOOTH", "LAPLACIANSMOOTH",
                    "WEIGHTED_NORMAL", "MULTIRES"}
# 数字の直しを、直前のこの操作の続きとみなす
TIE_MODIFIER_OPS = {"OBJECT_OT_modifier_add", "OBJECT_OT_shade_auto_smooth",
                    "OBJECT_OT_shade_smooth_by_angle"}
TIE_MATERIAL_OPS = {"MATERIAL_OT_new", "OBJECT_OT_material_slot_add"}
# 時間を測らない「動かす操作」（視点・画面の操作）
NAV_MODAL_PREFIXES = ("VIEW3D_OT_rotate", "VIEW3D_OT_zoom", "VIEW3D_OT_move", "VIEW3D_OT_dolly",
                      "VIEW3D_OT_navigate", "VIEW3D_OT_fly", "VIEW3D_OT_walk", "VIEW3D_OT_view",
                      "SCREEN_OT_", "UI_OT_", "VIEW2D_OT_", "WM_OT_")
# モディファイアの設定のうち、形に関係しない表示用の項目
SKIP_MODIFIER_PROPS = {"rna_type", "name", "is_active", "is_override_data", "execution_time",
                       "persistent_uid", "use_pin_to_last", "show_expanded"}


def modifier_cat(mod_type, name=""):
    low = (name or "").lower()
    if mod_type in SMOOTH_MODIFIERS or (mod_type == "NODES" and ("smooth" in low or "スムーズ" in low)):
        return SMOOTH
    return FACES


def classify(idname, props=None):
    """操作 ID を4つに分ける。None は記録しない操作（このアドオン自身・BlenderKit）。"""
    upper = idname.upper()
    if "BLENDERKIT" in upper or idname.startswith("MSLOG_"):
        return None
    if idname.startswith("TRANSFORM_OT_"):
        return SHAPE
    if idname == "OBJECT_OT_modifier_add":
        return modifier_cat((props or {}).get("type", ""))
    if idname.startswith(("MESH_OT_extrude", "MESH_OT_primitive_")) or idname in FACES_IDS:
        return FACES
    if idname in SMOOTH_IDS:
        return SMOOTH
    return OTHER


# 押しても「直前の操作の続き」を切らない操作（モディファイアの欄をクリックしただけ など）
NON_BREAKING_IDS = {"OBJECT_OT_modifier_set_active"}


def _ui_name(op_name, idname, props=None):
    """(日本語の名前, 英語の名前)。操作の名前は「Operator」の翻訳から取る。"""
    en = op_name or idname
    ja = pgettext_iface(en, "Operator")
    if ja == en:
        ja = pgettext_iface(en)
    if idname == "OBJECT_OT_modifier_add" and props and props.get("type"):
        ja, en = f"{ja}（{props['type']}）", f"{en} ({props['type']})"
    return ja, en


# ---------------------------------------------------------------- 記録中の状態

class _State:
    running = False
    start_time = 0.0
    start_dt = None
    out_dir = ""
    log_name = ""
    author = method = note = ""
    trial = 0
    part = "BODY"
    part_since = 0.0
    part_time = {}
    events = []           # 操作の記録（dict）
    records = []          # 開始・終了・作業切替・取り消しなど
    last_event = None
    undo = 0
    prev_ops = []
    last_op_props = None
    after_undo = False
    baseline_sig = None
    seen_sig = None
    pending_since = None  # 数字の変更を最初に見つけた時刻
    pending_last = None   # 数字の変更を最後に見つけた時刻
    modal_ignore = set()
    modal_start = None
    modal_last = None     # (開始, 終了)
    pending_undos = 0
    undo_target = None
    undo_sig = None
    undo_props = None
    message = ""


S = _State()


def _elapsed():
    return round(time.monotonic() - S.start_time, 2)


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
    try:
        bm = bmesh.from_edit_mesh(obj.data)  # 編集中のメッシュ。free() してはいけない
        return (len(bm.verts), tuple(round(c, 5) for v in bm.verts for c in v.co))
    except Exception:
        return None


def _material_sig():
    out = []
    for mat in bpy.data.materials:
        if mat.users == 0:
            continue
        nodes = []
        if mat.use_nodes and mat.node_tree:
            for node in mat.node_tree.nodes:
                vals = []
                for sock in node.inputs:
                    if hasattr(sock, "default_value"):
                        vals.append(_value(sock.default_value))
                nodes.append((node.name, tuple(vals)))
        out.append((mat.name, _value(mat.diffuse_color), _value(mat.roughness), tuple(nodes)))
    return tuple(sorted(out, key=lambda x: x[0]))


def _shape_sig():
    """形・モディファイア・マテリアルの設定値。数字の直しを見つけるために使う。"""
    shapes, mods = [], []
    for obj in bpy.context.scene.objects:
        if obj.type != "MESH":
            continue
        verts = _edit_verts_sig(obj) if obj.mode == "EDIT" else None
        shapes.append((obj.name, _value(obj.location), _value(obj.rotation_euler),
                       _value(obj.scale), verts))
        for m in obj.modifiers:
            mods.append((obj.name, m.name, m.type, _rna_sig(m, skip=SKIP_MODIFIER_PROPS)))
    return {"shape": tuple(sorted(shapes, key=lambda x: x[0])), "mod": tuple(mods),
            "mat": _material_sig()}


def _change_info(old, new):
    """何が変わったか → (区分, ログ用の言葉, モディファイアの種類)。"""
    if old is None:
        return SHAPE, "数字を直す|Edit values", ""
    if new["mod"] != old["mod"]:
        before = {(m[0], m[1]): m for m in old["mod"]}
        for m in new["mod"]:
            if before.get((m[0], m[1])) != m:
                return modifier_cat(m[2], m[1]), f"{m[1]} の数字を直す|Edit modifier values ({m[2]})", m[2]
        return FACES, "モディファイアの数字を直す|Edit modifier values", ""
    if new["mat"] != old["mat"]:
        return SMOOTH, "マテリアルの数字を直す|Edit material values", ""
    if new["shape"] != old["shape"]:
        before = {o[0]: o for o in old["shape"]}
        for o in new["shape"]:
            b = before.get(o[0])
            if b is not None and o[4] != b[4]:
                return SHAPE, f"{o[0]} の頂点の位置を数字で直す|Edit vertex position values", ""
        return SHAPE, "位置・回転・大きさを数字で直す|Edit location / rotation / scale values", ""
    return None, "", ""


# ---------------------------------------------------------------- 操作の取得

def _op_props(op):
    try:
        return {k: v for k, v in _rna_sig(op.properties)}
    except Exception:
        return {}


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


def _props_of(ptr):
    for op in bpy.context.window_manager.operators:
        if op.as_pointer() == ptr:
            return _op_props(op)
    return {}


def _new_operators(prev, cur):
    if not prev:
        return list(cur)
    last = prev[-1][:2]
    for i in range(len(cur) - 1, -1, -1):
        if cur[i][:2] == last:
            return list(cur[i + 1:])
    prev_keys = {p[:2] for p in prev}
    return [c for c in cur if c[:2] not in prev_keys]


def _is_adjustment(prev, cur, new_op):
    """左下のパネルで直前の操作を調整し直したか（同じ種類の操作で、直前の記録が置き換わった）。"""
    if not prev or S.after_undo:
        return False
    last_ptr, last_id = prev[-1][:2]
    return new_op[1] == last_id and last_ptr not in {c[0] for c in cur}


def _modal_ids():
    ids = []
    try:
        for w in bpy.context.window_manager.windows:
            ids.extend(op.bl_idname for op in w.modal_operators)
    except Exception:
        pass
    return ids


def _active_modal_ids():
    return [i for i in _modal_ids()
            if i not in S.modal_ignore and not i.startswith(NAV_MODAL_PREFIXES)
            and "BLENDERKIT" not in i.upper() and not i.startswith("MSLOG_")]


# ---------------------------------------------------------------- 操作の記録

def _add_event(idname, name, cat, start, confirm, props=None, name_en=""):
    ev = {"start": start, "confirm": confirm, "end": confirm, "part": S.part, "cat": cat,
          "name": name, "name_en": name_en or name, "id": idname, "count": 1, "adjust": 0,
          "mod_type": (props or {}).get("type", "") if idname == "OBJECT_OT_modifier_add" else ""}
    S.events.append(ev)
    if idname not in NON_BREAKING_IDS:
        S.last_event = ev
    return ev


def _adjust_last(now, how):
    """直前の操作の数字を直した → 時間を直し終わった時刻までのばす（回数は増やさない）。"""
    ev = S.last_event
    if ev is None:
        return
    ev["end"] = max(ev["end"], now)
    ev["adjust"] += 1
    S.records.append({"t": now, "what": f"{ev['name']} を{how}"})


def _record(what):
    S.records.append({"t": _elapsed(), "what": what})


# ---------------------------------------------------------------- 見張り

def _poll():
    if not S.running:
        return None
    try:
        _check()
    except Exception as exc:
        S.message = f"確認中のエラー: {exc}"
    _redraw_sidebars()
    return POLL_INTERVAL


def _track_modal(now):
    active = _active_modal_ids()
    if active and S.modal_start is None:
        S.modal_start = max(0.0, now - POLL_INTERVAL / 2)
    elif not active and S.modal_start is not None:
        S.modal_last = (S.modal_start, now)
        S.modal_start = None
    return bool(active)


def _check():
    now = _elapsed()
    if S.pending_undos:
        _resolve_undo()
        return
    modal = _track_modal(now)
    cur = _snapshot()
    new_ops = _new_operators(S.prev_ops, cur)
    counted = False

    if new_ops and S.pending_since is not None:
        _settle()   # 新しい操作の前にあった数字の直しを先に確定する

    first = True
    for ptr, idname, op_name in new_ops:
        props = _props_of(ptr)
        cat = classify(idname, props)
        if cat is None:
            continue
        counted = True
        if cat != OTHER and _is_adjustment(S.prev_ops, cur, (ptr, idname, op_name)):
            _adjust_last(now, "左下のパネルで調整")
        else:
            start = confirm = now
            if first and S.modal_last and now - S.modal_last[1] <= MODAL_LINK:
                start, confirm = S.modal_last
                S.modal_last = None
            ja, en = _ui_name(op_name, idname, props)
            _add_event(idname, ja, cat, start, confirm, props, en)
            first = False
        S.after_undo = False

    # 同じ操作のまま設定値だけ変わった＝左下のパネルで直前の操作を調整した
    props = _last_op_props()
    if (not new_ops and props and S.last_op_props and props[:2] == S.last_op_props[:2]
            and props[3] != S.last_op_props[3] and classify(props[1]) not in (None, OTHER)):
        _adjust_last(now, "左下のパネルで調整")
        counted = True
    S.prev_ops = cur
    S.last_op_props = props

    sig = _shape_sig()
    if counted:
        S.baseline_sig = S.seen_sig = sig
        S.pending_since = S.pending_last = None
        return
    if modal:
        return   # 動かしている途中の変化は、その操作の一部
    if sig != S.seen_sig:
        if S.pending_since is None:
            S.pending_since = now
        S.seen_sig = sig
        S.pending_last = now
    if S.pending_last is not None and now - S.pending_last >= SETTLE_TIME:
        _settle()


def _settle():
    """落ち着いた数字の直しを確定する（元の値に戻っていたら数えない）。"""
    if S.pending_since is None:
        return
    if S.seen_sig != S.baseline_sig:
        cat, text, mod_type = _change_info(S.baseline_sig, S.seen_sig)
        ev = S.last_event
        tied = False
        if ev is not None and cat == ev["cat"]:
            changed_mod = S.seen_sig["mod"] != S.baseline_sig["mod"]
            changed_mat = S.seen_sig["mat"] != S.baseline_sig["mat"]
            if changed_mod and ev["id"] in TIE_MODIFIER_OPS and (not ev["mod_type"] or ev["mod_type"] == mod_type):
                tied = True
            elif changed_mat and ev["id"] in TIE_MATERIAL_OPS:
                tied = True
        if tied:
            _adjust_last(S.pending_last, "数字で直す")
        elif cat is not None:
            ja, _, en = text.partition("|")
            _add_event("数字の直し", ja, cat, S.pending_since, S.pending_last, name_en=en or ja)
    S.baseline_sig = S.seen_sig
    S.pending_since = S.pending_last = None


def _redraw_sidebars():
    try:
        for window in bpy.context.window_manager.windows:
            for area in window.screen.areas:
                if area.type == "VIEW_3D":
                    area.tag_redraw()
    except Exception:
        pass


def _resync(after_undo=True):
    S.prev_ops = _snapshot()
    S.last_op_props = _last_op_props()
    S.baseline_sig = S.seen_sig = _shape_sig()
    S.pending_since = S.pending_last = None
    S.after_undo = after_undo


@persistent
def _on_undo(*_args):
    """取り消しが起きたら、すぐには数えずに「取り消し待ち」にする。

    左下のパネルで数字を直すと、Blender は 1 回の処理の中で
    「取り消し → 新しい数字でやり直し」を行う。取り消しの直後の最初の確認で、
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
    pending, S.pending_undos = S.pending_undos, 0
    if not pending:
        return
    target, props = S.undo_target, _last_op_props()
    redone = False
    if target and props and props[1] == target[1] and classify(props[1]) not in (None, OTHER):
        undo_props = S.undo_props[3] if S.undo_props else None
        redone = _shape_sig() != S.undo_sig or props[3] != undo_props
    real = pending - 1 if redone else pending
    for _ in range(real):
        S.undo += 1
        _record("取り消し（command＋Z）")
    if redone:
        _adjust_last(_elapsed(), "左下のパネルで調整")
    _resync(after_undo=real > 0)


@persistent
def _on_redo(*_args):
    if S.running:
        _record("やり直し")
        _resync()


@persistent
def _on_load_pre(*_args):
    if S.running:
        _finish("（別のファイルを開いたため終了）")


@persistent
def _on_load_post(*_args):
    try:
        wm = bpy.context.window_manager
        if not wm.mslog_author:
            wm.mslog_author = _read_last_author()
    except Exception:
        pass


# ---------------------------------------------------------------- 作業部分の切り替え

def _close_part_time():
    now = time.monotonic()
    S.part_time[S.part] = S.part_time.get(S.part, 0.0) + (now - S.part_since)
    S.part_since = now


def _on_part_changed(wm, _context):
    if not S.running or wm.mslog_part == S.part:
        return
    try:
        _check()
        if S.pending_since is not None:
            _settle()
    except Exception:
        pass
    _close_part_time()
    old = PART_LABELS[S.part]
    S.part = wm.mslog_part
    _record(f"作業切替：{old} → {PART_LABELS[S.part]}")


# ---------------------------------------------------------------- 集計

def _totals(events, parts=None):
    """区分ごとの (時間, 回数)。"""
    t = {c: 0.0 for c in CATS}
    n = {c: 0 for c in CATS}
    for ev in events:
        if parts is not None and ev["part"] not in parts:
            continue
        n[ev["cat"]] += ev["count"]
        if ev["cat"] in TIMED:
            t[ev["cat"]] += max(0.0, ev["end"] - ev["start"])
    return t, n


def _live_totals():
    t, n = _totals(S.events)
    total = _elapsed()
    t[OTHER] = max(0.0, total - sum(t[c] for c in TIMED))
    return total, t, n


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
            obj.update_from_editmode()
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


# ---------------------------------------------------------------- 書き出し

def _output_dir():
    base = os.path.dirname(bpy.data.filepath) if bpy.data.filepath else os.path.expanduser("~")
    path = os.path.join(base, "操作記録")
    os.makedirs(path, exist_ok=True)
    return path


def _summary_header():
    head = ["記録日時", "制作者", "手法", "試行番号", "グラフに使う", "メモ", "制作時間(秒)"]
    for c in CATS:
        head += [f"{c}の時間(秒)", f"{c}の回数"]
    head += ["取り消し回数"]
    for k in PART_KEYS:
        p = PART_LABELS[k]
        head += [f"{p}の時間(秒)"]
        for c in CATS:
            head += [f"{p}_{c}の時間(秒)", f"{p}_{c}の回数"]
    head += ["面数", "部品の数", "穴の数", "高さ(mm)", "直径(mm)", "操作ログファイル", "ツールの版"]
    return head


def _read_text(path):
    with open(path, "rb") as f:
        raw = f.read()
    for enc in ("utf-8-sig", "cp932"):
        try:
            return raw.decode(enc), enc
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace"), "utf-8"


def _write_summary(values):
    """まとめ.csv に1行足す。Excel で列を並べ替えたり足したりしていても、見出しに合わせて書く。"""
    path = os.path.join(S.out_dir, "まとめ.csv")
    header = _summary_header()
    msg = ""
    if os.path.exists(path):
        try:
            text, enc = _read_text(path)
            first = next(csv.reader(io.StringIO(text)), [])
        except Exception:
            first, enc = [], "utf-8"
        if not set(header) <= set(first):
            # 前の版（v1）のまとめ.csv は、名前を変えて残す
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            keep = os.path.join(S.out_dir, f"まとめ_前の版_{stamp}.csv")
            shutil.move(path, keep)
            msg = f"前の版のまとめ.csvを「{os.path.basename(keep)}」に名前を変えて残しました"
        else:
            header = first
            if enc == "cp932":
                msg = "まとめ.csvが日本語の文字コード(Shift_JIS)で保存されていたので、そのまま書き足しました"
    row = [values.get(h, "") for h in header]
    try:
        is_new = not os.path.exists(path)
        if is_new:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                csv.writer(f).writerows([header, row])
        else:
            text, enc = _read_text(path)
            needs_nl = text and not text.endswith(("\n", "\r"))
            with open(path, "a", newline="", encoding="cp932" if enc == "cp932" else "utf-8") as f:
                if needs_nl:
                    f.write("\r\n")
                csv.writer(f).writerow(row)
    except Exception as exc:
        alt = os.path.join(S.out_dir, f"まとめ_書き込めなかった分_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv")
        with open(alt, "w", newline="", encoding="utf-8-sig") as f:
            csv.writer(f).writerows([_summary_header(), [values.get(h, "") for h in _summary_header()]])
        msg = f"まとめ.csvに書き込めませんでした（Excelで開いていませんか？）。「{os.path.basename(alt)}」に保存しました。{exc}"
    return msg


LOG_HEADER = ["番号", "開始(秒)", "確定(秒)", "最後に直した(秒)", "時間(秒)", "作業部分", "区分",
              "操作", "操作ID", "数字の直し(回)", "回数に数える", "操作(英語)"]


def _write_log(total):
    path = os.path.join(S.out_dir, S.log_name)
    rows = []
    items = [("ev", e["start"], e) for e in S.events] + [("rec", r["t"], r) for r in S.records]
    items.sort(key=lambda x: x[1])
    n = 0
    for kind, _t, item in items:
        n += 1
        if kind == "ev":
            dur = round(item["end"] - item["start"], 2) if item["cat"] in TIMED else ""
            rows.append([n, round(item["start"], 2), round(item["confirm"], 2), round(item["end"], 2), dur,
                         PART_LABELS[item["part"]], item["cat"], item["name"], item["id"],
                         item["adjust"], item["count"], item["name_en"]])
        else:
            rows.append([n, round(item["t"], 2), "", "", "", "", "記録", item["what"], "", "", 0, ""])
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(LOG_HEADER)
        w.writerows(rows)


# ---------------------------------------------------------------- 開始・終了

def _config_path():
    try:
        folder = bpy.utils.user_resource("CONFIG", create=True)
    except Exception:
        folder = os.path.expanduser("~")
    return os.path.join(folder, "mslog_last_author.txt")


def _read_last_author():
    try:
        with open(_config_path(), encoding="utf-8") as f:
            return f.read().strip()
    except Exception:
        return ""


def _save_last_author(name):
    try:
        with open(_config_path(), "w", encoding="utf-8") as f:
            f.write(name)
    except Exception:
        pass


def _start(context):
    wm = context.window_manager
    S.running = True
    S.start_time = time.monotonic()
    S.start_dt = datetime.now()
    S.author = wm.mslog_author.strip()
    S.method = METHOD_LABELS.get(wm.mslog_method, wm.mslog_method)
    S.trial = wm.mslog_trial
    S.note = wm.mslog_note
    S.part = "BODY"
    wm.mslog_part = "BODY"
    S.part_since = S.start_time
    S.part_time = {k: 0.0 for k in PART_KEYS}
    S.events, S.records = [], []
    S.last_event = None
    S.undo = S.pending_undos = 0
    S.modal_ignore = set(_modal_ids())
    S.modal_start = S.modal_last = None
    S.message = ""
    S.out_dir = _output_dir()
    stamp = S.start_dt.strftime("%Y%m%d_%H%M%S")
    S.log_name = f"操作ログ_{S.method}_試行{S.trial}_{stamp}.csv"
    _save_last_author(S.author)
    _resync(after_undo=False)
    _record("記録開始")
    for handlers, func in ((bpy.app.handlers.undo_post, _on_undo),
                           (bpy.app.handlers.redo_post, _on_redo)):
        if func not in handlers:
            handlers.append(func)
    bpy.app.timers.register(_poll, first_interval=POLL_INTERVAL)


def _finish(note_suffix="", context=None):
    context = context or bpy.context
    try:
        if S.pending_undos:
            _resolve_undo()
        _check()
        if S.pending_since is not None:
            _settle()
    except Exception:
        pass
    _close_part_time()
    S.running = False
    total = _elapsed()
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
    _record("記録終了" + note_suffix)

    v = {"記録日時": S.start_dt.strftime("%Y-%m-%d %H:%M:%S"), "制作者": S.author, "手法": S.method,
         "試行番号": S.trial, "グラフに使う": "○", "メモ": S.note + note_suffix,
         "制作時間(秒)": round(total, 2), "取り消し回数": S.undo}
    t, n = _totals(S.events)
    t[OTHER] = max(0.0, total - sum(t[c] for c in TIMED))
    for c in CATS:
        v[f"{c}の時間(秒)"], v[f"{c}の回数"] = round(t[c], 2), n[c]
    for k in PART_KEYS:
        p = PART_LABELS[k]
        pt = S.part_time.get(k, 0.0)
        tt, nn = _totals(S.events, parts={k})
        tt[OTHER] = max(0.0, pt - sum(tt[c] for c in TIMED))
        v[f"{p}の時間(秒)"] = round(pt, 2)
        for c in CATS:
            v[f"{p}_{c}の時間(秒)"], v[f"{p}_{c}の回数"] = round(tt[c], 2), nn[c]
    v.update({"面数": stats["faces"], "部品の数": stats["islands"], "穴の数": stats["holes"],
              "高さ(mm)": stats["height"], "直径(mm)": stats["diameter"],
              "操作ログファイル": S.log_name, "ツールの版": VERSION})
    _write_log(total)
    S.message = _write_summary(v)
    return total, stats


# ---------------------------------------------------------------- グラフ

VIEWER_HTML = r'''<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Modeling Analytics</title>
<style>
.viz-root{
  color-scheme: light;
  --surface-0:#FFFFFF; --surface-1:#ffffff; --surface-2:#f5f7fa; --line:#e1e4e8; --grid:#eef0f3;
  --ink:#141413; --ink-2:#5b5a55; --ink-3:#7d776b;
  --c1:#2a78d6; --c2:#eb6834; --c3:#1baf7a; --c4:#d6d4cd;
  --accent:#185ABD; --accent-ink:#ffffff; --olive:#185ABD; --deep:#185ABD; --soft:#E8F0FB;
  --shadow:0 1px 2px rgba(16,24,40,.04),0 4px 14px rgba(16,24,40,.05);
}
@media (prefers-color-scheme: dark){
  :root:where(:not([data-theme="light"])) .viz-root{
    color-scheme: dark;
    --surface-0:#111110; --surface-1:#1a1a19; --surface-2:#161615; --line:#2b2b29; --grid:#232321;
    --ink:#f2f1ec; --ink-2:#bdbcb3; --ink-3:#7f7e78;
    --c1:#3987e5; --c2:#d95926; --c3:#199e70; --c4:#4a4945;
    --accent:#3b7ddd; --accent-ink:#ffffff; --olive:#8db8f5; --deep:#3b7ddd; --soft:#1e2a3d; --shadow:none;
  }
}
:root[data-theme="dark"] .viz-root{
  color-scheme: dark;
  --surface-0:#111110; --surface-1:#1a1a19; --surface-2:#161615; --line:#2b2b29; --grid:#232321;
  --ink:#f2f1ec; --ink-2:#bdbcb3; --ink-3:#7f7e78;
  --c1:#3987e5; --c2:#d95926; --c3:#199e70; --c4:#4a4945;
  --accent:#3b7ddd; --accent-ink:#ffffff; --olive:#8db8f5; --deep:#3b7ddd; --soft:#1e2a3d; --shadow:none;
}
*{box-sizing:border-box}
body{margin:0;background:#FFFFFF;font:14px/1.6 "Hiragino Sans","Hiragino Kaku Gothic ProN","Yu Gothic","Noto Sans CJK JP",system-ui,sans-serif;
  -webkit-font-smoothing:antialiased}
@media (prefers-color-scheme: dark){body{background:#111110}}
.viz-root{background:var(--surface-0);color:var(--ink);min-height:100vh}
.wrap{max-width:1200px;margin:0 auto;padding:40px 24px 64px}
.num{font-variant-numeric:tabular-nums;letter-spacing:-.01em}

/* ヘッダー */
header{display:flex;align-items:flex-end;justify-content:space-between;gap:16px;flex-wrap:wrap;padding-bottom:22px;border-bottom:1.5px solid var(--deep)}
.over{font-size:11px;letter-spacing:.18em;text-transform:uppercase;color:var(--olive);margin:0 0 8px;font-weight:700}
h1{font-size:30px;line-height:1.15;margin:0;font-weight:700;letter-spacing:-.01em}
.sub{margin:6px 0 0;color:var(--ink-2);font-size:13px}
.tools{display:flex;gap:10px;align-items:center}
.pill{display:inline-flex;background:var(--surface-1);border:1px solid var(--line);border-radius:999px;padding:3px}
.pill button{border:0;background:transparent;color:var(--ink-2);font:inherit;font-size:12.5px;font-weight:600;padding:6px 14px;border-radius:999px;cursor:pointer}
.pill button.on{background:var(--accent);color:var(--accent-ink);font-weight:700}
.ghost{border:1.5px solid var(--deep);background:var(--surface-1);color:var(--olive);border-radius:999px;padding:8px 16px;font:inherit;font-size:12.5px;font-weight:600;cursor:pointer}
.ghost:hover{background:var(--soft)}
.status{font-size:12px;color:var(--ink-3);margin:10px 0 0}
body.dragging .viz-root{outline:2px dashed var(--olive);outline-offset:-10px}

/* 手法ごとのサマリー */
.summary{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:16px;margin:28px 0 22px}
.tile{background:var(--surface-1);border:1px solid var(--line);border-radius:4px;padding:18px 20px 16px;box-shadow:var(--shadow)}
.tile .m{font-size:13px;font-weight:700;color:var(--olive);margin:0}
.tile .big{font-size:34px;font-weight:700;margin:6px 0 2px;line-height:1.1}
.tile .big small{font-size:14px;font-weight:600;color:var(--ink-3);margin-left:4px}
.tile .meta{font-size:12px;color:var(--ink-3);margin:0 0 12px}
.bar{display:flex;height:8px;border-radius:999px;overflow:hidden;gap:2px;background:var(--surface-2)}
.bar i{display:block;height:100%}
.tile .none{color:var(--ink-3);font-size:13px;padding:22px 0}

/* 切り替え */
.filters{display:flex;gap:12px 22px;flex-wrap:wrap;align-items:center;margin:0 0 18px}
.filters .f{display:flex;align-items:center;gap:8px}
.filters .lab{font-size:11px;letter-spacing:.08em;color:var(--olive);font-weight:700;text-transform:uppercase}
.legend{display:flex;gap:18px;flex-wrap:wrap;font-size:12.5px;color:var(--ink-2);margin:0 0 16px}
.legend span{display:inline-flex;align-items:center;gap:7px}
.sw{width:10px;height:10px;border-radius:3px;display:inline-block}

/* カード */
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:16px}
.card{background:var(--surface-1);border:1px solid var(--line);border-radius:4px;padding:20px 22px 16px;min-width:0;box-shadow:var(--shadow)}
.card .no{font-size:11px;font-weight:800;letter-spacing:.14em;color:var(--olive)}
.card h2{font-size:16px;margin:2px 0 2px;font-weight:700}
.card p.desc{margin:0 0 10px;font-size:12px;color:var(--ink-2)}
.wide{grid-column:1/-1}
.head{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;flex-wrap:wrap}
.pill.sm button{font-size:11.5px;padding:5px 12px}
.note{font-size:11.5px;color:var(--ink-3);margin:10px 0 0}
tr.group td{color:var(--ink);font-weight:700;padding-top:16px;border-bottom:1px solid var(--line)}
.empty{color:var(--ink-3);font-size:13px;padding:28px 0;text-align:center}
svg text{fill:var(--ink-3);font-size:11.5px;font-family:inherit}
svg .val{fill:var(--ink);font-size:12px;font-weight:700}
svg .cat{fill:var(--ink);font-size:12.5px;font-weight:700}
table{width:100%;border-collapse:collapse;font-size:13px}
th,td{padding:9px 10px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
th:first-child,td:first-child{text-align:left}
thead th{color:var(--ink-3);font-weight:700;font-size:11.5px;letter-spacing:.04em}
tbody tr:last-child td{border-bottom:0}
td.k{color:var(--ink-2)}
.tbl{overflow-x:auto}
.tip{position:fixed;pointer-events:none;background:#323130;color:#fff;border-radius:10px;
  padding:8px 12px;font-size:12px;line-height:1.5;display:none;z-index:9}
@media (max-width:860px){.grid,.summary{grid-template-columns:1fr} h1{font-size:24px}}
</style>
</head>
<body>
<div class="viz-root"><div class="wrap">
<header>
  <div>
    <p class="over" data-t="over"></p>
    <h1 data-t="title"></h1>
    <p class="sub" data-t="subtitle"></p>
  </div>
  <div class="tools">
    <span class="pill" id="lang"><button data-l="ja">日本語</button><button data-l="en">English</button></span>
    <label class="ghost"><span data-t="add"></span><input id="pick" type="file" webkitdirectory multiple hidden></label>
  </div>
</header>
<div class="status num" id="status"></div>

<div class="summary" id="summary"></div>
<div class="filters" id="filters"></div>
<div class="legend" id="legend"></div>

<div class="grid">
  <div class="card wide"><div class="head"><div><div class="no">01</div><h2 data-t="g1"></h2><p class="desc" data-t="g1d"></p></div><span class="pill sm" id="o1"></span></div><div id="g1"></div></div>
  <div class="card wide"><div class="head"><div><div class="no">02</div><h2 data-t="g2"></h2><p class="desc" data-t="g2d"></p></div><span class="pill sm" id="o2"></span></div><div id="g2"></div></div>
  <div class="card wide"><div class="head"><div><div class="no">03</div><h2 data-t="g3"></h2><p class="desc" id="s3"></p></div><span class="pill sm" id="o3"></span></div><div id="g3"></div></div>
  <div class="card wide"><div class="no">04</div><h2 data-t="g4"></h2><p class="desc" data-t="g4d"></p><div id="g4"></div></div>
  <div class="card wide"><h2 data-t="tbl"></h2><div class="tbl num" id="tbl"></div></div>
  <div class="card wide"><h2 data-t="oth"></h2><p class="desc" id="osub"></p><div class="tbl num" id="other"></div></div>
</div>
</div></div>
<div class="tip" id="tip"></div>

<script id="embedded" type="application/json">/*__DATA__*/null</script>
<script>
"use strict";
// ---------------------------------------------------------------- ことば（日本語・英語）
const I18N = {
  ja: { over:"Blender · Modeling Analytics", title:"モデリング操作グラフ", subtitle:"取手付きコップを3つの手法で作ったときの、操作の時間と回数",
    add:"＋ データを追加", g1:"作業の種類ごとの時間", g1d:"手法ごとに、どの作業に時間がかかっているか（縦の目盛りは3つの手法で共通・分）",
    g2:"作業の種類ごとの回数", g2d:"手法ごとに、どの作業を何回しているか（縦の目盛りは3つの手法で共通・回）",
    g3:"合計時間の比較", g3all:"棒の高さ＝制作時間の合計（分）。色は作業の種類の内訳", g3oth:"棒の高さ＝3種類（形を変える・面を増やす・滑らかにする）の時間の合計（分）。その他は含まない",
    showOther:"その他も表示", hideOther:"3種類だけ", tabAll:"全体", tabOther:"3種類の合計",
    perGroup:"1回あたりの時間（目安）", perNote:"※ 1回あたりの時間＝時間 ÷ 回数。押した瞬間に終わって数字も直していない操作（0秒）は除いています。操作によって1回の重さが違うため、手法どうしの比較ではなく、同じ人の慣れや初心者とプロの差を見る目安です。", g4:"時系列", g4d:"制作の始めから終わりまで、どの種類の操作をしていたか（横軸：分）",
    tbl:"数字の表", oth:"「その他」に入った操作", othd:"区分の入れ間違いがないかの確認用", sum:"（記録の合計）",
    part:"部分", view:"表示", kind:"①②に出す種類", author:"制作者", avg:"平均", trial:n=>`試行${n}`,
    all:"すべて", three:"3種類だけ", h1all:"棒の高さ＝制作時間の合計（分）", h2all:"棒の高さ＝操作回数の合計（回）",
    h1:k=>`棒の高さ＝${k}の時間（分）`, h2:k=>`棒の高さ＝${k}の回数（回）`, threeName:"3種類の合計",
    none:"記録なし", noRec:"記録がありません", t4avg:"上の「表示」で試行を1つ選ぶと表示されます（平均では順番を出せないため）",
    noLog:"操作ログが見つかりません", records:n=>`${n}件`, total:"制作時間", ops:"操作", undo:"取り消し回数", faces:"面の数", height:"高さ", diam:"直径", islands:"部品の数",
    count:"記録の数", timeOf:k=>`${k}の時間`, numOf:k=>`${k}の回数`, per:k=>`${k}：1回あたり`, partTime:p=>`${p}の時間`,
    loaded:(n,ex)=>`${n}件の記録を読み込みました`+(ex?`（「グラフに使う」が×の${ex}件は除いています）`:""), empty:"まだデータがありません。「＋ データを追加」から操作記録フォルダを選ぶか、この画面にドラッグしてください",
    tileMeta:(n,c)=>`操作 ${c}回 ・ ${n}`, sec:"秒", times:"回",
    fmt:s=>{const r=Math.round(s);return `${Math.floor(r/60)}分${String(r%60).padStart(2,"0")}秒`;}, big:s=>{const r=Math.round(s);return [`${Math.floor(r/60)}:${String(r%60).padStart(2,"0")}`,""];} },
  en: { over:"Blender · Modeling Analytics", title:"Modeling Operation Analytics", subtitle:"Time and number of operations for a handled cup built with three methods",
    add:"+ Add data", g1:"Time by operation type", g1d:"Where the time goes within each method (shared y-axis across methods, min)",
    g2:"Number of operations by type", g2d:"How many operations of each type within each method (shared y-axis)",
    g3:"Total time comparison", g3all:"Bar height = total production time (min), colored by operation type", g3oth:"Bar height = total time of the three operation types (min), excluding Other",
    showOther:"Include Other", hideOther:"Three types", tabAll:"Overall", tabOther:"Three types",
    perGroup:"Time per operation (reference)", perNote:"* Time per operation = time ÷ count, excluding instant operations with no value edits (0 s). Because operations differ in weight, use this to compare a person’s proficiency (e.g., novice vs. expert) rather than methods.", g4:"Timeline", g4d:"Which type of operation was performed from start to finish (x-axis: min)",
    tbl:"Data table", oth:"Operations classified as “Other”", othd:"For checking the classification", sum:" (total of records)",
    part:"Part", view:"View", kind:"Types in 01–02", author:"Modeler", avg:"Average", trial:n=>`Trial ${n}`,
    all:"All", three:"Three types", h1all:"Bar height = total production time (min)", h2all:"Bar height = total number of operations",
    h1:k=>`Bar height = time of ${k} (min)`, h2:k=>`Bar height = number of ${k} operations`, threeName:"the three types",
    none:"No data", noRec:"No records", t4avg:"Select a single trial under “View” to show the timeline (order cannot be averaged)",
    noLog:"Operation log not found", records:n=>`${n} record${n>1?"s":""}`, total:"Production time", ops:"Operation", undo:"Undo count", faces:"Faces", height:"Height", diam:"Diameter", islands:"Parts",
    count:"Records", timeOf:k=>`Time: ${k}`, numOf:k=>`Count: ${k}`, per:k=>`Per operation: ${k}`, partTime:p=>`Time: ${p}`,
    loaded:(n,ex)=>`Loaded ${n} record${n>1?"s":""}`+(ex?` (${ex} marked × excluded)`:""), empty:"No data yet. Use “+ Add data” to choose the 操作記録 folder, or drop it on this page",
    tileMeta:(n,c)=>`${c} operations · ${n}`, sec:"s", times:"",
    fmt:s=>{const r=Math.round(s);return `${Math.floor(r/60)}m ${String(r%60).padStart(2,"0")}s`;}, big:s=>{const r=Math.round(s);return [`${Math.floor(r/60)}:${String(r%60).padStart(2,"0")}`,""];} },
};
const NAMES = {
  method:{ "①円から押し出し":"① Extrude & Solidify", "②回転体":"② Spin", "③円柱をくぼませる":"③ Inset & Extrude", "その他":"Other" },
  cat:{ "形を変える":"Transform", "面を増やす":"Add Geometry", "滑らかにする":"Smooth", "その他":"Other" },
  part:{ "全体":"Overall", "本体":"Body", "取手":"Handle", "つなぎ・全体":"Joining" },
};
let lang = "ja";
try { lang = localStorage.getItem("mslog_lang") || "ja"; } catch(e){}
const L = () => I18N[lang];
const nm = (kind, ja) => lang==="en" ? (NAMES[kind][ja] || ja) : (kind==="part" && ja==="つなぎ・全体" ? "つなぎ" : ja);

const KNOWN = ["①円から押し出し","②回転体","③円柱をくぼませる"];
const K = ["形を変える","面を増やす","滑らかにする","その他"];
const C = ["var(--c1)","var(--c2)","var(--c3)","var(--c4)"];
const PARTS = ["全体","本体","取手","つなぎ・全体"];
const NS = "http://www.w3.org/2000/svg";
const tip = document.getElementById("tip");

// ---------------------------------------------------------------- CSV
function parseCSV(text){
  text = text.replace(/^﻿/,"");
  const rows=[]; let row=[], f="", q=false;
  for(let i=0;i<text.length;i++){
    const ch=text[i];
    if(q){ if(ch==='"'){ if(text[i+1]==='"'){f+='"';i++;} else q=false; } else f+=ch; }
    else if(ch==='"') q=true;
    else if(ch===','){ row.push(f); f=""; }
    else if(ch==='\n'||ch==='\r'){ if(ch==='\r'&&text[i+1]==='\n') i++; row.push(f); rows.push(row); row=[]; f=""; }
    else f+=ch;
  }
  if(f!==""||row.length){ row.push(f); rows.push(row); }
  const head=rows.shift()||[];
  return rows.filter(r=>r.some(x=>x.trim()!=="")).map(r=>Object.fromEntries(head.map((h,i)=>[h.trim(),(r[i]??"").trim()])));
}
const num = v => { const x=parseFloat(String(v??"").replace(/,/g,"")); return isFinite(x)?x:0; };
const excluded = v => /^(×|x|✕|✖|ｘ|no|いいえ|使わない)$/i.test(String(v||"").trim());

// ---------------------------------------------------------------- データ
const store = { recs: [], logs: {} };
function addFolder(summaryText, logs, folder){
  const rows = parseCSV(summaryText);
  let added=0, old=0;
  for(const r of rows){
    if(!("形を変えるの時間(秒)" in r)){ old++; continue; }
    const key=[r["記録日時"],r["制作者"],r["手法"],r["試行番号"],r["制作時間(秒)"]].join("|");
    const rec = { key, date:r["記録日時"], author:r["制作者"]||"—", method:r["手法"]||"その他", trial:parseInt(r["試行番号"])||0,
      use:!excluded(r["グラフに使う"]), undo:num(r["取り消し回数"]), faces:r["面数"], islands:r["部品の数"], height:r["高さ(mm)"], diameter:r["直径(mm)"],
      logKey: folder+"/"+(r["操作ログファイル"]||"").normalize("NFC"), parts:{} };
    rec.parts["全体"] = { time:num(r["制作時間(秒)"]), t:K.map(k=>num(r[k+"の時間(秒)"])), n:K.map(k=>num(r[k+"の回数"])) };
    for(const p of PARTS.slice(1)) rec.parts[p] = { time:num(r[p+"の時間(秒)"]), t:K.map(k=>num(r[p+"_"+k+"の時間(秒)"])), n:K.map(k=>num(r[p+"_"+k+"の回数"])) };
    const i = store.recs.findIndex(x=>x.key===key);
    if(i>=0) store.recs[i]=rec; else { store.recs.push(rec); added++; }
  }
  for(const [name,text] of Object.entries(logs)) store.logs[folder+"/"+name.normalize("NFC")]=parseCSV(text);
  return {added, old};
}
let folderSeq = 0;
async function loadFiles(files){
  const byDir = {};
  for(const f of files){
    const rel = (f.webkitRelativePath || f.relPath || f.name).normalize("NFC");
    const parts = rel.split("/"); const name = parts.pop(); const dir = parts.join("/") || "-";
    if(!/\.csv$/i.test(name)) continue;
    (byDir[dir] ||= {summary:null, logs:{}});
    if(name==="まとめ.csv") byDir[dir].summary=f; else if(name.startsWith("操作ログ_")) byDir[dir].logs[name]=f;
  }
  for(const g of Object.values(byDir)){
    if(!g.summary) continue;
    const logs={}; for(const [n,f] of Object.entries(g.logs)) logs[n]=await readText(f);
    addFolder(await readText(g.summary), logs, "f"+(++folderSeq));
  }
  buildAll();
}
function readText(file){
  return file.arrayBuffer().then(buf=>{ try { return new TextDecoder("utf-8",{fatal:true}).decode(buf); } catch(e){ return new TextDecoder("shift_jis").decode(buf); } });
}
// 画面のどこにでもドラッグできる
document.addEventListener("dragover",e=>{e.preventDefault();document.body.classList.add("dragging");});
document.addEventListener("dragleave",e=>{ if(!e.relatedTarget) document.body.classList.remove("dragging"); });
document.addEventListener("drop",async e=>{
  e.preventDefault(); document.body.classList.remove("dragging");
  const out=[]; const items=[...e.dataTransfer.items].map(i=>i.webkitGetAsEntry&&i.webkitGetAsEntry()).filter(Boolean);
  async function walk(entry,path){
    if(entry.isFile){ const f=await new Promise((res,rej)=>entry.file(res,rej)); f.relPath=path+entry.name; out.push(f); }
    else if(entry.isDirectory){ const reader=entry.createReader(); let batch;
      do{ batch=await new Promise((res,rej)=>reader.readEntries(res,rej)); for(const c of batch) await walk(c,path+entry.name+"/"); }while(batch.length); }
  }
  if(items.length){ for(const it of items) await walk(it,""); } else out.push(...e.dataTransfer.files);
  loadFiles(out);
});
document.getElementById("pick").addEventListener("change",e=>loadFiles([...e.target.files]));

// ---------------------------------------------------------------- 切り替え
const sel = { part:"全体", view:"平均", author:null, other1:false, other2:false, tab3:"all" };
function pill(label, key, options){
  const wrap=document.createElement("div"); wrap.className="f";
  wrap.innerHTML=`<span class="lab">${label}</span>`;
  const seg=document.createElement("span"); seg.className="pill";
  for(const [v,text] of options){
    const b=document.createElement("button"); b.textContent=text; if(String(sel[key])===String(v)) b.className="on";
    b.onclick=()=>{ sel[key]=v; if(key==="author") sel.view="平均"; buildAll(); };
    seg.appendChild(b);
  }
  wrap.appendChild(seg); return wrap;
}
const usable = () => store.recs.filter(r=>r.use);
const authors = () => [...new Set(usable().map(r=>r.author))];
function methods(){ const found=[...new Set(usable().map(r=>r.method))]; return [...KNOWN, ...found.filter(m=>!KNOWN.includes(m))]; }
function buildFilters(){
  const a=authors(); if(!a.includes(sel.author)) sel.author=a[0]??null;
  const trials=[...new Set(usable().filter(r=>r.author===sel.author).map(r=>r.trial))].sort((x,y)=>x-y);
  if(sel.view!=="平均" && !trials.includes(sel.view)) sel.view="平均";
  const box=document.getElementById("filters"); box.innerHTML="";
  box.append(
    pill(L().part,"part",PARTS.map(p=>[p,nm("part",p)])),
    pill(L().view,"view",[["平均",L().avg],...trials.map(t=>[t,L().trial(t)])]),
    pill(L().author,"author",a.length?a.map(x=>[x,x]):[[null,"—"]])
  );
  document.getElementById("legend").innerHTML = K.map((k,i)=>`<span><i class="sw" style="background:${C[i]}"></i>${nm("cat",k)}</span>`).join("");
}
function pick(method){
  const rs=usable().filter(r=>r.author===sel.author && r.method===method);
  const p=sel.part;
  if(sel.view==="平均"){
    if(!rs.length) return null;
    const avg=f=>rs.reduce((s,r)=>s+f(r),0)/rs.length;
    return { n:rs.length, recs:rs, time:avg(r=>r.parts[p].time), t:K.map((_,i)=>avg(r=>r.parts[p].t[i])), c:K.map((_,i)=>avg(r=>r.parts[p].n[i])),
      undo:avg(r=>r.undo), faces:avg(r=>num(r.faces)), islands:avg(r=>num(r.islands)), height:avg(r=>num(r.height)), diameter:avg(r=>num(r.diameter)) };
  }
  const r=rs.filter(r=>r.trial===sel.view).sort((x,y)=>String(y.date).localeCompare(String(x.date)))[0]; if(!r) return null;
  const q=r.parts[p];
  return { n:1, recs:[r], rec:r, time:q.time, t:q.t, c:q.n, undo:r.undo, faces:num(r.faces), islands:num(r.islands), height:num(r.height), diameter:num(r.diameter) };
}

// ---------------------------------------------------------------- 描画の道具
function el(t,a,p){const e=document.createElementNS(NS,t);for(const k in a)e.setAttribute(k,a[k]);if(p)p.appendChild(e);return e;}
function hover(e,html){
  e.addEventListener("mousemove",ev=>{tip.innerHTML=html;tip.style.display="block";
    tip.style.left=Math.min(ev.clientX+14, innerWidth-tip.offsetWidth-8)+"px"; tip.style.top=(ev.clientY+14)+"px";});
  e.addEventListener("mouseleave",()=>tip.style.display="none");
}
const fmt = s => L().fmt(s);
const fmtN = v => (Math.round(v*10)/10).toString().replace(/\.0$/,"")+L().times;
function niceStep(max, target=5){ if(max<=0) return 1; const raw=max/target, p=Math.pow(10,Math.floor(Math.log10(raw)));
  for(const m of [1,2,2.5,5,10]) if(raw<=m*p) return m*p; return 10*p; }
const empty = (id,text) => document.getElementById(id).innerHTML=`<div class="empty">${text}</div>`;
const shortM = m => lang==="en" ? (NAMES.method[m]||m) : (m==="①円から押し出し"?"①押し出し":m==="③円柱をくぼませる"?"③くぼませる":m);

// サマリー
function summary(){
  const box=document.getElementById("summary");
  box.innerHTML = KNOWN.map(m=>{
    const v=pick(m);
    if(!v) return `<div class="tile"><p class="m">${nm("method",m)}</p><div class="none">${L().none}</div></div>`;
    const tot=v.t.reduce((a,b)=>a+b,0)||1, cnt=v.c.reduce((a,b)=>a+b,0);
    const [big]=L().big(v.time);
    const label = sel.view==="平均" ? (lang==="en"?`${L().avg} of ${L().records(v.n)}`:`${L().records(v.n)}の${L().avg}`) : L().trial(sel.view);
    return `<div class="tile"><p class="m">${nm("method",m)}</p><p class="big num">${big}<small>${lang==="en"?"min":"分"}</small></p>
      <p class="meta num">${L().tileMeta(label, Math.round(cnt))}</p>
      <div class="bar">${v.t.map((x,i)=>x>0?`<i style="width:${x/tot*100}%;background:${C[i]}"></i>`:"").join("")}</div></div>`;
  }).join("");
}

// カードの右上の切り替え
function cardPill(id, key, options){
  const box=document.getElementById(id); box.innerHTML="";
  for(const [v,text] of options){ const b=document.createElement("button"); b.textContent=text; if(sel[key]===v) b.className="on";
    b.onclick=()=>{ sel[key]=v; buildAll(); }; box.appendChild(b); }
}

// 01 02 手法ごとに、作業の種類を横に並べる（先生の形）
function byType(id, unit, withOther){
  const ms=methods(); const vals=ms.map(m=>pick(m));
  if(vals.every(v=>!v)) return empty(id,L().noRec);
  const ks = withOther?[0,1,2,3]:[0,1,2];
  const get=(v,k)=> unit==="min"? v.t[k] : v.c[k];
  const maxRaw=Math.max(unit==="min"?60:5, ...vals.filter(Boolean).flatMap(v=>ks.map(k=>get(v,k))));
  const step=unit==="min"? Math.max(60,niceStep(maxRaw/60,4)*60) : niceStep(maxRaw,4);
  const max=Math.ceil(maxRaw*1.12/step)*step;
  const W=1100,H=300,Lp=40,B=44,top=40; const box=document.getElementById(id); box.innerHTML="";
  const svg=el("svg",{viewBox:`0 0 ${W} ${H}`,width:"100%",role:"img"},box);
  const y=v=>top+(H-top-B)*(1-v/max);
  const pw=(W-Lp)/ms.length, gap=28;
  for(let v=0;v<=max+1e-9;v+=step){
    el("text",{x:Lp-8,y:y(v)+4,"text-anchor":"end",class:"num"},svg).textContent=unit==="min"?Math.round(v/60*10)/10:Math.round(v*10)/10;
    ms.forEach((_,i)=>el("line",{x1:Lp+i*pw+(i?gap/2:0),x2:Lp+(i+1)*pw-gap/2,y1:y(v),y2:y(v),stroke:v===0?"var(--line)":"var(--grid)"},svg));
  }
  const lab = unit==="min"?fmt:fmtN;
  vals.forEach((v,i)=>{
    const x0=Lp+i*pw+(i?gap/2:0), w=pw-gap/2-(i?gap/2:0);
    el("text",{x:x0+w/2,y:16,"text-anchor":"middle",class:"cat"},svg).textContent=nm("method",ms[i]);
    if(!v){ el("text",{x:x0+w/2,y:y(0)-10,"text-anchor":"middle"},svg).textContent=L().none; return; }
    const slot=w/ks.length, bw=Math.min(62,slot*0.62);
    ks.forEach((k,j)=>{ const val=get(v,k), x=x0+j*slot+(slot-bw)/2;
      const r=el("rect",{x,y:y(val),width:bw,height:Math.max(y(0)-y(val),0.5),fill:C[k],rx:5},svg);
      if(y(0)-y(val)>5) el("rect",{x,y:y(val)+5,width:bw,height:y(0)-y(val)-5,fill:C[k]},svg).style.pointerEvents="none";
      hover(r,`<b>${nm("method",ms[i])}</b><br>${nm("cat",K[k])}：${lab(val)}`);
      el("text",{x:x+bw/2,y:y(val)-7,"text-anchor":"middle",class:"val num"},svg).textContent=lab(val);
      el("text",{x:x+bw/2,y:H-22,"text-anchor":"middle"},svg).textContent=nm("cat",K[k]);
    });
  });
}

// 03 合計時間の比較（全体＝4色の積み上げ／その他だけ）
function totals(){
  const id="g3"; const onlyOther = sel.tab3==="other";
  document.getElementById("s3").textContent = onlyOther? L().g3oth : L().g3all;
  const ms=methods(); const vals=ms.map(m=>pick(m));
  if(vals.every(v=>!v)) return empty(id,L().noRec);
  const keep = onlyOther?[0,1,2]:[0,1,2,3];
  const data=vals.map(v=>v? K.map((_,k)=>keep.includes(k)?v.t[k]:0) : null);
  const W=1100,H=260,Lp=40,B=36,top=26; const n=ms.length; const slot=(W-Lp-12)/n; const bw=Math.min(90,slot*0.36);
  const box=document.getElementById(id); box.innerHTML="";
  const svg=el("svg",{viewBox:`0 0 ${W} ${H}`,width:"100%",role:"img"},box);
  const tot=data.map(r=>r?r.reduce((a,b)=>a+b,0):0);
  const maxRaw=Math.max(...tot,60); const step=Math.max(60,niceStep(maxRaw/60,4)*60);
  const max=Math.ceil(maxRaw*1.12/step)*step; const y=v=>top+(H-top-B)*(1-v/max);
  for(let v=0;v<=max+1e-9;v+=step){el("line",{x1:Lp,x2:W,y1:y(v),y2:y(v),stroke:v===0?"var(--line)":"var(--grid)"},svg);
    el("text",{x:Lp-8,y:y(v)+4,"text-anchor":"end",class:"num"},svg).textContent=Math.round(v/60*10)/10;}
  data.forEach((r,i)=>{const x=Lp+6+i*slot+(slot-bw)/2;
    el("text",{x:x+bw/2,y:H-10,"text-anchor":"middle"},svg).textContent=nm("method",ms[i]);
    if(!r){ el("text",{x:x+bw/2,y:y(0)-8,"text-anchor":"middle"},svg).textContent=L().none; return; }
    let acc=0; const order=[0,1,2,3].filter(k=>r[k]>0); const lastK=order[order.length-1];
    order.forEach(k=>{const v=r[k]; const y0=y(acc+v), h=y(acc)-y(acc+v)-(k===lastK?0:2); acc+=v;
      const rc=el("rect",{x,y:y0,width:bw,height:Math.max(h,0.5),fill:C[k],rx:k===lastK?5:0},svg);
      if(k===lastK && h>5) el("rect",{x,y:y0+5,width:bw,height:Math.max(h-5,0),fill:C[k]},svg).style.pointerEvents="none";
      hover(rc,`<b>${nm("method",ms[i])}</b><br>${nm("cat",K[k])}：${fmt(v)}`);});
    el("text",{x:x+bw/2,y:y(tot[i])-8,"text-anchor":"middle",class:"val num"},svg).textContent=fmt(tot[i]);
  });
}

// 1回あたりの時間（操作ログがあれば、0秒の操作を除いて計算）
function perOpValues(v){
  const res=[null,null,null];
  const parts = sel.part==="全体"?null:sel.part;
  const logs=v.recs.map(r=>store.logs[r.logKey]);
  if(logs.every(Boolean)){
    for(let k=0;k<3;k++){ let t=0,c=0;
      for(const log of logs) for(const e of log){ if(e["区分"]!==K[k]) continue; if(parts && e["作業部分"]!==parts) continue;
        const d=num(e["時間(秒)"]); if(d<=0 && num(e["数字の直し(回)"])===0) continue; t+=d; c+=1; }
      res[k]= c? t/c : null; }
    return res;
  }
  return [0,1,2].map(k=>v.c[k]>0? v.t[k]/v.c[k] : null);
}

// ④ 時系列
function timeline(){
  if(sel.view==="平均") return empty("g4",L().t4avg);
  const ms=methods(); const rows=ms.map(m=>({m, v:pick(m)})).filter(x=>x.v);
  if(!rows.length) return empty("g4",L().noRec);
  const logs=rows.map(x=>store.logs[x.v.rec.logKey]);
  if(logs.every(l=>!l)) return empty("g4",L().noLog);
  const W=1100,rowH=30,Lp=130,top=8,gapY=20; const H=top+rows.length*(rowH+gapY)+24;
  const box=document.getElementById("g4"); box.innerHTML="";
  const svg=el("svg",{viewBox:`0 0 ${W} ${H}`,width:"100%",role:"img"},box);
  const maxT=Math.max(...rows.map(x=>x.v.rec.parts["全体"].time),60); const step=Math.max(60,niceStep(maxT/60,10)*60);
  const x=t=>Lp+(W-Lp-6)*t/maxT;
  for(let t=0;t<=maxT+1e-9;t+=step){el("line",{x1:x(t),x2:x(t),y1:top,y2:H-30,stroke:"var(--grid)"},svg);
    el("text",{x:x(t),y:H-10,"text-anchor":"middle",class:"num"},svg).textContent=Math.round(t/60*10)/10;}
  rows.forEach((row,i)=>{const y0=top+i*(rowH+gapY); const log=logs[i];
    el("text",{x:0,y:y0+rowH/2+4,class:"cat"},svg).textContent=shortM(row.m);
    el("rect",{x:x(0),y:y0,width:x(row.v.rec.parts["全体"].time)-x(0),height:rowH,fill:"var(--c4)",rx:6},svg);
    if(!log) return;
    for(const e of log){
      const k=K.indexOf(e["区分"]); if(k<0||k>2) continue;
      if(sel.part!=="全体" && e["作業部分"]!==sel.part) continue;
      const s=num(e["開始(秒)"]), en=num(e["最後に直した(秒)"]);
      const name = lang==="en" ? (e["操作(英語)"]||e["操作ID"]||e["操作"]) : e["操作"];
      const rc=el("rect",{x:x(s),y:y0,width:Math.max(x(en)-x(s),1.5),height:rowH,fill:C[k]},svg);
      hover(rc,`<b>${name}</b>（${nm("cat",K[k])}）<br>${fmt(s)} – ${fmt(en)}・${(en-s).toFixed(1)}${L().sec}<br>${nm("part",e["作業部分"])}`);
    }
  });
}

// 表
function table(){
  const ms=methods(); const vals=ms.map(m=>pick(m));
  if(vals.every(v=>!v)) return empty("tbl",L().noRec);
  const cell=(v,f)=>v?f(v):"—"; const T=L();
  const rows=[[T.count,...vals.map(v=>cell(v,v=>T.records(v.n)))],[sel.part==="全体"?T.total:T.partTime(nm("part",sel.part)),...vals.map(v=>cell(v,v=>fmt(v.time)))]];
  K.forEach((k,j)=>rows.push([T.timeOf(nm("cat",k)),...vals.map(v=>cell(v,v=>fmt(v.t[j])))]));
  K.forEach((k,j)=>rows.push([T.numOf(nm("cat",k)),...vals.map(v=>cell(v,v=>fmtN(v.c[j])))]));
  const per=vals.map(v=>v?perOpValues(v):null);
  rows.push(["__group__"+T.perGroup]);
  K.slice(0,3).forEach((k,j)=>rows.push([nm("cat",k),...per.map(p=>p? (p[j]==null?"—":p[j].toFixed(1)+" "+T.sec) : "—")]));
  rows.push(["__group__"+(lang==="en"?"Quality and others":"品質・そのほか")]);
  rows.push([T.undo,...vals.map(v=>cell(v,v=>fmtN(v.undo)))],[T.faces,...vals.map(v=>cell(v,v=>Math.round(v.faces)))],
    [T.height,...vals.map(v=>cell(v,v=>v.height.toFixed(1)+" mm"))],[T.diam,...vals.map(v=>cell(v,v=>v.diameter.toFixed(1)+" mm"))],
    [T.islands,...vals.map(v=>cell(v,v=>Math.round(v.islands*10)/10))]);
  const note = sel.view==="平均"?T.avg:T.trial(sel.view);
  const body=rows.map(r=> String(r[0]).startsWith("__group__") ? `<tr class="group"><td colspan="${ms.length+1}">${r[0].slice(9)}</td></tr>` : `<tr>${r.map((c,i)=>`<td class="${i?"":"k"}">${c}</td>`).join("")}</tr>`).join("");
  document.getElementById("tbl").innerHTML=`<table><thead><tr><th>${nm("part",sel.part)} · ${note}</th>${ms.map(m=>`<th>${nm("method",m)}</th>`).join("")}</tr></thead><tbody>${body}</tbody></table><p class="note">${T.perNote}</p>`;
}

// その他
function others(){
  const ms=methods(); const vals=ms.map(m=>pick(m)); const counts={}; let anyLog=false;
  vals.forEach((v,i)=>{ if(!v) return; for(const r of v.recs){ const log=store.logs[r.logKey]; if(!log) continue; anyLog=true;
    for(const e of log){ if(e["区分"]!=="その他") continue; if(sel.part!=="全体" && e["作業部分"]!==sel.part) continue;
      const name = lang==="en" ? (e["操作(英語)"]||e["操作ID"]||e["操作"]) : e["操作"];
      (counts[name] ||= ms.map(()=>0))[i]+=1; } } });
  document.getElementById("osub").textContent = L().othd + (sel.view==="平均"?L().sum:` (${L().trial(sel.view)})`);
  if(!anyLog) return empty("other",L().noLog);
  const list=Object.entries(counts).sort((a,b)=>b[1].reduce((s,x)=>s+x,0)-a[1].reduce((s,x)=>s+x,0));
  document.getElementById("other").innerHTML=`<table><thead><tr><th>${L().ops}</th>${ms.map(m=>`<th>${nm("method",m)}</th>`).join("")}</tr></thead><tbody>${list.map(([n,c])=>`<tr><td class="k">${n}</td>${c.map(x=>`<td>${x}</td>`).join("")}</tr>`).join("")}</tbody></table>`;
}

function texts(){
  document.documentElement.lang = lang;
  document.querySelectorAll("[data-t]").forEach(e=>e.textContent=L()[e.dataset.t]);
  document.querySelectorAll("#lang button").forEach(b=>b.classList.toggle("on", b.dataset.l===lang));
  const ex=store.recs.filter(x=>!x.use).length;
  document.getElementById("status").textContent = store.recs.length ? L().loaded(store.recs.length, ex) : L().empty;
}
function buildAll(){
  buildFilters(); texts(); summary();
  cardPill("o1","other1",[[false,L().hideOther],[true,L().showOther]]);
  cardPill("o2","other2",[[false,L().hideOther],[true,L().showOther]]);
  cardPill("o3","tab3",[["all",L().tabAll],["other",L().tabOther]]);
  byType("g1","min",sel.other1); byType("g2","count",sel.other2); totals(); timeline(); table(); others();
}
document.getElementById("lang").addEventListener("click",e=>{ const l=e.target.dataset.l; if(!l) return; lang=l; try{localStorage.setItem("mslog_lang",l);}catch(err){} buildAll(); });

(function init(){
  let embedded=null;
  try{ embedded=JSON.parse(document.getElementById("embedded").textContent); }catch(e){}
  if(embedded && embedded.summary) addFolder(embedded.summary, embedded.logs||{}, "blender");
  buildAll();
})();
</script>
</body>
</html>
'''


def _collect_data(folder):
    data = {"summary": "", "logs": {}}
    summary = os.path.join(folder, "まとめ.csv")
    if os.path.exists(summary):
        data["summary"] = _read_text(summary)[0]
        for row in csv.DictReader(io.StringIO(data["summary"])):
            name = (row.get("操作ログファイル") or "").strip()
            path = os.path.join(folder, name)
            if name and os.path.exists(path):
                data["logs"][name] = _read_text(path)[0]
    return data


def make_viewer(folder):
    data = json.dumps(_collect_data(folder), ensure_ascii=False).replace("</", "<\\/")
    html = VIEWER_HTML.replace("/*__DATA__*/null", data)
    path = os.path.join(folder, "グラフ.html")
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    return path


# ---------------------------------------------------------------- ボタン

class MSLOG_OT_start(bpy.types.Operator):
    bl_idname = "mslog.start"
    bl_label = "記録開始"
    bl_description = "制作時間と操作の記録を始める"

    @classmethod
    def poll(cls, context):
        return not S.running

    def execute(self, context):
        if not context.window_manager.mslog_author.strip():
            self.report({"WARNING"}, "制作者の名前を入れてください")
            return {"CANCELLED"}
        _start(context)
        self.report({"INFO"}, f"記録を開始しました：{S.method} 試行{S.trial}")
        return {"FINISHED"}


class MSLOG_OT_stop(bpy.types.Operator):
    bl_idname = "mslog.stop"
    bl_label = "記録終了"
    bl_description = "記録を終了し、まとめ.csvと操作ログに書き出す"

    @classmethod
    def poll(cls, context):
        return S.running

    def execute(self, context):
        total, stats = _finish("", context)
        if S.message:
            self.report({"WARNING"}, S.message)
        else:
            self.report({"INFO"}, f"記録しました：{total:.0f}秒、面数{stats['faces']}")
        return {"FINISHED"}


class MSLOG_OT_graph(bpy.types.Operator):
    bl_idname = "mslog.graph"
    bl_label = "グラフを見る"
    bl_description = "記録フォルダのデータからグラフのページを作って、ブラウザで開く"

    @classmethod
    def poll(cls, context):
        return not S.running

    def execute(self, context):
        path = make_viewer(_output_dir())
        url = "file://" + path.replace(os.sep, "/") if os.sep != "/" else "file://" + path
        try:
            bpy.ops.wm.url_open(url=url)
        except Exception:
            webbrowser.open(url)
        return {"FINISHED"}


class MSLOG_OT_open_folder(bpy.types.Operator):
    bl_idname = "mslog.open_folder"
    bl_label = "記録フォルダを開く"

    def execute(self, context):
        bpy.ops.wm.path_open(filepath=_output_dir())
        return {"FINISHED"}


def _mmss(sec):
    sec = int(round(sec))
    return f"{sec // 60}:{sec % 60:02d}"


class MSLOG_PT_panel(bpy.types.Panel):
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "操作記録"
    bl_label = "操作記録"

    def draw(self, context):
        layout = self.layout
        wm = context.window_manager

        col = layout.column()
        col.enabled = not S.running
        col.prop(wm, "mslog_author", text="制作者")
        col.prop(wm, "mslog_method", text="手法")
        col.prop(wm, "mslog_trial", text="試行番号")
        col.prop(wm, "mslog_note", text="メモ")

        if S.running:
            layout.label(text="今の作業")
            row = layout.row(align=True)
            row.scale_y = 1.5
            row.prop(wm, "mslog_part", expand=True)

            box = layout.box()
            total, t, n = _live_totals()
            big = box.row()
            big.scale_y = 1.4
            big.alignment = "CENTER"
            big.label(text=f"記録中  {_mmss(total)}", icon="REC")
            grid = box.grid_flow(row_major=True, columns=3, even_columns=False, align=True)
            for c in CATS:
                grid.label(text=c)
                grid.label(text=_mmss(t[c]))
                grid.label(text=f"{n[c]}回")
            box.label(text=f"取り消し  {S.undo}回")
            layout.operator("mslog.stop", icon="SNAP_FACE")
        else:
            big = layout.row()
            big.scale_y = 1.4
            big.operator("mslog.start", icon="REC")
            layout.operator("mslog.graph", icon="GRAPH")
        layout.operator("mslog.open_folder", icon="FILE_FOLDER")
        if S.message:
            layout.label(text=S.message, icon="INFO")


# ---------------------------------------------------------------- 登録

CLASSES = (MSLOG_OT_start, MSLOG_OT_stop, MSLOG_OT_graph, MSLOG_OT_open_folder, MSLOG_PT_panel)
WM_PROPS = ("mslog_author", "mslog_method", "mslog_trial", "mslog_note", "mslog_part")


def register():
    for cls in CLASSES:
        bpy.utils.register_class(cls)
    wm = bpy.types.WindowManager
    wm.mslog_author = StringProperty(name="制作者", default=_read_last_author())
    wm.mslog_method = EnumProperty(name="手法", items=METHOD_ITEMS, default="EXTRUDE")
    wm.mslog_trial = IntProperty(name="試行番号", default=1, min=0)
    wm.mslog_note = StringProperty(name="メモ", default="")
    wm.mslog_part = EnumProperty(name="今の作業", items=PART_ITEMS, default="BODY",
                                 update=_on_part_changed)
    if _on_load_pre not in bpy.app.handlers.load_pre:
        bpy.app.handlers.load_pre.append(_on_load_pre)
    if _on_load_post not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(_on_load_post)


def unregister():
    if S.running:
        _finish("（アドオンを無効化したため終了）")
    for handlers, func in ((bpy.app.handlers.load_pre, _on_load_pre),
                           (bpy.app.handlers.load_post, _on_load_post)):
        if func in handlers:
            handlers.remove(func)
    wm = bpy.types.WindowManager
    for name in WM_PROPS:
        if hasattr(wm, name):
            delattr(wm, name)
    for cls in reversed(CLASSES):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
