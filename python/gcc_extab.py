# .eh_frame/.gcc_exception_table parser/formatter for IDA
# Copyright (c) 2012 Igor Skochinsky
# Version 0.1 2012-06-19
#
# This software is provided 'as-is', without any express or implied
# warranty. In no event will the authors be held liable for any damages
# arising from the use of this software.
#
# Permission is granted to anyone to use this software for any purpose,
# including commercial applications, and to alter it and redistribute it
# freely, subject to the following restrictions:
#
#    1. The origin of this software must not be misrepresented; you must not
#    claim that you wrote the original software. If you use this software
#    in a product, an acknowledgment in the product documentation would be
#    appreciated but is not required.
#
#    2. Altered source versions must be plainly marked as such, and must not be
#    misrepresented as being the original software.
#
#    3. This notice may not be removed or altered from any source
#    distribution.

import struct

import idaapi
import ida_bytes
import ida_ida
import ida_idaapi
import ida_kernwin
import ida_nalt
import ida_offset
import ida_segment
import ida_xref
import idc

# REF_OFF* constants location differs across IDA builds.
REF_OFF32 = getattr(ida_offset, "REF_OFF32", getattr(ida_nalt, "REF_OFF32", None))
REF_OFF64 = getattr(ida_offset, "REF_OFF64", getattr(ida_nalt, "REF_OFF64", None))

def make_array(ea, nbytes):
  if nbytes <= 0:
    return False
  try:
    ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, nbytes)
    # Best-effort byte array marking.
    return ida_bytes.create_data(ea, ida_bytes.FF_BYTE, nbytes, ida_idaapi.BADADDR)
  except Exception:
    return False

_orig_set_cmt = ida_bytes.set_cmt
_comments_enabled = True
_last_lsda_info = None
_last_fde_info = None
_last_skip_diag = None
_warned_missing_bases = set()
_warned_missing_cie = set()
_warned_unresolved_indirect = set()
_entries_in_progress = set()
MAX_CFI_ENTRY_SIZE = 0x100000

def set_comments_enabled(enabled):
  global _comments_enabled
  _comments_enabled = bool(enabled)

def get_comments_enabled():
  return bool(_comments_enabled)

def set_cmt(ea, cmt, repeatable = 0):
  if not _comments_enabled:
    return False
  try:
    return _orig_set_cmt(ea, cmt, repeatable)
  except Exception:
    return False

def reset_parse_state():
  global _last_lsda_info, _last_fde_info, _last_skip_diag
  _last_lsda_info = None
  _last_fde_info = None
  _last_skip_diag = None
  try:
    aug_params.clear()
  except Exception:
    pass
  try:
    _warned_missing_bases.clear()
    _warned_missing_cie.clear()
    _warned_unresolved_indirect.clear()
    _entries_in_progress.clear()
  except Exception:
    pass

def get_last_lsda_info():
  return _last_lsda_info

def get_last_fde_info():
  return _last_fde_info

def get_last_skip_diag():
  return _last_skip_diag

def _set_skip_diag(entry_ea, reason, detail = "", **kwargs):
  global _last_skip_diag
  info = {
    "entry_ea": entry_ea,
    "reason": reason,
    "detail": detail,
  }
  info.update(kwargs)
  _last_skip_diag = info

def ptrval(ea):
  return ida_bytes.get_qword(ea)

def _ptr_size():
  return 8 if ida_ida.inf_is_64bit() else 4

def _align_up(x, a):
  return (x + (a - 1)) & ~(a - 1)

def _default_text_base():
  try:
    seg = ida_segment.get_segm_by_name('.text')
    if seg:
      return seg.start_ea
  except Exception:
    pass
  return None

def _default_data_base():
  # Base selection for datarel-based encodings.
  for name in ('.got', '.gotrw', '.data', '.rodata'):
    try:
      seg = ida_segment.get_segm_by_name(name)
      if seg:
        return seg.start_ea
    except Exception:
      pass
  return None

def _offset_item_width(ea):
  f = ida_bytes.get_full_flags(ea)
  if not ida_bytes.is_data(f):
    return 0
  sz = ida_bytes.get_item_size(ea)
  if ida_bytes.is_byte(f) and sz == 1:
    return 1
  if ida_bytes.is_word(f) and sz == 2:
    return 2
  if ida_bytes.is_dword(f) and sz == 4:
    return 4
  if ida_bytes.is_qword(f) and sz == 8:
    return 8
  return 0

def _ensure_item_head(ea, create_byte=False):
  if ea in (None, 0, ida_idaapi.BADADDR):
    return False
  if not ida_bytes.is_loaded(ea):
    return False
  flags = ida_bytes.get_full_flags(ea)
  if ida_bytes.is_head(flags):
    return True
  if not create_byte:
    return False
  # Avoid destructive rewrites: only auto-create a head on unknown bytes.
  if not ida_bytes.is_unknown(flags):
    return False
  try:
    if ida_bytes.create_data(ea, ida_bytes.FF_BYTE, 1, ida_idaapi.BADADDR):
      return ida_bytes.is_head(ida_bytes.get_full_flags(ea))
  except Exception:
    pass
  return False

def safe_add_dref(frm, to, drtype=(ida_xref.dr_O | ida_xref.XREF_USER), create_from=False, create_to=False):
  """
  Best-effort xref creation that avoids IDA 'bad call add_dref' warnings by
  ensuring item heads at both ends when requested.
  """
  if not _ensure_item_head(frm, create_byte=create_from):
    return False
  if not _ensure_item_head(to, create_byte=create_to):
    return False
  try:
    ida_xref.add_dref(frm, to, drtype)
    return True
  except Exception:
    return False

# sign extend b low bits in x
# from "Bit Twiddling Hacks"
def SIGNEXT(x, b):
  m = 1 << (b - 1)
  x = x & ((1 << b) - 1)
  return (x ^ m) - m

def ForceWord(ea):
  if ea != ida_idaapi.BADADDR and ea != 0:
    if not ida_bytes.is_word(ida_bytes.get_full_flags(ea)) or ida_bytes.get_item_size(ea) != 2:
      ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, 2)
      ida_bytes.create_data(ea, ida_bytes.FF_WORD, 2, ida_idaapi.BADADDR)
    if ida_bytes.is_off0(ida_bytes.get_full_flags(ea)) and idc.get_fixup_target_type(ea) == -1:
      # remove the offset
      ida_bytes.op_hex(ea, 0)

def ForceDword(ea):
  if ea != ida_idaapi.BADADDR and ea != 0:
    if not ida_bytes.is_dword(ida_bytes.get_full_flags(ea)) or ida_bytes.get_item_size(ea) != 4:
      ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, 4)
      ida_bytes.create_data(ea, ida_bytes.FF_DWORD, 4, ida_idaapi.BADADDR)
    if ida_bytes.is_off0(ida_bytes.get_full_flags(ea)) and idc.get_fixup_target_type(ea) == -1:
      # remove the offset
      ida_bytes.op_hex(ea, 0)

def ForceQword(ea):
  if ea != ida_idaapi.BADADDR and ea != 0:
    if not ida_bytes.is_qword(ida_bytes.get_full_flags(ea)) or ida_bytes.get_item_size(ea) != 8:
      ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, 8)
      ida_bytes.create_data(ea, ida_bytes.FF_QWORD, 8, ida_idaapi.BADADDR)
    if ida_bytes.is_off0(ida_bytes.get_full_flags(ea)) and idc.get_fixup_target_type(ea) == -1:
      # remove the offset
      ida_bytes.op_hex(ea, 0)

def ForcePtr(ea, delta = 0):
  ForceQword(ea)
  if _offset_item_width(ea) != 8:
    return
  if idc.get_fixup_target_type(ea) != -1 and ida_bytes.is_off0(ida_bytes.get_full_flags(ea)):
    # don't touch fixups
    return
  pv = ptrval(ea)
  if pv != 0 and pv != ida_idaapi.BADADDR:
    # apply offset again
    if idaapi.is_spec_ea(pv):
      delta = 0
    if REF_OFF64 is not None:
      ida_offset.op_offset(ea, 0, REF_OFF64, -1, 0, delta)

def format_byte(ea, cmt = None):
  if ea != ida_idaapi.BADADDR and ea != 0:
    if not ida_bytes.is_byte(ida_bytes.get_full_flags(ea)) or ida_bytes.get_item_size(ea) != 1:
      ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, 1)
      ida_bytes.create_data(ea, ida_bytes.FF_BYTE, 1, ida_idaapi.BADADDR)
  if cmt:
    set_cmt(ea, cmt, 0)
  return ida_bytes.get_wide_byte(ea)

def format_dword(ea, cmt = None):
  ForceDword(ea)
  if cmt:
    set_cmt(ea, cmt, 0)
  return ida_bytes.get_wide_dword(ea), ea + 4

def format_string(ea, cmt = None):
  s = ida_bytes.get_strlit_contents(ea, -1, ida_nalt.STRTYPE_C)
  if s is None:
    s = b""
  slen = len(s)+1
  ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, slen)
  ida_bytes.create_strlit(ea, slen, ida_nalt.STRTYPE_C)
  if cmt:
    set_cmt(ea, cmt, 0)
  return s, ea + slen

def format_leb128(ea, cmt = None, signed = False):
  val, ea2 = read_enc_val(ea, [DW_EH_PE_uleb128, DW_EH_PE_sleb128][signed], True)
  if cmt:
    set_cmt(ea, cmt, 0)
  return val, ea2

def read_leb128(ea, signed):
  v = 0
  s = 0
  while True:
    b = ida_bytes.get_wide_byte(ea)
    v |= (b&0x7F)<<s
    s += 7
    ea += 1
    if (b & 0x80) == 0:
      break
    if s > 64:
      print("Bad leb128 at %08X" % (ea - s//7))
      return ida_idaapi.BADADDR, ida_idaapi.BADADDR
  if signed and (b & 0x40):
    v -= (1<<s)
  return v, ea

def read_uleb128(ea):
  return read_leb128(ea, False)

def read_sleb128(ea):
  return read_leb128(ea, True)

val_format = {
  0x00: "DW_EH_PE_ptr",
  0x01: "DW_EH_PE_uleb128",
  0x02: "DW_EH_PE_udata2",
  0x03: "DW_EH_PE_udata4",
  0x04: "DW_EH_PE_udata8",
  0x08: "DW_EH_PE_signed",
  0x09: "DW_EH_PE_sleb128",
  0x0A: "DW_EH_PE_sdata2",
  0x0B: "DW_EH_PE_sdata4",
  0x0C: "DW_EH_PE_sdata8",
}
val_appl = {
  0x00: "DW_EH_PE_absptr",
  0x10: "DW_EH_PE_pcrel",
  0x20: "DW_EH_PE_textrel",
  0x30: "DW_EH_PE_datarel",
  0x40: "DW_EH_PE_funcrel",
  0x50: "DW_EH_PE_aligned",
}

DW_EH_PE_ptr       = 0x00
DW_EH_PE_uleb128   = 0x01
DW_EH_PE_udata2    = 0x02
DW_EH_PE_udata4    = 0x03
DW_EH_PE_udata8    = 0x04
DW_EH_PE_signed    = 0x08
DW_EH_PE_sleb128   = 0x09
DW_EH_PE_sdata2    = 0x0A
DW_EH_PE_sdata4    = 0x0B
DW_EH_PE_sdata8    = 0x0C
DW_EH_PE_absptr    = 0x00
DW_EH_PE_pcrel     = 0x10
DW_EH_PE_textrel   = 0x20
DW_EH_PE_datarel   = 0x30
DW_EH_PE_funcrel   = 0x40
DW_EH_PE_aligned   = 0x50
DW_EH_PE_indirect  = 0x80
DW_EH_PE_omit      = 0xFF

def format_enc(ea, cmt):
  v = format_byte(ea)
  if v == DW_EH_PE_omit:
    addcmt = "DW_EH_PE_omit"
  else:
    f, a = v&0x0F, v&0x70
    if f in val_format and a in val_appl:
      addcmt = "%s|%s" % (val_format[f], val_appl[a])
      if v & DW_EH_PE_indirect:
        addcmt += "|DW_EH_PE_indirect"
    else:
      addcmt = "Bad encoding: %02X" % v
  set_cmt(ea, "%s: %s" % (cmt, addcmt), 0)
  return v, ea + 1

def enc_size(enc):
  f = enc & 0x0F
  if f == DW_EH_PE_ptr:
    return 8
  elif f in [DW_EH_PE_sdata2, DW_EH_PE_udata2]:
    return 2
  elif f in [DW_EH_PE_sdata4, DW_EH_PE_udata4]:
    return 4
  elif f in [DW_EH_PE_sdata8, DW_EH_PE_udata8]:
    return 8
  elif f != DW_EH_PE_omit:
    ida_kernwin.warning("logic error: encoding %02X is not fixed size" % (enc))
  return 0

def read_enc_val(ea, enc, format = False, text_ea = None, data_ea = None, funcrel_ea = None):
  if enc == DW_EH_PE_omit:
    ida_kernwin.warning("%08X: logic error in read_enc_val" % ea)
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR
  start = ea
  f, a = enc&0x0F, enc&0x70
  if a == DW_EH_PE_aligned:
    # Align read cursor to pointer-sized boundary and treat as absolute value.
    ea = _align_up(ea, _ptr_size())
    start = ea
    a = DW_EH_PE_absptr
    # In practice aligned is used with pointer-sized values.
    if f == DW_EH_PE_omit:
      f = DW_EH_PE_ptr
  if f == DW_EH_PE_ptr:
    val = ptrval(ea)
    ea += 8
    if format:
      ForcePtr(start)
  elif f in [DW_EH_PE_uleb128, DW_EH_PE_sleb128]:
    val, ea = read_leb128(ea, f== DW_EH_PE_sleb128)
    format_byte(start)
    if ea - start > 1:
      make_array(start, ea - start)
  elif f in [DW_EH_PE_sdata2, DW_EH_PE_udata2]:
    val = ida_bytes.get_wide_word(ea)
    ea += 2
    if f == DW_EH_PE_sdata2:
      val = SIGNEXT(val, 16)
    if format:
      ForceWord(start)
  elif f in [DW_EH_PE_sdata4, DW_EH_PE_udata4]:
    val = ida_bytes.get_wide_dword(ea)
    ea += 4
    if f == DW_EH_PE_sdata4:
      val = SIGNEXT(val, 32)
    if format:
      ForceDword(start)
  elif f in [DW_EH_PE_sdata8, DW_EH_PE_udata8]:
    val = ida_bytes.get_qword(ea)
    ea += 8
    if f == DW_EH_PE_sdata8:
      val = SIGNEXT(val, 64)
    if format:
      ForceQword(start)
  else:
    print("%08X: don't know how to handle encoding %02X" % (start, enc))
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR
  base_ea = None
  if a == DW_EH_PE_pcrel:
    base_ea = start
    if val != 0:
      make_reloff(start, start)
      val += start
      val &= (1<<(8*8)) - 1
      # ida_offset.op_offset(start, 0, ida_offset.REF_OFF32, ida_idaapi.BADADDR, start, 0)
  elif a == DW_EH_PE_textrel:
    if text_ea is None:
      text_ea = _default_text_base()
    base_ea = text_ea
    if val != 0 and base_ea is not None:
      make_reloff(start, base_ea)
      val += base_ea
      val &= (1<<(8*8)) - 1
    elif val != 0:
      if "textrel" not in _warned_missing_bases:
        print("%08X: DW_EH_PE_textrel without text base EA (using raw value)" % start)
        _warned_missing_bases.add("textrel")
  elif a == DW_EH_PE_datarel:
    if data_ea is None:
      data_ea = _default_data_base()
    base_ea = data_ea
    if val != 0 and base_ea is not None:
      make_reloff(start, base_ea)
      val += base_ea
      val &= (1<<(8*8)) - 1
    elif val != 0:
      if "datarel" not in _warned_missing_bases:
        print("%08X: DW_EH_PE_datarel without data base EA (using raw value)" % start)
        _warned_missing_bases.add("datarel")
  elif a == DW_EH_PE_funcrel:
    base_ea = funcrel_ea
    if val != 0 and base_ea is not None:
      make_reloff(start, base_ea)
      val += base_ea
      val &= (1<<(8*8)) - 1
    elif val != 0:
      if "funcrel" not in _warned_missing_bases:
        print("%08X: DW_EH_PE_funcrel without function base EA (using raw value)" % start)
        _warned_missing_bases.add("funcrel")
  elif a == DW_EH_PE_absptr:
    pass
  else:
    print("%08X: don't know how to handle encoding %02X" % (start, enc))
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR
  if (enc & DW_EH_PE_indirect) and val != 0:
    if not ida_bytes.is_loaded(val):
      # Keep raw value and continue parsing.
      # This is common for some binaries where referenced slots are not mapped
      # in the current IDA view yet, and hard-failing here breaks CIE/FDE parse.
      warn_key = (start, enc, val)
      if warn_key not in _warned_unresolved_indirect:
        print("%08X: unresolved indirect pointer %08X (enc=%02X), keeping raw value" % (start, val, enc))
        _warned_unresolved_indirect.add(warn_key)
      return val, ea
    val = ptrval(val)
  return val, ea

def make_reloff(ea, base, subtract = False):
  width = _offset_item_width(ea)
  if width == 0:
    return False
  ri = idaapi.refinfo_t()
  reftype = REF_OFF64 if width == 8 else REF_OFF32
  if reftype is None:
    return False
  flag = reftype | ida_nalt.REFINFO_NOBASE
  if subtract:
    flag |= idaapi.REFINFO_SUBTRACT
  ri.init(flag, base)
  ida_offset.op_offset_ex(ea, 0, ri)
  return True

def decode_eh_frame_hdr(hdr_seg, verbose = False):
  """
  Decode .eh_frame_hdr header fields and table start.
  Returns dict on success:
    {
      "version", "eh_frame_ptr_enc", "fde_count_enc", "table_enc",
      "eh_frame_ptr", "fde_count", "table_ea", "hdr_base"
    }
  or None on failure.
  """
  if not hdr_seg:
    return None
  try:
    ea = hdr_seg.start_ea
    version = ida_bytes.get_byte(ea)
    if version != 1:
      if verbose:
        print("[gcc_extab] .eh_frame_hdr unsupported version: %r" % (version,))
      return None

    eh_frame_ptr_enc = ida_bytes.get_byte(ea + 1) & 0xFF
    fde_count_enc = ida_bytes.get_byte(ea + 2) & 0xFF
    table_enc = ida_bytes.get_byte(ea + 3) & 0xFF
    ea += 4

    hdr_base = hdr_seg.start_ea
    eh_frame_ptr = ida_idaapi.BADADDR
    if eh_frame_ptr_enc == 0x1B:
      # pcrel|sdata4: base is the encoded field address.
      field_ea = ea
      raw = ida_bytes.get_bytes(field_ea, 4) or b""
      if len(raw) != 4:
        if verbose:
          print("[gcc_extab] .eh_frame_hdr failed to read 0x1B eh_frame_ptr field.")
        return None
      rel, = struct.unpack("<i", raw)
      eh_frame_ptr = (field_ea + rel) & 0xFFFFFFFFFFFFFFFF
      ea = field_ea + 4
    else:
      eh_frame_ptr, ea2 = read_enc_val(ea, eh_frame_ptr_enc, True, data_ea = hdr_base)
      if eh_frame_ptr in (None, ida_idaapi.BADADDR) or ea2 in (None, ida_idaapi.BADADDR):
        if verbose:
          print("[gcc_extab] .eh_frame_hdr failed to decode eh_frame_ptr.")
        return None
      ea = ea2

    fde_count, ea2 = read_enc_val(ea, fde_count_enc, True, data_ea = hdr_base)
    if fde_count in (None, ida_idaapi.BADADDR) or ea2 in (None, ida_idaapi.BADADDR):
      if verbose:
        print("[gcc_extab] .eh_frame_hdr failed to decode fde_count.")
      return None
    ea = ea2

    try:
      fde_count = int(fde_count)
    except Exception:
      if verbose:
        print("[gcc_extab] .eh_frame_hdr fde_count is not an integer: %r" % (fde_count,))
      return None

    return {
      "version": version,
      "eh_frame_ptr_enc": eh_frame_ptr_enc,
      "fde_count_enc": fde_count_enc,
      "table_enc": table_enc,
      "eh_frame_ptr": eh_frame_ptr,
      "fde_count": fde_count,
      "table_ea": ea,
      "hdr_base": hdr_base,
    }
  except Exception as e:
    if verbose:
      print("[gcc_extab] .eh_frame_hdr decode failed: %s" % e)
    return None

def collect_fde_ptrs_from_eh_frame_hdr(hdr_seg, eh_seg = None, verbose = False, max_count = 200000):
  """
  Collect FDE entry addresses from .eh_frame_hdr binary search table.
  Returns list of dicts: {fde_ea, hdr_start, index}.
  """
  out = []
  info = decode_eh_frame_hdr(hdr_seg, verbose = verbose)
  if not info:
    return out

  table_enc = info["table_enc"]
  if table_enc == DW_EH_PE_omit:
    if verbose:
      print("[gcc_extab] .eh_frame_hdr has no FDE table (DW_EH_PE_omit).")
    return out

  fde_count = info["fde_count"]
  if fde_count <= 0:
    return out
  if fde_count > max_count:
    if verbose:
      print("[gcc_extab] .eh_frame_hdr suspicious fde_count=%d, clamping." % fde_count)
    fde_count = max_count

  ea = info["table_ea"]
  hdr_base = info["hdr_base"]
  seen = {}
  for i in range(fde_count):
    if ea >= hdr_seg.end_ea:
      break

    hdr_start, ea2 = read_enc_val(ea, table_enc, True, data_ea = hdr_base)
    if ea2 in (None, ida_idaapi.BADADDR):
      break
    ea = ea2

    fde_ptr, ea2 = read_enc_val(ea, table_enc, True, data_ea = hdr_base)
    if ea2 in (None, ida_idaapi.BADADDR):
      break
    ea = ea2

    if fde_ptr in (None, 0, ida_idaapi.BADADDR):
      continue
    fde_ptr = fde_ptr & 0xFFFFFFFFFFFFFFFF
    if not ida_bytes.is_loaded(fde_ptr):
      continue
    if eh_seg and (fde_ptr < eh_seg.start_ea or fde_ptr >= eh_seg.end_ea):
      continue
    if fde_ptr in seen:
      continue
    seen[fde_ptr] = True
    out.append({
      "fde_ea": fde_ptr,
      "hdr_start": (hdr_start & 0xFFFFFFFFFFFFFFFF) if hdr_start not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
      "index": i,
    })
  return out

def find_eh_frame_end(eh_frame_start_ea, limit_ea = None, default_span = 0x400000, verbose = False):
  """
  Determine .eh_frame end by scanning CIE/FDE records:
    [u32 len][payload] ... [u32 0 terminator]
  Returns end EA or BADADDR on failure.
  """
  if eh_frame_start_ea in (None, 0, ida_idaapi.BADADDR):
    return ida_idaapi.BADADDR

  if limit_ea is None:
    seg = ida_segment.getseg(eh_frame_start_ea)
    if seg:
      limit_ea = seg.end_ea
    else:
      limit_ea = (eh_frame_start_ea + default_span) & 0xFFFFFFFFFFFFFFFF

  if limit_ea in (None, ida_idaapi.BADADDR) or limit_ea <= eh_frame_start_ea:
    return ida_idaapi.BADADDR

  curr = eh_frame_start_ea
  while curr + 4 <= limit_ea and ida_bytes.is_loaded(curr):
    length = ida_bytes.get_dword(curr)
    if length in (None, ida_idaapi.BADADDR):
      break
    if length == 0:
      curr += 4
      break

    # 64-bit DWARF extension: 0xFFFFFFFF + uint64 length.
    if length == 0xFFFFFFFF:
      if curr + 12 > limit_ea:
        break
      real_len = ida_bytes.get_qword(curr + 4)
      next_ea = curr + 12 + real_len
    else:
      next_ea = curr + 4 + length

    if next_ea <= curr:
      if verbose:
        print("[gcc_extab] .eh_frame scan stalled at 0x%x" % curr)
      break

    if next_ea > limit_ea:
      curr = limit_ea
      break
    curr = next_ea

  end_ea = min(curr, limit_ea)
  if end_ea <= eh_frame_start_ea:
    return ida_idaapi.BADADDR
  return end_ea

def _try_resolve_cie(cie_ea):
  if cie_ea in aug_params:
    return True
  if cie_ea in _entries_in_progress:
    return False
  seg = ida_segment.getseg(cie_ea)
  if not seg:
    return False
  seg_name = ida_segment.get_segm_name(seg) or ""
  if seg_name != ".eh_frame":
    return False
  try:
    _entries_in_progress.add(cie_ea)
    format_cie_fde(cie_ea)
  except Exception:
    return False
  finally:
    _entries_in_progress.discard(cie_ea)
  return cie_ea in aug_params

def format_lsda(ea, lpstart = None, sjlj = False):
  global _last_lsda_info
  text_base = _default_text_base()
  data_base = _default_data_base()
  lsda_start_ea = ea
  lsda_seg = ida_segment.getseg(lsda_start_ea)
  lsda_limit = lsda_seg.end_ea if lsda_seg else ida_idaapi.BADADDR
  lpstart_enc, ea = format_enc(ea, "LPStart encoding")
  if lpstart_enc != DW_EH_PE_omit:
    lpstart, ea2 = read_enc_val(ea, lpstart_enc, True, text_ea = text_base, data_ea = data_base, funcrel_ea = lpstart)
    if ea2 in (None, ida_idaapi.BADADDR):
      print("%08X: failed to decode LSDA LPStart pointer" % ea)
      return None
    set_cmt(ea, "LPStart: %08X" % lpstart, 0)
    ea = ea2
  ttype_enc, ea = format_enc(ea, "TType encoding")
  ttype_addr = ida_idaapi.BADADDR
  if ttype_enc != DW_EH_PE_omit:
    ttype_off, ea2 = read_enc_val(ea, DW_EH_PE_uleb128, True)
    if ttype_off in (None, ida_idaapi.BADADDR) or ea2 in (None, ida_idaapi.BADADDR):
      print("%08X: failed to decode LSDA type table offset" % ea)
      return None
    ttype_addr = ea2 + ttype_off
    if lsda_limit not in (None, ida_idaapi.BADADDR) and ttype_addr > lsda_limit:
      print("%08X: LSDA type table exceeds segment bounds (ttype=%08X, seg_end=%08X)" % (ea, ttype_addr, lsda_limit))
      return None
    set_cmt(ea, "TType offset: %08X -> %08X" % (ttype_off, ttype_addr), 0)
    make_reloff(ea, ea2)
    ea = ea2
  cs_enc, ea = format_enc(ea, "call site encoding")
  cs_len, ea2 = read_enc_val(ea, DW_EH_PE_uleb128, True)
  if cs_len in (None, ida_idaapi.BADADDR) or ea2 in (None, ida_idaapi.BADADDR):
    print("%08X: failed to decode LSDA call site table length" % ea)
    return None
  action_tbl = ea2 + cs_len
  if action_tbl < ea2:
    print("%08X: invalid LSDA call site table length (overflow)" % ea)
    return None
  if lsda_limit not in (None, ida_idaapi.BADADDR) and action_tbl > lsda_limit:
    print("%08X: LSDA call site table exceeds segment bounds (end=%08X, seg_end=%08X)" % (ea, action_tbl, lsda_limit))
    return None
  set_cmt(ea, "call site table length: %08X\naction table start: %08X" % (cs_len, action_tbl), 0)
  make_reloff(ea, ea2)
  ea = ea2
  i = 0
  actions = []
  callsites = []
  while ea < action_tbl:
    if sjlj:
      cs_lp, ea2 = read_enc_val(ea, DW_EH_PE_uleb128, True)
      if ea2 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode SJLJ call-site landing pad" % ea)
        return None
      cs_action, ea3 = read_enc_val(ea2, DW_EH_PE_uleb128, True)
      if ea3 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode SJLJ call-site action index" % ea2)
        return None
      set_cmt(ea, "cs_lp[%d] = %d" % (i, cs_lp), 0)
      act_ea = ea2
      ea = ea3
      callsites.append({
        "index": i,
        "try_start": ida_idaapi.BADADDR,
        "try_end": ida_idaapi.BADADDR,
        "landing": cs_lp if cs_lp not in (None, ida_idaapi.BADADDR) else 0,
        "action": cs_action if cs_action not in (None, ida_idaapi.BADADDR) else 0,
      })
    else:
      cs_start, ea2 = read_enc_val(ea, cs_enc, True, text_ea = text_base, data_ea = data_base, funcrel_ea = lpstart)
      if ea2 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode call-site start" % ea)
        return None
      cs_len,   ea3 = read_enc_val(ea2, cs_enc & 0x0F, True)
      if ea3 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode call-site length" % ea2)
        return None
      cs_lp,    ea4 = read_enc_val(ea3, cs_enc, True, text_ea = text_base, data_ea = data_base, funcrel_ea = lpstart)
      if ea4 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode call-site landing pad" % ea3)
        return None
      cs_action,ea5 = read_enc_val(ea4, DW_EH_PE_uleb128, True)
      if ea5 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode call-site action index" % ea4)
        return None
      if lpstart is not None:
        cs_start += lpstart
        if cs_lp != 0:
          cs_lp    += lpstart
          set_cmt(ea3, "cs_lp[%d] = %08X" % (i, cs_lp), 0)
          set_cmt(cs_lp, "Landing pad for %08X..%08X" % (cs_start, cs_start + cs_len), 0)
        else:
          set_cmt(ea3, "cs_lp[%d] = 0 (none)" % (i), 0)
      set_cmt(ea, "cs_start[%d] = %08X" % (i, cs_start), 0)
      set_cmt(ea2, "cs_len[%d] = %d (end = %08X)" % (i, cs_len, cs_start + cs_len), 0)
      if lpstart is not None:
        make_reloff(ea, lpstart)
        if cs_lp != 0:
          make_reloff(ea3, lpstart)
      callsites.append({
        "index": i,
        "try_start": cs_start if cs_start not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
        "try_end": (cs_start + cs_len) if cs_start not in (None, ida_idaapi.BADADDR) and cs_len not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
        "landing": cs_lp if cs_lp not in (None, ida_idaapi.BADADDR) else 0,
        "action": cs_action if cs_action not in (None, ida_idaapi.BADADDR) else 0,
      })
      act_ea = ea4
      ea = ea5
    if ea in (None, ida_idaapi.BADADDR):
      print("%08X: LSDA call-site parser reached invalid cursor" % lsda_start_ea)
      return None
    if cs_action == 0:
      addcmt = "no action"
    else:
      addcmt = "%08X" % (action_tbl + cs_action - 1)
      actions.append(cs_action)
    set_cmt(act_ea, "cs_action[%d] = %d (%s)" % (i, cs_action, addcmt), 0)
    i += 1

  actions2 = []
  while len(actions):
    act = actions.pop()
    if not act in actions2:
      act_ea = action_tbl + act - 1
      if lsda_limit not in (None, ida_idaapi.BADADDR) and (act_ea < lsda_start_ea or act_ea >= lsda_limit):
        print("%08X: LSDA action entry out of bounds (act=%d ea=%08X seg_end=%08X)" % (lsda_start_ea, act, act_ea, lsda_limit))
        return None
      # print("action %d -> %08X" % (act, act_ea))
      actions2.append(act)
      ar_filter,ea2 = read_enc_val(act_ea, DW_EH_PE_sleb128, True)
      if ea2 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode LSDA action filter" % act_ea)
        return None
      ar_disp,  ea3 = read_enc_val(ea2, DW_EH_PE_sleb128, True)
      if ea3 in (None, ida_idaapi.BADADDR):
        print("%08X: failed to decode LSDA action displacement" % ea2)
        return None
      if ar_filter == 0:
        addcmt = "cleanup"
      else:
        if ttype_addr == ida_idaapi.BADADDR:
          addcmt = "no type table?!"
        else:
          if ar_filter > 0:
            # catch expression
            type_slot = ttype_addr - ar_filter * enc_size(ttype_enc)
            set_cmt(type_slot, "Type index %d" % ar_filter, 0)
            type_ea, eatmp = read_enc_val(type_slot, ttype_enc, True, text_ea = text_base, data_ea = data_base, funcrel_ea = lpstart)
            addcmt = "catch type typeinfo = %08X" % (type_ea)
          else:
            # exception spec list
            type_slot = ttype_addr - ar_filter - 1
            addcmt = "exception spec index list = %08X" % (type_slot)

      set_cmt(act_ea, "ar_filter[%d]: %d (%s)" % (act, ar_filter, addcmt), 0)
      if ar_disp == 0:
        addcmt = "end"
      else:
        next_ea = ea2 + ar_disp
        if lsda_limit not in (None, ida_idaapi.BADADDR) and (next_ea < lsda_start_ea or next_ea >= lsda_limit):
          addcmt = "next out of bounds"
        else:
          next_act = next_ea - act_ea + act
          if next_act > 0:
            addcmt = "next: %d => %08X" % (next_act, next_ea)
            actions.append(next_act)
          else:
            addcmt = "invalid next action"
      set_cmt(ea2, "ar_disp[%d]: %d (%s)" % (act, ar_disp, addcmt), 0)
  _last_lsda_info = {
    "start_ea": lsda_start_ea,
    "end_ea": max(action_tbl, ea),
    "entries": i,
    "ttype_addr": ttype_addr,
    "action_table": action_tbl,
    "callsites": callsites,
  }
  return _last_lsda_info

class AugParams:
  def __init__(self):
    self.aug_present = False
    self.lsda_encoding = DW_EH_PE_omit
    self.personality_ptr = None
    self.fde_encoding = DW_EH_PE_absptr

aug_params = {}

def format_cie_fde(ea):
  global _last_fde_info, _last_skip_diag
  _last_fde_info = None
  _last_skip_diag = None
  text_base = _default_text_base()
  data_base = _default_data_base()
  start = ea
  sz32, ea = format_dword(ea, "Size")
  ext_mode = False
  if sz32 == 0:
    #print("%08X: end of CIEs" % start)
    _set_skip_diag(start, "terminator", "Zero-sized CFI entry")
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
  elif sz32 == 0xFFFFFFFF:
    ext_mode = True
    ForceQword(ea)
    sz = ida_bytes.get_qword(ea)
    set_cmt(ea, "Extended size", 0)
    ea += 8
  else:
    sz = sz32
    make_reloff(start, ea)
  if sz in (None, ida_idaapi.BADADDR) or sz <= 0:
    _set_skip_diag(start, "bad_entry_size", "Invalid CFI entry size", size = sz)
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
  if sz > MAX_CFI_ENTRY_SIZE:
    _set_skip_diag(start, "entry_too_large", "CFI entry size is suspiciously large", size = sz, limit = MAX_CFI_ENTRY_SIZE)
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
  end_ea = ea + sz
  if end_ea <= ea:
    _set_skip_diag(start, "bad_entry_end", "CFI entry end overflow/underflow", size = sz, body_start = ea)
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
  seg = ida_segment.getseg(start)
  if seg and end_ea > seg.end_ea:
    _set_skip_diag(start, "entry_out_of_bounds", "CFI entry exceeds segment bounds", end_ea = end_ea, seg_end = seg.end_ea, size = sz)
    return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
  if ext_mode:
    ForceQword(ea)
    cie_id = ida_bytes.get_qword(ea)
    set_cmt(ea, "CIE id", 0)
    cie_field_ea = ea
    ea += 8
  else:
    cie_id, ea = format_dword(ea, "CIE id")
    cie_field_ea = ea - 4
  is_cie = (cie_id == 0 or cie_id == 0xFFFFFFFFFFFFFFFF)
  #print("%08X: %s, size=%d" % (start, ["FIE", "CDE"][is_cie], sz))
  loc_start = loc_end = ida_idaapi.BADADDR
  if is_cie:
    ver, ea = format_byte(ea, "Version"), ea+1
    augmentation_raw, ea = format_string(ea, "Augmentation String")
    if isinstance(augmentation_raw, (bytes, bytearray)):
      augmentation = augmentation_raw.decode("latin-1", errors="replace")
    else:
      augmentation = str(augmentation_raw)
    code_align, ea = format_leb128(ea, "Code alignment factor")
    data_align, ea = format_leb128(ea, "Data alignment factor", True)
    if ver == 1:
      retreg, ea = format_byte(ea, "Return register"), ea+1
    else:
      retreg, ea = format_leb128(ea, "Return register")

    aug = AugParams()

    if augmentation and augmentation[0] == 'z':
      augm_len, ea = format_leb128(ea, "Augmentation data length")
      aug.aug_present = True
      for c in augmentation[1:]:
        if c == 'L':
          aug.lsda_encoding, ea = format_enc(ea, "L: LSDA pointer encoding")
        elif c == 'P':
          enc, ea = format_enc(ea, "P: Personality routine encoding")
          aug.personality_ptr, ea2 = read_enc_val(ea, enc, True, text_ea = text_base, data_ea = data_base)
          set_cmt(ea, "P: Personality routine pointer: %08X" % aug.personality_ptr, 0)
          ea = ea2
        elif c == 'R':
          aug.fde_encoding, ea = format_enc(ea, "R: FDE pointers encoding")
        else:
          print("%08X: unhandled augmentation string char: %c" % (ea, c))
          _set_skip_diag(start, "unhandled_augmentation_char", "Unhandled CIE augmentation char", char = c, aug = augmentation, aug_ea = ea)
          return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR

    instr_length = end_ea - ea
    if instr_length > 0:
      format_byte(ea, "Initial CFE Instructions")
      make_array(ea, instr_length)
    else:
      print("%08X: insn_len = %d?!" % (ea, instr_length))
    aug_params[start] = aug
    _last_fde_info = {
      "kind": "cie",
      "entry_ea": start,
      "end_ea": end_ea,
      "loc_start": ida_idaapi.BADADDR,
      "loc_end": ida_idaapi.BADADDR,
      "lsda_ptr": ida_idaapi.BADADDR,
      "lsda_end": ida_idaapi.BADADDR,
      "lsda_entries": 0,
    }
    # print("instr_length:", instr_length)
  else:
    cie_ea = cie_field_ea - cie_id
    if cie_ea in aug_params or _try_resolve_cie(cie_ea):
      aug = aug_params[cie_ea]
    else:
      warn_key = (cie_field_ea, cie_ea)
      if warn_key not in _warned_missing_cie:
        print("%08X: CIE %08X not present?!" % (cie_field_ea, cie_ea))
        _warned_missing_cie.add(warn_key)
      _set_skip_diag(start, "missing_cie", "Referenced CIE entry not parsed/present", cie_field_ea = cie_field_ea, cie_ea = cie_ea, cie_id = cie_id)
      return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
    make_reloff(cie_field_ea, cie_field_ea, True)
    set_cmt(cie_field_ea, "CIE pointer", 0)
    init_loc, ea2 = read_enc_val(ea, aug.fde_encoding, True, text_ea = text_base, data_ea = data_base)
    if init_loc in (None, ida_idaapi.BADADDR):
      _set_skip_diag(start, "bad_initial_location", "Unable to decode FDE initial location", fde_encoding = aug.fde_encoding, field_ea = ea, cie_ea = cie_ea)
      return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
    set_cmt(ea, "Initial location=%08X" % init_loc, 0)
    ea = ea2
    range_len, ea2 = read_enc_val(ea, aug.fde_encoding & 0x0F, True)
    if range_len in (None, ida_idaapi.BADADDR):
      _set_skip_diag(start, "bad_range_length", "Unable to decode FDE range length", fde_encoding = aug.fde_encoding & 0x0F, field_ea = ea, cie_ea = cie_ea, init_loc = init_loc)
      return ida_idaapi.BADADDR, ida_idaapi.BADADDR, ida_idaapi.BADADDR
    set_cmt(ea, "Range length=%08X (end=%08X)" % (range_len, range_len + init_loc), 0)
    if range_len:
      make_reloff(ea, init_loc)
    ea = ea2
    lsda_ptr = 0
    lsda_info = None
    if aug.aug_present:
      augm_len, ea = format_leb128(ea, "Augmentation data length")
      if aug.lsda_encoding != DW_EH_PE_omit:
        lsda_ptr, ea2 = read_enc_val(ea, aug.lsda_encoding, True, text_ea = text_base, data_ea = data_base, funcrel_ea = init_loc)
        set_cmt(ea, "L: LSDA pointer=%08X" % lsda_ptr, 0)
        if lsda_ptr:
          lsda_info = format_lsda(lsda_ptr, init_loc, False)
        ea = ea2
    instr_length = end_ea - ea
    if instr_length > 0:
      format_byte(ea, "CFE Instructions")
      make_array(ea, instr_length)
    else:
      print("%08X: insn_len = %d?!" % (ea, instr_length))
    loc_start, loc_end = init_loc, init_loc + range_len
    _last_fde_info = {
      "kind": "fde",
      "entry_ea": start,
      "end_ea": end_ea,
      "loc_start": loc_start,
      "loc_end": loc_end,
      "lsda_ptr": lsda_ptr if lsda_ptr else ida_idaapi.BADADDR,
      "lsda_end": (lsda_info or {}).get("end_ea", ida_idaapi.BADADDR) if lsda_ptr else ida_idaapi.BADADDR,
      "lsda_entries": int((lsda_info or {}).get("entries", 0)) if lsda_ptr else 0,
      "lsda_callsites": list((lsda_info or {}).get("callsites", [])) if lsda_ptr else [],
      "cie_ea": cie_ea,
    }
  return loc_start, loc_end, end_ea
