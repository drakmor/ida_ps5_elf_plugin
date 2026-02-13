import sys, os
import struct
import hashlib
import re
import json
import traceback

import ida_allins
import ida_auto
import ida_bytes
import ida_diskio
import ida_entry
import ida_funcs
import ida_hexrays
import ida_ida
import ida_idaapi
import ida_idp
import ida_kernwin
import ida_nalt
import ida_name
import ida_netnode
import ida_search
import ida_segment
import ida_typeinf
import ida_ua
import ida_xref

import idc
import idautils

from collections import OrderedDict
from io import BytesIO
from pprint import pprint

def as_uint8(x):
	return x & 0xFF

def as_uint16(x):
	return x & 0xFFFF

def as_uint32(x):
	return x & 0xFFFFFFFF

def as_uint64(x):
	return x & 0xFFFFFFFFFFFFFFFF

def align_up(x, alignment):
	return (x + (alignment - 1)) & ~(alignment - 1)

def align_down(x, alignment):
	return x & ~(alignment - 1)

def hexdump(data, cols=16, addr=0):
	byte_filter = ''.join([(len(repr(chr(x))) == 3) and chr(x) or '.' for x in range(256)])
	lines = []

	for c in range(0, len(data), cols):
		chunk = data[c:c + cols]
		hex_data = ' '.join(['%02x' % x for x in chunk])
		printable = ''.join(['%s' % ((x <= 127 and byte_filter[x]) or '.') for x in chunk])
		lines.append('%08x %-*s %s' % (addr + c, cols * 3, hex_data, printable))

	print('\n'.join(lines))

def determine_simple_type(type_decl):
	type_decl = type_decl.strip()
	return {
		'uint8_t': 'uint8_t',
		'__uint8': 'uint8_t',
		'unsigned int8_t': 'uint8_t',
		'unsigned __int8': 'uint8_t',
		'unsigned char': 'uint8_t',
		'byte': 'uint8_t',
		'int8_t': 'int8_t',
		'__int8': 'int8_t',
		'signed int8_t': 'int8_t',
		'signed __int8': 'int8_t',
		'char': 'int8_t',

		'uint16_t': 'uint16_t',
		'__uint16': 'uint16_t',
		'unsigned int16_t': 'uint16_t',
		'unsigned __int16': 'uint16_t',
		'unsigned short': 'uint16_t',
		'Elf64_Half': 'uint16_t',
		'Elf64_Section': 'uint16_t',
		'int16_t': 'int16_t',
		'__int16': 'int16_t',
		'signed int16_t': 'int16_t',
		'signed __int16': 'int16_t',
		'short': 'int16_t',

		'uint32_t': 'uint32_t',
		'__uint32': 'uint32_t',
		'unsigned int32_t': 'uint32_t',
		'unsigned __int32': 'uint32_t',
		'unsigned int': 'uint32_t',
		'Elf64_Word': 'uint32_t',
		'int32_t': 'int32_t',
		'__int32': 'int32_t',
		'signed int32_t': 'int32_t',
		'signed __int32': 'int32_t',
		'int': 'int32_t',
		'Elf64_Sword': 'int32_t',

		'uint64_t': 'uint64_t',
		'__uint64': 'uint64_t',
		'unsigned int64_t': 'uint64_t',
		'unsigned __int64': 'uint64_t',
		'unsigned long': 'uint64_t',
		'unsigned long long': 'uint64_t',
		'Elf64_Addr': 'uint64_t',
		'Elf64_Off': 'uint64_t',
		'Elf64_Xword': 'uint64_t',
		'size_t': 'uint64_t',
		'int64_t': 'int64_t',
		'__int64': 'int64_t',
		'signed int64_t': 'int64_t',
		'signed __int64': 'int64_t',
		'long': 'int64_t',
		'long long': 'int64_t',
		'Elf64_Sxword': 'int64_t',
	}.get(type_decl, None)

def unpack_by_type(data, size, type_info):
	assert len(data) >= size

	data = data[:size]
	endian = '>' if ida_ida.inf_is_be() else '<'

	def _simple_name(ti):
		type_name = ti.dstr()
		final_type_name = ti.get_final_type_name()
		if final_type_name is None:
			final_type_name = type_name
		return determine_simple_type(final_type_name)

	def _fmt_for_type(ti):
		final_type_name = _simple_name(ti)
		if final_type_name == 'uint8_t':
			return 'B'
		if final_type_name == 'int8_t':
			return 'b'
		if final_type_name == 'uint16_t':
			return 'H'
		if final_type_name == 'int16_t':
			return 'h'
		if final_type_name == 'uint32_t':
			return 'I'
		if final_type_name == 'int32_t':
			return 'i'
		if final_type_name == 'uint64_t':
			return 'Q'
		if final_type_name == 'int64_t':
			return 'q'
		if final_type_name == 'float':
			return 'f'
		if final_type_name == 'double':
			return 'd'
		if ti.is_ptr():
			return 'Q' if ida_ida.inf_is_64bit() else 'I'
		return None

	def _unpack_scalar(raw, fmt):
		if not fmt:
			return raw
		stride = struct.calcsize(fmt)
		if stride <= 0:
			return raw
		count = len(raw) // stride
		if count > 1:
			return list(struct.unpack('%s%d%s' % (endian, count, fmt), raw[:count * stride]))
		if count == 1:
			return struct.unpack('%s%s' % (endian, fmt), raw[:stride])[0]
		return []

	# Arrays: decode per-element recursively when possible.
	if type_info.is_array():
		elem_ti = type_info.get_array_element()
		try:
			elem_sz = int(elem_ti.get_size())
		except Exception:
			elem_sz = 0
		if elem_sz > 0 and size >= elem_sz and size % elem_sz == 0:
			count = size // elem_sz
			out = []
			for i in range(count):
				chunk = data[i * elem_sz:(i + 1) * elem_sz]
				v, _ = unpack_by_type(chunk, elem_sz, elem_ti)
				out.append(v)
			return out, size
		# Fallback: try scalar format directly for simple arrays.
		fmt = _fmt_for_type(elem_ti)
		if fmt is not None:
			return _unpack_scalar(data, fmt), size
		return data, size

	# Scalars and pointers.
	fmt = _fmt_for_type(type_info)
	if fmt is not None:
		return _unpack_scalar(data, fmt), size

	# Enums/bool and other scalar-like fields: decode by width when possible.
	try:
		is_enum = bool(type_info.is_enum())
	except Exception:
		is_enum = False
	try:
		is_bool = bool(type_info.is_bool())
	except Exception:
		is_bool = False

	if is_bool and size >= 1:
		return bool(data[0]), size

	if is_enum or size in (1, 2, 4, 8):
		int_fmt = {
			1: 'B',
			2: 'H',
			4: 'I',
			8: 'Q',
		}.get(size, None)
		if int_fmt is not None:
			return struct.unpack('%s%s' % (endian, int_fmt), data[:size])[0], size

	# Keep raw bytes for unknown/compound types.
	return data, size

def get_struct_size(name):
	assert isinstance(name, str)

	type_id = ida_typeinf.get_named_type_tid(name)
	type_info = ida_typeinf.tinfo_t()
	if type_id == ida_idaapi.BADADDR or not type_info.get_type_by_tid(type_id) or not type_info.is_udt():
		raise RuntimeError('Structure not found: %s' % name)

	return type_info.get_size()

def parse_struct(name, data):
	assert isinstance(name, str)
	assert isinstance(data, bytes)

	type_id = ida_typeinf.get_named_type_tid(name)
	type_info = ida_typeinf.tinfo_t()
	if type_id == ida_idaapi.BADADDR or not type_info.get_type_by_tid(type_id) or not type_info.is_udt():
		raise RuntimeError('Structure not found: %s' % name)

	total_size = type_info.get_size()
	assert len(data) >= total_size

	udt = ida_typeinf.udt_type_data_t()
	assert type_info.get_udt_details(udt)
	count = type_info.get_udt_nmembers()

	#if type_info.is_typedef():
	#	return None

	fields = OrderedDict()

	for idx, udm in enumerate(udt):
		if udm.is_gap():
			continue

		member_name = udm.name
		member_offset = udm.offset // 8
		member_size = udm.size // 8
		member_type_info = udm.type

		value_data = data[member_offset:member_offset + member_size]

		info = unpack_by_type(value_data, member_size, member_type_info)

		fields[member_name] = info[0]

	return fields

def check_insn_format(ea, mnem, operands=[]):
	if ida_ua.print_insn_mnem(ea).lower() != mnem.lower():
		return False

	match = True

	for i, (needed_type, needed_value) in enumerate(operands):
		if needed_type is None:
			continue
		real_type = idc.get_operand_type(ea, i)
		if real_type != needed_type:
			match = False
			break

		if needed_value is None:
			continue
		if isinstance(needed_value, str):
			# XXX: Cannot use ida_ua.print_operand because it returns garbage data.
			value = idc.print_operand(ea, i).lower().strip()
			needed_value = needed_value.lower().strip()
		else:
			value = idc.get_operand_value(ea, i)

		if value != needed_value:
			match = False
			break

	return match

def read_cstring_at(ea, encoding='utf-8'):
	def read_raw(max_len=0x200):
		buf = bytearray()
		for i in range(max_len):
			b = ida_bytes.get_byte(ea + i)
			if b in [None, ida_idaapi.BADADDR]:
				break
			if b == 0:
				break
			buf.append(b & 0xFF)
		return bytes(buf)

	length = ida_bytes.get_max_strlit_length(ea, ida_nalt.STRTYPE_C)
	data = None
	try:
		if length and length != ida_idaapi.BADADDR:
			data = ida_bytes.get_strlit_contents(ea, length, ida_nalt.STRTYPE_C)
	except Exception:
		data = None

	if not data:
		data = read_raw()

	if encoding is not None and isinstance(data, (bytes, bytearray)):
		try:
			return data.decode(encoding, errors='replace')
		except Exception:
			return data.decode('utf-8', errors='replace')
	return data

def refresh_views():
	ida_kernwin.refresh_idaview_anyway()

	widget = ida_kernwin.get_current_widget()
	vu = ida_hexrays.get_widget_vdui(widget)
	if vu:
		vu.refresh_ctext()

def sha1(data):
	return hashlib.sha1(data).digest()

def _ida_is_name_free(ea, name):
	if not name:
		return False
	other_ea = ida_name.get_name_ea(ida_idaapi.BADADDR, name)
	return other_ea in [ida_idaapi.BADADDR, ea]

def set_name_unique(ea, name, flags=ida_name.SN_NOCHECK, fallback_names=None):
	"""
	Set a name without triggering "name already used" errors.

	Returns the final name used, or None if nothing was set.
	"""
	if name is None:
		return None
	name = str(name).strip()
	if not name:
		return None

	if fallback_names is None:
		fallback_names = []

	# If it already has the intended name, keep it.
	try:
		if ida_name.get_name(ea) == name:
			return name
	except Exception:
		pass

	nowarn = ida_name.SN_NOWARN if hasattr(ida_name, 'SN_NOWARN') else 0
	set_flags = flags | nowarn

	def try_set(candidate):
		if not candidate:
			return None
		if not _ida_is_name_free(ea, candidate):
			return None
		if ida_name.set_name(ea, candidate, set_flags):
			return candidate
		return None

	# First: preferred and fallbacks (when free).
	for candidate in [name] + list(fallback_names):
		used = try_set(candidate)
		if used is not None:
			return used

	# Second: make it unique by suffixing with address/counter.
	base = name
	used = try_set('%s_%X' % (base, ea))
	if used is not None:
		return used

	for i in range(1, 1000):
		used = try_set('%s_%X_%d' % (base, ea, i))
		if used is not None:
			return used

	return None


class ObjectInfo(object):
	ROLE_UNKNOWN = 0
	ROLE_IMPORT = (1 << 0)
	ROLE_EXPORT = (1 << 1)

	AUTO_EXPORT = (1 << 0)
	WEAK_EXPORT = (1 << 1)
	LOOSE_IMPORT = (1 << 3)

	CANT_STOP = (1 << 0)
	EXCLUSIVE_LOAD = (1 << 1)
	EXCLUSIVE_START = (1 << 2)
	CAN_RESTART = (1 << 3)
	CAN_RELOCATE = (1 << 4)
	CANT_SHARE = (1 << 5)

	ATTR_MASK = 0xFFFFFFFFFFFF
	EXPORT_ATTR_MASK = AUTO_EXPORT | WEAK_EXPORT | LOOSE_IMPORT
	IMPORT_ATTR_MASK = EXCLUSIVE_LOAD | CANT_STOP | CAN_RESTART | EXCLUSIVE_START | CANT_SHARE | CAN_RELOCATE

	ENCODING_CHARSET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-'
	DECODING_CHARSET = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3EFF3FFFFF3435363738393A3B3C3DFFFFFFFFFFFFFF000102030405060708090A0B0C0D0E0F10111213141516171819FFFFFFFFFFFF1A1B1C1D1E1F202122232425262728292A2B2C2D2E2F30313233FFFFFFFFFF')

	NID_SUFFIX = bytes.fromhex('518D64A635DED8C1E6B039B1C3E55230')

	def __init__(self):
		self.id = None
		self.version_major = None
		self.version_minor = None
		self.name_offset = None
		self.name = None
		self.attrs = None
		self.role = ObjectInfo.ROLE_UNKNOWN
		self.is_export = None

	def _sync_is_export(self):
		# Backward-compatible boolean view used by existing code.
		if self.role & ObjectInfo.ROLE_EXPORT:
			self.is_export = True
		elif self.role & ObjectInfo.ROLE_IMPORT:
			self.is_export = False
		else:
			self.is_export = None

	def add_role(self, role):
		self.role |= role
		self._sync_is_export()

	def set_info(self, value, is_export=None):
		self.id = ObjectInfo.obj_id(value)
		self.version_major, self.version_minor = ObjectInfo.obj_version(value)
		self.name_offset = ObjectInfo.obj_name_offset(value)
		if is_export is True:
			self.add_role(ObjectInfo.ROLE_EXPORT)
		elif is_export is False:
			self.add_role(ObjectInfo.ROLE_IMPORT)
		else:
			self._sync_is_export()

	def set_attr(self, value, is_export=None):
		self.id = ObjectInfo.obj_id(value)
		self.attrs = ObjectInfo.obj_attrs(value)

		if is_export is True:
			self.add_role(ObjectInfo.ROLE_EXPORT)
		elif is_export is False:
			self.add_role(ObjectInfo.ROLE_IMPORT)

		mode_export = is_export if is_export is not None else self.is_export
		if mode_export is True:
			if self.attrs & (~ObjectInfo.EXPORT_ATTR_MASK):
				ida_kernwin.warning('Unsupported export attributes: %s' % ObjectInfo.stringify_attrs(self.attrs, True))
		elif mode_export is False:
			if self.attrs & (~ObjectInfo.IMPORT_ATTR_MASK):
				ida_kernwin.warning('Unsupported import attributes: %s' % ObjectInfo.stringify_attrs(self.attrs, False))

	def update_name(self, base_ea):
		assert self.name_offset is not None
		self.name = read_cstring_at(base_ea + self.name_offset)

	def __repr__(self):
		if self.id is not None:
			is_export_s = 'nil' if self.is_export is None else ('1' if self.is_export else '0')
			return 'ObjectInfo(id=0x%x, version=%02d.%02d, name=%s, attrs=%s, role=0x%x, is_export=%s)' % (
				self.id, self.version_major, self.version_minor,
				self.name if self.name else 'nil',
				ObjectInfo.stringify_attrs(self.attrs, bool(self.is_export)),
				self.role,
				is_export_s
			)
		else:
			return 'n/a'

	@staticmethod
	def calculate_nid(x):
		return sha1(x.encode('ascii') + ObjectInfo.NID_SUFFIX)[:8]

	@staticmethod
	def encode_nid(x):
		enc, = struct.unpack('<Q', ObjectInfo.calculate_nid(x))

		result = ObjectInfo.ENCODING_CHARSET[(enc & 0xF) << 2]
		tmp = enc >> 4
		while tmp != 0:
			result += ObjectInfo.ENCODING_CHARSET[tmp & 0x3F]
			tmp = tmp >> 6

		return result[::-1], enc

	@staticmethod
	def decode_nid(x):
		size = len(x)
		assert size == 11

		result = 0

		for i in range(size):
			idx = ord(x[i])
			assert idx < len(ObjectInfo.DECODING_CHARSET)
			value = ObjectInfo.DECODING_CHARSET[idx]
			assert value != 0xFF

			if i == size - 1:
				result = (result << 4) | (value >> 2)
			else:
				result = (result << 6) | value

		return result

	@staticmethod
	def encode_obj_id(x):
		result = ObjectInfo.ENCODING_CHARSET[(x & 0xF) << 2]
		tmp = x >> 4
		while tmp != 0:
			result += ObjectInfo.ENCODING_CHARSET[tmp & 0x3F]
			tmp = tmp >> 6

		return result[::-1]

	@staticmethod
	def decode_obj_id(x):
		size = len(x)
		assert size <= 4

		result = 0

		for i in range(size):
			idx = ord(x[i])
			assert idx < len(ObjectInfo.DECODING_CHARSET)
			value = ObjectInfo.DECODING_CHARSET[idx]
			assert value != 0xFF
			result = (result << 6) | value

		return result

	@staticmethod
	def obj_id(value):
		return (value >> 48) & 0xFFFF

	@staticmethod
	def obj_attrs(value):
		return (value & ObjectInfo.ATTR_MASK)

	@staticmethod
	def obj_name_offset(value):
		return value & ((1 << 32) - 1)

	@staticmethod
	def obj_version(value):
		major, minor = (value >> 32) & 0xFF, (value >> 40) & 0xFF
		return major, minor

	@staticmethod
	def stringify_attrs(attrs, is_export):
		if not attrs:
			return 'none'

		result = []

		if is_export:
			if attrs & ObjectInfo.AUTO_EXPORT:
				result.append('AUTO_EXPORT')
				attrs &= ~ObjectInfo.AUTO_EXPORT
			if attrs & ObjectInfo.WEAK_EXPORT:
				result.append('WEAK_EXPORT')
				attrs &= ~ObjectInfo.WEAK_EXPORT
			if attrs & ObjectInfo.LOOSE_IMPORT:
				result.append('LOOSE_IMPORT')
				attrs &= ~ObjectInfo.LOOSE_IMPORT
		else:
			if attrs & ObjectInfo.CANT_STOP:
				result.append('CANT_STOP')
				attrs &= ~ObjectInfo.CANT_STOP
			if attrs & ObjectInfo.EXCLUSIVE_LOAD:
				result.append('EXCLUSIVE_LOAD')
				attrs &= ~ObjectInfo.EXCLUSIVE_LOAD
			if attrs & ObjectInfo.EXCLUSIVE_START:
				result.append('EXCLUSIVE_START')
				attrs &= ~ObjectInfo.EXCLUSIVE_START
			if attrs & ObjectInfo.CAN_RESTART:
				result.append('CAN_RESTART')
				attrs &= ~ObjectInfo.CAN_RESTART
			if attrs & ObjectInfo.CAN_RELOCATE:
				result.append('CAN_RELOCATE')
				attrs &= ~ObjectInfo.CAN_RELOCATE
			if attrs & ObjectInfo.CANT_SHARE:
				result.append('CANT_SHARE')
				attrs &= ~ObjectInfo.CANT_SHARE
		if attrs != 0:
			result.append('0x%x' % attrs)

		return '|'.join(result)

def load_known_nids(file_name):
	nids = {}

	# Keep behavior deterministic: load only from IDA's cfg directory.
	# Users can place ps5_symbols.txt there to enable NID -> name decoding.
	file_path = os.path.join(ida_diskio.idadir(ida_diskio.CFG_SUBDIR), file_name)
	if not os.path.isfile(file_path):
		ida_kernwin.warning('NID database not found: %s' % file_path)
		return nids

	with open(file_path, 'r') as f:
		for line in f.readlines():
			line = line.rstrip('\r\n').strip()
			if not line:
				continue

			name = line.split(':')
			if name:
				name = name[0]
			else:
				continue

			nid_ascii, nid = ObjectInfo.encode_nid(name)
			nids[nid] = name

			# Try to prepend underscore symbol to symbol, thus getting a new one.
			if name.startswith('_'):
				name = name[1:]
			name = '_' + name
			nid_ascii, nid = ObjectInfo.encode_nid(name)
			nids[nid] = name

	return nids

class ElfUtil(object):
	# Node and tags to find corresponding net node.
	ELF_NODE = '$ elfnode'

	ELF_PHT_TAG = 'p'
	ELF_SHT_TAG = 's'

	# File types.
	ET_LOOS = 0xFE00
	ET_HIOS = 0xFEFF
	ET_SCE_EXEC_ASLR = ET_LOOS + 0x10
	ET_SCE_DYNAMIC = ET_LOOS + 0x18

	# Segment types.
	PT_LOAD = 0x1
	PT_DYNAMIC = 0x2
	PT_NOTE = 0x4
	PT_TLS = 0x7
	PT_GNU_RELRO = 0x6474E552
	PT_GNU_EH_FRAME = 0x6474E550
	PT_SCE_PROCPARAM = 0x61000001
	PT_SCE_MODULE_PARAM = 0x61000002
	PT_SCE_COMMENT = 0x6FFFFF00
	PT_SCE_VERSION = 0x6FFFFF01

	# Segment flags.
	PF_NONE = 0x0
	PF_EXEC = 0x1
	PF_WRITE = 0x2
	PF_READ = 0x4
	PF_READ_WRITE = PF_READ | PF_WRITE

	# Supported dynamic tags.
	DT_LOOS = 0x60000000
	DT_HIOS = 0x6FFFFFFF
	DT_NULL = 0x0
	DT_NEEDED = 0x1
	DT_PLTGOT = 0x3
	DT_INIT = 0xC
	DT_FINI = 0xD
	DT_SONAME = 0xE
	DT_TEXTREL = 0x16
	DT_SCE_IDTABENTSZ = DT_LOOS + 0x5
	DT_SCE_FINGERPRINT = DT_LOOS + 0x1000007
	DT_SCE_ORIGINAL_FILENAME = DT_LOOS + 0x1000009
	DT_SCE_MODULE_INFO = DT_LOOS + 0x100000D
	DT_SCE_NEEDED_MODULE = DT_LOOS + 0x100000F
	DT_SCE_MODULE_ATTR = DT_LOOS + 0x1000011
	DT_SCE_EXPORT_LIB = DT_LOOS + 0x1000013
	DT_SCE_IMPORT_LIB = DT_LOOS + 0x1000015
	DT_SCE_EXPORT_LIB_ATTR = DT_LOOS + 0x1000017
	DT_SCE_IMPORT_LIB_ATTR = DT_LOOS + 0x1000019
	DT_61000027 = DT_LOOS + 0x1000027 # TODO: Is it related to PLTGOT?
	DT_SCE_ORIGINAL_FILENAME_PPR = DT_LOOS + 0x1000041
	DT_SCE_MODULE_INFO_PPR = DT_LOOS + 0x1000043
	DT_SCE_NEEDED_MODULE_PPR = DT_LOOS + 0x1000045
	DT_SCE_IMPORT_LIB_PPR = DT_LOOS + 0x1000047
	DT_SCE_EXPORT_LIB_PPR = DT_LOOS + 0x1000049

	# Skipped dynamic tags.
	DT_PLTRELSZ = 0x2
	DT_HASH = 0x4
	DT_STRTAB = 0x5
	DT_SYMTAB = 0x6
	DT_RELA = 0x7
	DT_RELASZ = 0x8
	DT_RELAENT = 0x9
	DT_STRSZ = 0xA
	DT_SYMENT = 0xB
	DT_PLTREL = 0x14
	DT_DEBUG = 0x15
	DT_JMPREL = 0x17
	DT_INIT_ARRAY = 0x19
	DT_FINI_ARRAY = 0x1A
	DT_INIT_ARRAYSZ = 0x1B
	DT_FINI_ARRAYSZ = 0x1C
	DT_PREINIT_ARRAY = 0x20
	DT_PREINIT_ARRAYSZ = 0x21
	DT_61000025 = DT_LOOS + 0x1000025
	DT_61000029 = DT_LOOS + 0x1000029
	DT_6100002B = DT_LOOS + 0x100002B
	DT_6100002D = DT_LOOS + 0x100002D
	DT_6100002F = DT_LOOS + 0x100002F
	DT_61000031 = DT_LOOS + 0x1000031
	DT_61000033 = DT_LOOS + 0x1000033
	DT_61000035 = DT_LOOS + 0x1000035
	DT_61000037 = DT_LOOS + 0x1000037
	DT_61000039 = DT_LOOS + 0x1000039
	DT_6100003B = DT_LOOS + 0x100003B
	DT_SCE_HASHSZ = DT_LOOS + 0x100003D
	DT_SCE_SYMTABSZ = DT_LOOS + 0x100003F
	DT_RELACOUNT = DT_LOOS + 0xFFFFFF9
	DT_FLAGS_1 = DT_LOOS + 0xFFFFFFB

	# Obsoleted dynamic tags.
	DT_SYMBOLIC = 0x10
	DT_FLAGS = 0x1E

	# Unsupported dynamic tags.
	DT_RPATH = 0xF
	DT_REL = 0x11
	DT_RELSZ = 0x12
	DT_RELENT = 0x13
	DT_BIND_NOW = 0x18
	DT_RUNPATH = 0x1D
	DT_ENCODING = 0x1F
	DT_61000008 = DT_LOOS + 0x1000008
	DT_6100000A = DT_LOOS + 0x100000A
	DT_6100000B = DT_LOOS + 0x100000B
	DT_6100000C = DT_LOOS + 0x100000C
	DT_6100000E = DT_LOOS + 0x100000E
	DT_61000010 = DT_LOOS + 0x1000010
	DT_61000012 = DT_LOOS + 0x1000012
	DT_61000014 = DT_LOOS + 0x1000014
	DT_61000016 = DT_LOOS + 0x1000016
	DT_61000018 = DT_LOOS + 0x1000018
	DT_6100001A = DT_LOOS + 0x100001A
	DT_6100001B = DT_LOOS + 0x100001B
	DT_6100001C = DT_LOOS + 0x100001C
	DT_SCE_STUB_MODULE_NAME = DT_LOOS + 0x100001D
	DT_6100001E = DT_LOOS + 0x100001E
	DT_SCE_STUB_MODULE_VERSION = DT_LOOS + 0x100001F
	DT_61000020 = DT_LOOS + 0x1000020
	DT_SCE_STUB_LIBRARY_NAME = DT_LOOS + 0x1000021
	DT_61000022 = DT_LOOS + 0x1000022
	DT_SCE_STUB_LIBRARY_VERSION = DT_LOOS + 0x1000023
	DT_61000024 = DT_LOOS + 0x1000024
	DT_61000026 = DT_LOOS + 0x1000026
	DT_61000028 = DT_LOOS + 0x1000028
	DT_6100002A = DT_LOOS + 0x100002A
	DT_6100002C = DT_LOOS + 0x100002C
	DT_6100002E = DT_LOOS + 0x100002E
	DT_61000030 = DT_LOOS + 0x1000030
	DT_61000032 = DT_LOOS + 0x1000032
	DT_61000034 = DT_LOOS + 0x1000034
	DT_61000036 = DT_LOOS + 0x1000036
	DT_61000038 = DT_LOOS + 0x1000038
	DT_6100003A = DT_LOOS + 0x100003A
	DT_6100003C = DT_LOOS + 0x100003C
	DT_6100003E = DT_LOOS + 0x100003E
	DT_61000040 = DT_LOOS + 0x1000040
	DT_61000042 = DT_LOOS + 0x1000042
	DT_61000044 = DT_LOOS + 0x1000044
	DT_61000046 = DT_LOOS + 0x1000046
	DT_61000048 = DT_LOOS + 0x1000048

	# Filler for .sce_padding.
	SCE_PADDING_SIZE = 0x10
	SCE_PADDING = b'\xCC' * SCE_PADDING_SIZE

	# Magics for sceProcessParam and sceModuleParam structures.
	SCE_PROCESS_PARAM_MAGIC = b'ORBI'
	SCE_MODULE_PARAM_MAGIC = b'\xBF\xF4\x13\x3C'

	_DT_STR_MAP = {}

	def __init__(self):
		self.elf_node = ida_netnode.netnode(ElfUtil.ELF_NODE)

		if not self.is_inited():
			return

		#print('Parsing elf header.')
		self._parse_ehdr()

		#print('Parsing program headers.')
		self._parse_phdrs()

		#print('Parsing section headers.')
		self._parse_shdrs()

	def find_phdr_by_type(self, type_id, index=0):
		phdrs = []

		for i, phdr in enumerate(self.phdrs):
			p_type = ElfUtil.phdr_type(phdr)
			if p_type != type_id:
				continue
			phdrs.append(phdr)

		return phdrs[index] if index < len(phdrs) else None

	def find_phdr_by_seg(self, seg):
		if not seg:
			return None

		idx = ida_segment.get_segm_num(seg.start_ea)

		#print('Segment #%03d (start=0x%x, end=0x%0x, perm=0x%x)' % (idx, seg.start_ea, seg.end_ea, seg.perm))

		# Try to find a program header which boundaries are exactly the same as in the segment.
		#print('Doing first pass (exact).')
		for i, phdr in enumerate(self.phdrs):
			if self._match_phdr_boundaries_with_seg(i, phdr, seg, True):
				return phdr

		# Now try to find a program header which boundaries includes the segment boundaries.
		#print('Doing second pass (inexact).')
		for i, phdr in enumerate(self.phdrs):
			if self._match_phdr_boundaries_with_seg(i, phdr, seg, False):
				return phdr

		return None

	def is_inited(self):
		if self.elf_node.valobj() is None:
			return False
		node = ida_netnode.netnode(ps5_elf_plugin_t.PROSPERO_NET_NODE)
		return ida_netnode.exist(node)

	@staticmethod
	def phdr_type(phdr):
		for name in ['p_type', '_p_type', '__p_type']:
			if name in phdr:
				return phdr[name]
		return None

	@staticmethod
	def stringify_phdr_type(type_id):
		return {
			ElfUtil.PT_LOAD: 'PT_LOAD',
			ElfUtil.PT_DYNAMIC: 'PT_DYNAMIC',
			ElfUtil.PT_NOTE: 'PT_NOTE',
			ElfUtil.PT_TLS: 'PT_TLS',
			ElfUtil.PT_GNU_RELRO: 'PT_GNU_RELRO',
			ElfUtil.PT_GNU_EH_FRAME: 'PT_GNU_EH_FRAME',
			ElfUtil.PT_SCE_PROCPARAM: 'PT_SCE_PROCPARAM',
			ElfUtil.PT_SCE_MODULE_PARAM: 'PT_SCE_MODULE_PARAM',
			ElfUtil.PT_SCE_COMMENT: 'PT_SCE_COMMENT',
			ElfUtil.PT_SCE_VERSION: 'PT_SCE_VERSION',
		}.get(type_id, '0x%08x' % type_id)

	@staticmethod
	def stringify_phdr_flags(flags):
		result = []
		if flags == ElfUtil.PF_NONE:
			result.append('PF_NONE')
		else:
			if flags & ElfUtil.PF_READ:
				result.append('PF_READ')
			if flags & ElfUtil.PF_WRITE:
				result.append('PF_WRITE')
			if flags & ElfUtil.PF_EXEC:
				result.append('PF_EXEC')
		return '|'.join(result)

	@staticmethod
	def stringify_dyn_tag(tag):
		return ElfUtil._DT_STR_MAP.get(tag, '0x%x' % tag)

	@staticmethod
	def phdr_flags_from_perm(perm):
		flags = 0
		if perm & ida_segment.SEGPERM_READ:
			flags |= ElfUtil.PF_READ
		if perm & ida_segment.SEGPERM_WRITE:
			flags |= ElfUtil.PF_WRITE
		if perm & ida_segment.SEGPERM_EXEC:
			flags |= ElfUtil.PF_EXEC
		return flags

	def _match_phdr_boundaries_with_seg(self, idx, phdr, seg, exact):
		p_type, seg_flags = ElfUtil.phdr_type(phdr), ElfUtil.phdr_flags_from_perm(seg.perm)
		va_start, va_end = phdr['p_vaddr'], phdr['p_vaddr'] + phdr['p_memsz']

		info_str = 'type=0x%x(%s), flags=0x%x(%s), offset=0x%x, va_start=0x%x, va_end=0x%x, filesz=0x%x, memsz=0x%x' % (
			p_type, ElfUtil.stringify_phdr_type(p_type),
			phdr['p_flags'], ElfUtil.stringify_phdr_flags(phdr['p_flags']),
			phdr['p_offset'],
			va_start, va_end,
			phdr['p_filesz'], phdr['p_memsz']
		)

		if p_type not in [ElfUtil.PT_LOAD, ElfUtil.PT_DYNAMIC, ElfUtil.PT_SCE_PROCPARAM, ElfUtil.PT_SCE_MODULE_PARAM, ElfUtil.PT_GNU_EH_FRAME, ElfUtil.PT_TLS]:
			#print('Skipping phdr #%03d (%s): type mismatch (0x%x)' % (idx, info_str, p_type))
			return False

		if seg_flags != phdr['p_flags']:
			#print('Skipping phdr #%03d (%s): flags mismatch (segment: 0x%x, phdr: 0x%x)' % (idx, info_str, seg_flags, phdr['p_flags']))
			return False

		result = (va_start == seg.start_ea and va_end == seg.end_ea) if exact else ((va_start <= seg.start_ea < va_end) and (va_start < seg.end_ea <= va_end))
		if not result:
			#print('Skipping phdr #%03d (%s): %s addresses mismatch' % (idx, info_str, 'exact' if exact else 'inexact'))
			return False

		#print('Matched phdr #%03d (%s).' % (idx, info_str))

		return True

	def _parse_ehdr(self):
		data = self.elf_node.valobj()
		self.ehdr = parse_struct('Elf64_Ehdr', data)

	def _parse_phdrs(self):
		self.phdrs = []

		i = 0
		while self.elf_node.supval(i, ElfUtil.ELF_PHT_TAG) is not None:
			data = self.elf_node.supval(i, ElfUtil.ELF_PHT_TAG)
			phdr = parse_struct('Elf64_Phdr', data)
			self.phdrs.append(phdr)
			i += 1

	def _parse_shdrs(self):
		self.shdrs = []

		i = 0
		while self.elf_node.supval(i, ElfUtil.ELF_SHT_TAG) is not None:
			data = self.elf_node.supval(i, ElfUtil.ELF_SHT_TAG)
			shdr = parse_struct('Elf64_Shdr', data)
			self.shdrs.append(shdr)
			i += 1

for key in dir(ElfUtil):
	if not key.startswith('DT_') or key in ['DT_LOOS', 'DT_HIOS']:
		continue

	int_value = getattr(ElfUtil, key)
	if int_value >= ElfUtil.DT_LOOS and int_value <= ElfUtil.DT_HIOS:
		str_value = '%s(DT_LOOS+0x%x)' % (key, int_value - ElfUtil.DT_LOOS)
	else:
		str_value = '%s(0x%x)' % (key, int_value)

	ElfUtil._DT_STR_MAP[int_value] = str_value

class ElfTable(object):
	def __init__(self, ea=ida_idaapi.BADADDR, size=ida_idaapi.BADADDR, entry_size=ida_idaapi.BADADDR, entry_count=ida_idaapi.BADADDR):
		self.ea = ea
		self.size = size
		self.entry_size = entry_size
		self.entry_count = entry_count

	def type_name(self):
		return self.__class__.__name__

	def struct_name(self):
		return None

	def is_loaded(self):
		return self.ea != ida_idaapi.BADADDR and self.size != ida_idaapi.BADADDR

	def is_table_loaded(self):
		return self.is_loaded() and self.entry_size != ida_idaapi.BADADDR

	def get_entry(self, idx):
		assert self.is_table_loaded()
		assert self.struct_name() is not None

		count = self.get_num_entries()
		assert idx >= 0 and idx < count

		data = ida_bytes.get_bytes(self.ea + idx * self.entry_size, self.entry_size)
		assert len(data) == self.entry_size

		entry = parse_struct(self.struct_name(), data)

		return entry

	def get_num_entries(self):
		# XXX: We do not rely on entry count because it could be not set or may a wrong value.
		return self.size // self.entry_size

	def __repr__(self):
		params = []

		if self.ea != ida_idaapi.BADADDR:
			params.append('ea=0x%x' % self.ea)
		if self.size != ida_idaapi.BADADDR:
			params.append('size=0x%x' % self.size)
		if self.entry_size != ida_idaapi.BADADDR:
			params.append('entry_size=0x%x' % self.entry_size)
			params.append('real_entry_count=%d' % self.get_num_entries())
		if self.entry_count != ida_idaapi.BADADDR:
			params.append('entry_count=%d' % self.entry_count)

		return '%s(%s)' % (self.type_name(), ', '.join(params))

class RelaRelocTable(ElfTable):
	R_AMD64_NONE = 0
	R_AMD64_64 = 1
	R_AMD64_PC32 = 2
	R_AMD64_GOT32 = 3
	R_AMD64_PLT32 = 4
	R_AMD64_COPY = 5
	R_AMD64_GLOB_DAT = 6
	R_AMD64_JUMP_SLOT = 7
	R_AMD64_RELATIVE = 8
	R_AMD64_GOTPCREL = 9
	R_AMD64_32 = 10
	R_AMD64_32S = 11
	R_AMD64_16 = 12
	R_AMD64_PC16 = 13
	R_AMD64_8 = 14
	R_AMD64_PC8 = 15
	R_AMD64_DTPMOD64 = 16
	R_AMD64_DTPOFF64 = 17
	R_AMD64_TPOFF64 = 18
	R_AMD64_TLSGD = 19
	R_AMD64_TLSLD = 20
	R_AMD64_DTPOFF32 = 21
	R_AMD64_GOTTPOFF = 22
	R_AMD64_TPOFF32 = 23
	R_AMD64_PC64 = 24
	R_AMD64_GOTOFF64 = 25
	R_AMD64_GOTPC32 = 26

	class Record(object):
		def __init__(self, entry):
			self.entry = entry

		def get_symbol_idx(self):
			return as_uint64(self.entry['r_info']) >> 32

		def get_type(self):
			return as_uint32(self.entry['r_info'])

		def __repr__(self):
			params = []

			if self.entry is not None:
				params.append('entry=%s' % repr(self.entry))

			return 'Record(%s)' % ', '.join(params)

	def type_name(self):
		return 'ELF RELA Relocation Table'

	def struct_name(self):
		return 'Elf64_Rela'

class JmpRelRelocTable(RelaRelocTable):
	class Record(RelaRelocTable.Record):
		"""
		JMPREL decoder with compatibility fallback.

		On some IDA type packs/builds, Elf64_Rela can effectively behave as if
		r_info/r_addend were swapped when parsed through type metadata. In that case
		get_type() becomes 0xFFFFFFFF for all entries. Prefer the field that yields
		a plausible x86-64 relocation type.
		"""
		def _get_info_value(self):
			info = as_uint64(self.entry.get('r_info', 0))
			rt = as_uint32(info)
			# Common valid range for x86-64 reloc types used in PS5 ELFs.
			if rt != 0xFFFFFFFF and rt <= 0x100:
				return info

			# Fallback: treat r_addend as encoded r_info when layouts appear swapped.
			alt = as_uint64(self.entry.get('r_addend', 0))
			alt_rt = as_uint32(alt)
			if alt_rt != 0xFFFFFFFF and alt_rt <= 0x100:
				return alt

			return info

		def get_symbol_idx(self):
			return as_uint64(self._get_info_value()) >> 32

		def get_type(self):
			return as_uint32(self._get_info_value())

	def type_name(self):
		return 'ELF JMPREL Relocation Table'

	def struct_name(self):
		# JMPREL can be either Elf64_Rel or Elf64_Rela depending on DT_PLTREL.
		try:
			if self.entry_size == get_struct_size('Elf64_Rel'):
				return 'Elf64_Rel'
		except Exception:
			pass
		return 'Elf64_Rela'

class SymbolTable(ElfTable):
	STB_LOCAL = 0
	STB_GLOBAL = 1
	STB_WEAK = 2

	STT_NOTYPE = 0
	STT_OBJECT = 1
	STT_FUNC = 2
	STT_SECTION = 3
	STT_FILE = 4
	STT_COMMON = 5
	STT_TLS = 6

	SHN_UNDEF = 0

	@staticmethod
	def sanitize_name(name):
		return re.sub(r'[^a-zA-Z0-9_]', '_', name)

	class Symbol(object):
		def __init__(self, entry):
			self.entry = entry
			self.module_name = None
			self.library_name = None
			self.symbol_name = None
			self.is_export = None

		def set_descriptor(self, module_name, library_name, symbol_name, is_export):
			self.module_name = module_name
			self.library_name = library_name
			self.symbol_name = symbol_name
			self.is_export = is_export

		def has_descriptor(self):
			return self.module_name is not None and self.library_name is not None and self.symbol_name is not None

		def get_binding(self):
			return as_uint8(self.entry['st_info']) >> 4

		def get_type(self):
			return as_uint8(self.entry['st_info']) & 0xF

		@property
		def is_undef(self):
			# Undefined dynsym symbols have SHN_UNDEF (0).
			try:
				return as_uint16(self.entry.get('st_shndx', 0)) == SymbolTable.SHN_UNDEF
			except Exception:
				return False

		def is_notype(self):
			return self.get_type() == SymbolTable.STT_NOTYPE

		def _get_name(self, kind='simple'):
			module_name = SymbolTable.sanitize_name(self.module_name)
			library_name = SymbolTable.sanitize_name(self.library_name)

			if self.is_func(): suffix = 'f'
			elif self.is_object(): suffix = 'o'
			else: suffix = 'u'

			if isinstance(self.symbol_name, str):
				if kind == 'extended':
					symbol_name = SymbolTable.sanitize_name(self.symbol_name)
					if module_name != library_name:
						symbol_name = '%s_%s_%s' % (module_name, library_name, symbol_name)
					else:
						symbol_name = '%s_%s' % (module_name, symbol_name)
				elif kind == 'comment':
					symbol_name = self.symbol_name
					demangled_name = ida_name.demangle_name(symbol_name, idc.get_inf_attr(idc.INF_LONG_DEMNAMES))
					if demangled_name is not None:
						demangled_name = demangled_name.strip()
						if demangled_name:
							symbol_name = demangled_name
				else:
					symbol_name = self.symbol_name
			else:
				# Keep fallback NID names compact/stable:
				# module + NID (without library component).
				symbol_name = 'nid%s_%s_0x%016x' % (suffix, module_name, self.symbol_name)

			return symbol_name

		def get_name(self):
			return self._get_name('simple')

		def get_name_ex(self):
			return self._get_name('extended')

		def get_name_comment(self):
			name = self._get_name('comment')

			if self.is_func():
				type_str = 'Function'
			elif self.is_object():
				type_str = 'Object'
			else:
				type_str = 'Unknown'

			return '\n'.join([
				'%s:' % type_str,
				'  Module: %s' % self.module_name,
				'  Library: %s' % self.library_name,
				'  Name: %s' % name
			])

		def is_local(self):
			return self.get_binding() & SymbolTable.STB_LOCAL

		def is_global(self):
			return self.get_binding() & SymbolTable.STB_GLOBAL

		def is_weak(self):
			return self.get_binding() & SymbolTable.STB_WEAK

		def is_object(self): # Variable, array, etc.
			return self.get_type() == SymbolTable.STT_OBJECT

		def is_func(self): # Method or function.
			return self.get_type() == SymbolTable.STT_FUNC

		def is_tls(self): # TLS stuff
			return self.get_type() == SymbolTable.STT_TLS

		def __repr__(self):
			params = []

			if self.module_name is not None:
				params.append('module_name=%s' % self.module_name)
			if self.library_name is not None:
				params.append('library_name=%s' % self.library_name)
			if self.symbol_name is not None:
				if isinstance(self.symbol_name, str):
					params.append('symbol_name=%s' % self.symbol_name)
				else:
					params.append('symbol_nid=%s' % hex(self.symbol_name))
			if self.is_export is not None:
				params.append('is_export=%d' % self.is_export)

			if self.entry is not None:
				params.append('entry=%s' % repr(self.entry))

			return 'Symbol(%s)' % ', '.join(params)

	def type_name(self):
		return 'ELF Symbol Table'

	def struct_name(self):
		return 'Elf64_Sym'

class StringTable(ElfTable):
	def type_name(self):
		return 'ELF String Table'

	def get_string(self, offset):
		assert self.is_loaded()

		assert offset >= 0 and offset < self.size

		return read_cstring_at(self.ea + offset)

class HashTable(ElfTable):
	def type_name(self):
		return 'ELF Hash Table'

class IdTable(ElfTable):
	def type_name(self):
		return 'ELF ID Table'

class ps5_elf_plugin_t(ida_idaapi.plugin_t):
	flags = ida_idaapi.PLUGIN_PROC
	wanted_name = 'PS5 elf plugin'
	comment = f'{wanted_name} to extend loader functionality'
	wanted_hotkey = ''
	help = ''

	# Inhibit flags for symbol names.
	DEMANGLED_FORM = 0x0EA3FFE7 # MNG_SHORT_FORM | MNG_NOBASEDT | MNG_NOCALLC | MNG_NOCSVOL

	# Inhibit flags for type info comments.
	DEMANGLED_TYPEINFO = 0x06400007 # MNG_LONG_FORM

	# ud2 instruction bytes.
	UD2_INSN_BYTES = b'\x0F\x0B'

	# Netnode to determine if ELF is for Prospero.
	PROSPERO_NET_NODE = '$ prospero'

	# Global plugin settings storage (IDA user dir, shared across projects).
	SETTINGS_FILE_NAME = 'ps5_elf_plugin_settings.json'
	SETTINGS_VERSION = 1
	DEFAULT_SETTINGS = {
		'version': SETTINGS_VERSION,
		'eh_funcs_enable': True,
		'eh_funcs_create_missing': True,
		'eh_funcs_adjust_bounds': True,
		'eh_funcs_clamp_to_next': True,
		'eh_funcs_skip_plt': True,
		'eh_funcs_maxrange': 0x100000,
		'eh_funcs_shrink': False,
		'eh_funcs_verbose': False,
		'gcc_extab_comments': True,
		'lsda_enable': True,
		'lsda_verbose': False,
		'tls_items': False,
		'relro_got': False,
	}

	class UiHooks(ida_kernwin.UI_Hooks):
		def __init__(self, plugin):
			super().__init__()

			self.plugin = plugin

		def ready_to_run(self, *args):
			# UI ready to run (called multiple times).
			return 0

		def database_inited(self, is_new_database, idc_script):
			# It is called multiple times, not really useful.
			return 0

		def plugin_loaded(self, plugin_info):
			#print('Loading plugin: %s' % plugin_info.name)
			return 0

	class IdbHooks(ida_idp.IDB_Hooks):
		def __init__(self, plugin):
			super().__init__()

			self.plugin = plugin

		def loader_finished(self, *args):
			# External file loader finished its work.
			# Use this event to augment the existing loader functionality.
			try:
				self.plugin.pre_initial_analysis()
			except Exception:
				try:
					ida_kernwin.msg('[ps5_elf] pre_initial_analysis failed in loader_finished:\n')
					ida_kernwin.msg(traceback.format_exc() + '\n')
				except Exception:
					pass
			return 0

		def determined_main(self, ea):
			return 0

		def segm_added(self, seg):
			return 0

		def auto_empty_finally(self, *args):
			try:
				self.plugin.post_initial_analysis()
			except Exception:
				try:
					ida_kernwin.msg('[ps5_elf] post_initial_analysis failed in auto_empty_finally:\n')
					ida_kernwin.msg(traceback.format_exc() + '\n')
				except Exception:
					pass
			return 0

	class IdpHooks(ida_idp.IDP_Hooks):
		def __init__(self, plugin):
			super().__init__()

			self.plugin = plugin

		def ev_func_bounds(self, possible_ret_code, func, max_func_end_ea):
			self.plugin.fixup_func_bounds(func, max_func_end_ea)
			return 0

	def __init__(self):
		super().__init__()

		self.settings = None
		self.elf = None
		self.file_type = None
		self.lib_versions = None
		self.prodg_meta_data = None
		self.gnu_build_id = None
		self.soname = None
		self.orig_file_path = None
		self.needed_modules = None
		self.modules = None
		self.libraries = None
		self.relocation_type = None
		self.rela_relative_count = ida_idaapi.BADADDR
		self.rela_reloc_table = None
		self.jmprel_reloc_table = None
		self.symbol_table = None
		self.string_table = None
		self.hash_table = None
		self.id_table = None
		self.got_start_ea = ida_idaapi.BADADDR
		self.got_plt_start_ea = ida_idaapi.BADADDR
		self.init_proc_ea = ida_idaapi.BADADDR
		self.term_proc_ea = ida_idaapi.BADADDR
		self.preinit_array_ea = ida_idaapi.BADADDR
		self.preinit_array_sz = 0
		self.init_array_ea = ida_idaapi.BADADDR
		self.init_array_sz = 0
		self.fini_array_ea = ida_idaapi.BADADDR
		self.fini_array_sz = 0
		self.nids = None
		self.symbols = None
		self._pre_analysis_done = False
		self._post_analysis_done = False
		self._post_analysis_running = False
		self._func_bounds_fixup_active = False
		self._jmprel_info_off = None
		self._tls_templates = []

		self.ui_hooks = ps5_elf_plugin_t.UiHooks(self)
		self.idb_hooks = ps5_elf_plugin_t.IdbHooks(self)
		self.idp_hooks = ps5_elf_plugin_t.IdpHooks(self)

	def _get_global_settings_path(self):
		try:
			user_dir = ida_diskio.get_user_idadir()
		except Exception:
			user_dir = None
		if not user_dir:
			try:
				user_dir = os.path.expanduser('~')
			except Exception:
				user_dir = '.'
		# Keep under "cfg" to match IDA user-level config layout.
		return os.path.join(user_dir, 'cfg', ps5_elf_plugin_t.SETTINGS_FILE_NAME)

	def _settings_sanitize(self, s):
		out = dict(ps5_elf_plugin_t.DEFAULT_SETTINGS)
		try:
			if isinstance(s, dict):
				out.update(s)
		except Exception:
			pass

		# Types/clamps.
		out['version'] = ps5_elf_plugin_t.SETTINGS_VERSION
		out['eh_funcs_enable'] = bool(out.get('eh_funcs_enable', True))
		out['eh_funcs_create_missing'] = bool(out.get('eh_funcs_create_missing', True))
		out['eh_funcs_adjust_bounds'] = bool(out.get('eh_funcs_adjust_bounds', True))
		out['eh_funcs_clamp_to_next'] = bool(out.get('eh_funcs_clamp_to_next', True))
		out['eh_funcs_skip_plt'] = bool(out.get('eh_funcs_skip_plt', True))
		out['eh_funcs_shrink'] = bool(out.get('eh_funcs_shrink', False))
		out['eh_funcs_verbose'] = bool(out.get('eh_funcs_verbose', False))
		out['gcc_extab_comments'] = bool(out.get('gcc_extab_comments', True))
		out['lsda_enable'] = bool(out.get('lsda_enable', True))
		out['lsda_verbose'] = bool(out.get('lsda_verbose', False))
		out['tls_items'] = bool(out.get('tls_items', False))
		out['relro_got'] = bool(out.get('relro_got', False))

		try:
			mr = int(out.get('eh_funcs_maxrange', 0x100000))
		except Exception:
			mr = 0x100000
		# Keep a sane floor/ceiling to avoid pathological workloads.
		mr = max(0x100, min(mr, 0x10000000))
		out['eh_funcs_maxrange'] = mr

		return out

	def _settings_load(self):
		# Load global settings only.
		try:
			path = self._get_global_settings_path()
			if path and os.path.isfile(path):
				with open(path, 'r', encoding='utf-8') as f:
					data = json.load(f)
				return self._settings_sanitize(data)
		except Exception:
			# Fall through to defaults.
			pass

		return dict(ps5_elf_plugin_t.DEFAULT_SETTINGS)

	def _settings_save(self, s):
		s = self._settings_sanitize(s)
		try:
			path = self._get_global_settings_path()
			if not path:
				return False
			dir_name = os.path.dirname(path)
			if dir_name:
				os.makedirs(dir_name, exist_ok=True)
			tmp_path = path + '.tmp'
			with open(tmp_path, 'w', encoding='utf-8') as f:
				json.dump(s, f, sort_keys=True, indent=2)
			os.replace(tmp_path, path)
			return True
		except Exception:
			return False

	def apply_settings_now(self, settings=None):
		"""
		Apply current settings to the active IDB immediately.

		Notes:
		- This is best-effort and is not fully reversible (e.g. created functions/items cannot
		be automatically "unmade" if a setting is disabled later).
		- It only re-runs the settings-driven fixups.
		"""
		if settings is not None:
			self.settings = self._settings_sanitize(settings)
			self._settings_save(self.settings)
		elif self.settings is None:
			self.settings = self._settings_load()

		# Applying analysis fixups only makes sense on a loaded x86-64 ELF database.
		try:
			if ida_ida.inf_get_filetype() != idc.FT_ELF:
				ida_kernwin.warning('Not an ELF database; nothing to apply.')
				return False
			if ida_ida.inf_get_procname() != 'metapc' or ida_ida.inf_is_be() or not ida_ida.inf_is_64bit():
				ida_kernwin.warning('Unsupported database type for apply; expected little-endian x86-64 ELF.')
				return False
		except Exception:
			# If the checks fail, stay conservative.
			return False

		# Ensure elf helper is initialized when called manually.
		if self.elf is None or not getattr(self.elf, 'is_inited', lambda: False)():
			try:
				self.elf = ElfUtil()
			except Exception:
				self.elf = None

		changed = False
		try:
			changed |= bool(self._fixup_funcs_from_eh_frame())
		except Exception:
			pass
		try:
			changed |= bool(self._fixup_lsda_from_eh_frame())
		except Exception:
			pass
		try:
			changed |= bool(self._fixup_tls_template())
		except Exception:
			pass
		try:
			changed |= bool(self._fixup_relro_segments())
		except Exception:
			pass

		if changed:
			try:
				refresh_views()
			except Exception:
				pass

		return changed

	def _try_msg(self, s):
		try:
			ida_kernwin.msg(str(s))
		except Exception:
			pass

	def _show_settings_dialog_qt(self, s):
		"""
		Qt-based settings dialog.
		Returns (ok: bool, new_settings: dict|None)
		"""
		QtWidgets = None
		QtCore = None
		QtGui = None
		try:
			ver = ida_kernwin.get_kernel_version()
		except Exception:
			ver = '0.0'
		try:
			m = re.match(r'^(\\d+)\\.(\\d+)', str(ver))
			vt = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
		except Exception:
			vt = (0, 0)

		# IDA 9.2+ ships with PySide6 by default (preferred).
		if vt >= (9, 2):
			import_order = ('PySide6', 'PyQt5')
		else:
			import_order = ('PyQt5', 'PySide6')

		last_exc = None
		for mod in import_order:
			try:
				if mod == 'PySide6':
					from PySide6 import QtWidgets as _QtWidgets, QtCore as _QtCore, QtGui as _QtGui
				elif mod == 'PyQt5':
					from PyQt5 import QtWidgets as _QtWidgets, QtCore as _QtCore, QtGui as _QtGui
				else:
					continue
				QtWidgets, QtCore, QtGui = _QtWidgets, _QtCore, _QtGui
				last_exc = None
				break
			except Exception as e:
				last_exc = e
				continue
		if QtWidgets is None:
			return False, None

		def mk_chk(label, key, default=False, tooltip=None):
			cb = QtWidgets.QCheckBox(label)
			cb.setChecked(bool(s.get(key, default)))
			if tooltip:
				cb.setToolTip(tooltip)
			return cb

		dlg = QtWidgets.QDialog()
		dlg.setWindowTitle('PS5 ELF Plugin Settings')
		try:
			# Best-effort parenting to keep the dialog on top of IDA.
			tw = ida_kernwin.get_main_window()
			parent = ida_kernwin.PluginForm.TWidgetToPyQtWidget(tw)
			dlg.setParent(parent)
		except Exception:
			pass
		try:
			dlg.setWindowModality(QtCore.Qt.ApplicationModal)
		except Exception:
			dlg.setModal(True)

		root = QtWidgets.QVBoxLayout(dlg)

		gb_eh = QtWidgets.QGroupBox('.eh_frame function recovery')
		eh_l = QtWidgets.QVBoxLayout(gb_eh)

		cb_eh_en = mk_chk('Enable', 'eh_funcs_enable', True, 'Enable .eh_frame-based function recovery')
		cb_eh_create = mk_chk('Create missing functions', 'eh_funcs_create_missing', True, 'Create functions for unwind ranges without functions')
		cb_eh_adjust = mk_chk('Adjust existing bounds', 'eh_funcs_adjust_bounds', True, 'Adjust bounds of existing functions using unwind ranges')
		cb_eh_clamp = mk_chk('Clamp end to next unwind start', 'eh_funcs_clamp_to_next', True, 'Clamp end to the next unwind start to reduce overlaps')
		cb_eh_skipplt = mk_chk('Skip .plt segment', 'eh_funcs_skip_plt', True, 'Ignore unwind ranges located in .plt')
		cb_eh_shrink = mk_chk('Allow shrink ends', 'eh_funcs_shrink', False, 'Allow making function ends smaller if unwind range is shorter')
		cb_eh_verbose = mk_chk('Verbose logging', 'eh_funcs_verbose', False, 'Print verbose log while applying')

		eh_l.addWidget(cb_eh_en)
		eh_l.addWidget(cb_eh_create)
		eh_l.addWidget(cb_eh_adjust)
		eh_l.addWidget(cb_eh_clamp)
		eh_l.addWidget(cb_eh_skipplt)

		form = QtWidgets.QFormLayout()
		form.setLabelAlignment(QtCore.Qt.AlignLeft)
		form.setFormAlignment(QtCore.Qt.AlignTop)
		form.setFieldGrowthPolicy(QtWidgets.QFormLayout.ExpandingFieldsGrow)

		le_max = QtWidgets.QLineEdit()
		le_max.setText('0x%X' % int(s.get('eh_funcs_maxrange', 0x100000)))
		le_max.setPlaceholderText('0x100000')
		try:
			rex = QtCore.QRegularExpression(r'^(0x[0-9a-fA-F]+|[0-9]+)$')
			le_max.setValidator(QtGui.QRegularExpressionValidator(rex, le_max))
		except Exception:
			# Qt binding might not provide QtGui or QRegularExpressionValidator.
			pass

		form.addRow('Max range (hex):', le_max)
		eh_l.addLayout(form)

		eh_l.addWidget(cb_eh_shrink)
		eh_l.addWidget(cb_eh_verbose)

		gb_other = QtWidgets.QGroupBox('Other')
		oth_l = QtWidgets.QVBoxLayout(gb_other)
		cb_gcc_comments = mk_chk('gcc_extab: add comments', 'gcc_extab_comments', True, 'Enable comments generated by gcc_extab CIE/FDE/LSDA formatter')
		cb_lsda_enable = mk_chk('LSDA/.gcc_except_table recovery', 'lsda_enable', True, 'Parse LSDA tables and annotate try/landing pads')
		cb_lsda_verbose = mk_chk('LSDA: verbose logging', 'lsda_verbose', False, 'Print verbose LSDA parsing log')
		cb_tls_items = mk_chk('TLS: create items (noisy)', 'tls_items', False, 'Create TLS template items (may be noisy)')
		cb_relro_got = mk_chk('RELRO: include GOT segments', 'relro_got', False, 'Include GOT segments when handling RELRO')
		oth_l.addWidget(cb_gcc_comments)
		oth_l.addWidget(cb_lsda_enable)
		oth_l.addWidget(cb_lsda_verbose)
		oth_l.addWidget(cb_tls_items)
		oth_l.addWidget(cb_relro_got)

		root.addWidget(gb_eh)
		root.addWidget(gb_other)

		btns = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel)
		btns.button(QtWidgets.QDialogButtonBox.Ok).setText('Save && Apply')
		btns.button(QtWidgets.QDialogButtonBox.Cancel).setText('Cancel')
		root.addWidget(btns)

		def parse_int_auto(x):
			x = (x or '').strip()
			return int(x, 0)  # accepts 123, 0x123

		def on_accept():
			try:
				mr = parse_int_auto(le_max.text())
			except Exception:
				try:
					QtWidgets.QMessageBox.warning(dlg, 'Invalid value', 'Max range must be an integer (e.g., 0x100000).')
				except Exception:
					pass
				return

			ns = {
				'eh_funcs_enable': bool(cb_eh_en.isChecked()),
				'eh_funcs_create_missing': bool(cb_eh_create.isChecked()),
				'eh_funcs_adjust_bounds': bool(cb_eh_adjust.isChecked()),
				'eh_funcs_clamp_to_next': bool(cb_eh_clamp.isChecked()),
				'eh_funcs_skip_plt': bool(cb_eh_skipplt.isChecked()),
				'eh_funcs_maxrange': int(mr),
				'eh_funcs_shrink': bool(cb_eh_shrink.isChecked()),
				'eh_funcs_verbose': bool(cb_eh_verbose.isChecked()),
				'gcc_extab_comments': bool(cb_gcc_comments.isChecked()),
				'lsda_enable': bool(cb_lsda_enable.isChecked()),
				'lsda_verbose': bool(cb_lsda_verbose.isChecked()),
				'tls_items': bool(cb_tls_items.isChecked()),
				'relro_got': bool(cb_relro_got.isChecked()),
			}
			dlg._ps5elf_settings = self._settings_sanitize(ns)
			dlg.accept()

		btns.accepted.connect(on_accept)
		btns.rejected.connect(dlg.reject)

		try:
			rc = dlg.exec_() if hasattr(dlg, 'exec_') else dlg.exec()
		except Exception:
			return False, None

		if rc != QtWidgets.QDialog.Accepted:
			return False, None
		return True, getattr(dlg, '_ps5elf_settings', None)

	def show_settings_dialog(self):
		"""
		Show plugin settings dialog and persist globally.
		"""
		self.settings = self._settings_load()
		s = dict(self.settings)

		try:
			ok, s2 = self._show_settings_dialog_qt(s)
			if ok and isinstance(s2, dict):
				self._settings_save(s2)
				self.settings = s2
				self.apply_settings_now(s2)
				return True
			return False
		except Exception:
			self._try_msg('[ps5_elf] Settings dialog (Qt) failed:\n')
			self._try_msg(traceback.format_exc() + '\n')

		try:
			ida_kernwin.warning('Unable to open settings window (Qt). See Output window for details.')
		except Exception:
			pass
		return False

	def init(self):
		# Cannot be used in terminal mode.
		if not ida_kernwin.is_idaq():
			return ida_idaapi.PLUGIN_SKIP

		if not ida_hexrays.init_hexrays_plugin():
			return ida_idaapi.PLUGIN_SKIP

		print(f'Initializing plugin: {self.wanted_name}')

		file_path = ida_nalt.get_input_file_path()
		file_name = ida_nalt.get_root_filename()

		# Sanity check.
		if ida_ida.inf_get_filetype() != idc.FT_ELF or ida_ida.inf_get_procname() != 'metapc' or ida_ida.inf_is_be() or not ida_ida.inf_is_64bit():
			return ida_idaapi.PLUGIN_SKIP

		# Load needed type info libraries and register standard types.
		idc.add_default_til('gnuunx64')

		standard_types = ['Elf64_Ehdr', 'Elf64_Phdr', 'Elf64_Shdr', 'Elf64_Nhdr', 'Elf64_Rel', 'Elf64_Rela', 'Elf64_Dyn', 'Elf64_Sym']
		for type_name in standard_types:
			idc.import_type(-1, type_name)

		# Read and parse ELF header.
		elf = ElfUtil()
		if elf.is_inited():
			ehdr = elf.ehdr
			is_just_loaded = False
		else:
			ehdr_struct_name = 'Elf64_Ehdr'
			ehdr_size = get_struct_size(ehdr_struct_name)

			phdr_struct_name = 'Elf64_Phdr'
			phdr_size = get_struct_size(phdr_struct_name)

			is_prospero_elf = False

			try:
				with open(file_path, 'rb') as f:
					data = f.read(ehdr_size)

					while True:
						if len(data) != ehdr_size:
							break
						ehdr = parse_struct(ehdr_struct_name, data)

						phdr_offset = ehdr['e_phoff']
						if phdr_offset <= 0:
							break
						f.seek(phdr_offset)

						data = f.read(phdr_size)
						if len(data) != phdr_size:
							break
						# Scan program headers: on some binaries the executable PT_LOAD is not the first PHDR.
						phnum = ehdr.get('e_phnum', 0)
						phentsize = ehdr.get('e_phentsize', phdr_size) or phdr_size
						if phnum <= 0:
							break

						is_exec_load = False
						for j in range(phnum):
							try:
								f.seek(phdr_offset + j * phentsize)
							except Exception:
								break
							data = f.read(phdr_size)
							if len(data) != phdr_size:
								break
							phdr = parse_struct(phdr_struct_name, data)
							phdr_type = ElfUtil.phdr_type(phdr)
							phdr_flags = phdr.get('p_flags', 0)

							if phdr_type == ElfUtil.PT_LOAD and (phdr_flags & ElfUtil.PF_EXEC):
								is_exec_load = True
								break

						if not is_exec_load:
							break

						is_prospero_elf = True
						break
			except Exception as e:
				#print('Got exception during header parsing attempt:', e)
				pass

			if not is_prospero_elf:
				return ida_idaapi.PLUGIN_SKIP
			else:
				node = ida_netnode.netnode()
				node.create(ps5_elf_plugin_t.PROSPERO_NET_NODE)

			is_just_loaded = True

		# Determine file type.
		file_type_str = {
			ElfUtil.ET_SCE_EXEC_ASLR: 'Executable',
			ElfUtil.ET_SCE_DYNAMIC: 'PRX',
		}.get(ehdr['e_type'], None)

		if file_type_str is None:
			return ida_idaapi.PLUGIN_SKIP

		self.file_type = ehdr['e_type']

		print('File type: %s' % file_type_str)

		# Reset members.
		self.lib_versions = {}
		self.prodg_meta_data = {}
		self.soname = None
		self.orig_file_path = None
		self.needed_modules = []
		self.modules = {}
		self.libraries = {}
		self.relocation_type = None
		self.rela_relative_count = ida_idaapi.BADADDR
		self.rela_reloc_table = None
		self.jmprel_reloc_table = None
		self.symbol_table = None
		self.string_table = None
		self.hash_table = None
		self.id_table = None
		self.got_start_ea = ida_idaapi.BADADDR
		self.got_plt_start_ea = ida_idaapi.BADADDR
		self.init_proc_ea = ida_idaapi.BADADDR
		self.term_proc_ea = ida_idaapi.BADADDR
		self.preinit_array_ea = ida_idaapi.BADADDR
		self.preinit_array_sz = 0
		self.init_array_ea = ida_idaapi.BADADDR
		self.init_array_sz = 0
		self.fini_array_ea = ida_idaapi.BADADDR
		self.fini_array_sz = 0
		self._pre_analysis_done = False
		self._post_analysis_done = False
		self._post_analysis_running = False
		self._jmprel_info_off = None
		self._tls_templates = []

		# Load additional type info libraries.
		for name in ['prospero']:
			idc.add_default_til(name)

		# Load known NIDS.
		self.nids = load_known_nids('ps5_symbols.txt')

		self.symbols = []

		# Load additional modules.
		ida_idaapi.require('gcc_extab')

		# Set up analyzer on the first load.
		if is_just_loaded:
			self.setup_analysis()
		else:
			self.elf = elf

		self.ui_hooks.hook()
		self.idb_hooks.hook()
		self.idp_hooks.hook()

		# In some IDA builds, IDB_Hooks.loader_finished can be missed depending on
		# plugin initialization timing. Ensure pre-pass runs on first load anyway.
		if is_just_loaded and not self._pre_analysis_done:
			try:
				self.pre_initial_analysis()
			except Exception:
				try:
					ida_kernwin.msg('[ps5_elf] pre_initial_analysis failed in init:\n')
					ida_kernwin.msg(traceback.format_exc() + '\n')
				except Exception:
					pass

		return ida_idaapi.PLUGIN_KEEP

	def term(self):
		#print(f'Terminating plugin: {self.wanted_name}')

		self.idp_hooks.unhook()
		self.idb_hooks.unhook()
		self.ui_hooks.unhook()

	def setup_analysis(self):
		# Set up common parameters.
		ida_ida.inf_set_ostype(0x6) # BSD OS
		ida_ida.inf_set_demnames(ida_ida.DEMNAM_NAME | ida_ida.DEMNAM_GCC3) # use GCC mangling names

		# Set up compiler parameters.
		ida_ida.inf_set_cc_id(ida_typeinf.COMP_GNU)
		ida_ida.inf_set_cc_cm(ida_typeinf.CM_N64 | ida_typeinf.CM_M_NN | ida_typeinf.CM_CC_FASTCALL)
		ida_ida.inf_set_cc_size_b(1)
		ida_ida.inf_set_cc_size_s(2)
		ida_ida.inf_set_cc_size_i(4)
		ida_ida.inf_set_cc_size_e(4)
		ida_ida.inf_set_cc_size_l(8)
		ida_ida.inf_set_cc_size_ll(8)
		ida_ida.inf_set_cc_size_ldbl(8)
		ida_ida.inf_set_cc_defalign(0)

		# Set up analysis parameters.
		ida_ida.inf_set_mark_code(False) # Do not find functions inside .data segments.
		ida_ida.inf_set_create_func_tails(False) # Don not create function tails.
		ida_ida.inf_set_noflow_to_data(True) # Control flow to data segment is ignored.
		ida_ida.inf_set_rename_jumpfunc(False) # Rename jump functions as J_.

	def _fixup_segment(self, seg):
		image_base = ida_nalt.get_imagebase()

		name = ida_segment.get_segm_name(seg)
		type_id = ida_segment.segtype(seg.start_ea)
		is_exec = (seg.perm & ida_segment.SEGPERM_EXEC) != 0

		print('Fixing up segment at 0x%x (type: %d, perm: 0x%x).' % (seg.start_ea, type_id, seg.perm))

		# Some loaders (or bad heuristics) mark executable segments as DATA; treat EXEC as a bitflag.
		other_text = ida_segment.get_segm_by_name('.text')
		if is_exec and not other_text:
			# Prefer the segment that contains the entrypoint; fallback to image_base.
			start_ip = ida_ida.inf_get_start_ip()
			if start_ip != ida_idaapi.BADADDR and seg.start_ea <= start_ip < seg.end_ea:
				ida_segment.set_segm_name(seg, '.text')
				print('Found .text segment by entrypoint.')
				return True
			if seg.start_ea == image_base:
				ida_segment.set_segm_name(seg, '.text')
				print('Found .text segment.')
				return True
		elif is_exec and other_text and seg.start_ea != other_text.start_ea:
			# IDA often names unnamed segments as segXXXX/LOAD. If there are multiple executable
			# segments, keep them recognizable as .text.* so later fixups can treat them as code.
			seg_name = (name or '').strip()
			seg_name_l = seg_name.lower()
			if seg_name and not seg_name.startswith('.text') and (seg_name_l.startswith('seg') or seg_name_l == 'load'):
				new_name = '.text.%X' % seg.start_ea
				if ida_segment.get_segm_by_name(new_name) is None:
					ida_segment.set_segm_name(seg, new_name)
					print('Found extra code segment: %s' % new_name)
					return True

		if type_id == ida_segment.SEG_CODE:
			# Keep legacy behavior for code-typed segments.
			pass
		elif type_id == ida_segment.SEG_DATA:
			other_seg = ida_segment.get_segm_by_name('.rodata')
			if seg.perm == ida_segment.SEGPERM_READ:
				if not other_seg:
					ida_segment.set_segm_name(seg, '.rodata')
					print('Found .rodata segment.')
					return True
				else:
					if name.lower().strip() == 'note':
						# Keep PT_NOTE segments: they can contain useful metadata (e.g. GNU build-id).
						# Give them a stable name to avoid confusing them with rodata duplicates.
						new_name = '.note'
						if ida_segment.get_segm_by_name(new_name) is not None:
							new_name = '.note.%X' % seg.start_ea
						try:
							ida_segment.set_segm_name(seg, new_name)
							print('Found note segment: %s' % new_name)
						except Exception:
							print('Found note segment.')
						return True
			elif seg.perm == ida_segment.SEGPERM_READ | ida_segment.SEGPERM_WRITE:
				# There are multiple R/W segments and we need more info to recognize them, so skip now and process them later.
				return False
			elif seg.perm == 0:
				other_seg = ida_segment.get_segm_by_name('.dynsym')
				if not other_seg:
					ida_segment.set_segm_name(seg, '.dynsym')
					print('Found .dynsym segment.')
					return True
		elif type_id == ida_segment.SEG_XTRN:
			other_seg = ida_segment.get_segm_by_name('extern')
			if seg.perm == 0 and not other_seg:
				ida_segment.set_segm_name(seg, 'extern')
				print('Found extern segment.')
				return True

		return False

	def _parse_extra_segments(self):
		assert self.elf.is_inited()

		file_path = ida_nalt.get_input_file_path()

		result = False

		dynamic_phdr = self.elf.find_phdr_by_type(ElfUtil.PT_DYNAMIC)

		if dynamic_phdr is not None:
			result |= self._parse_dynamic_segment(dynamic_phdr)

		comment_phdr = self.elf.find_phdr_by_type(ElfUtil.PT_SCE_COMMENT)
		version_phdr = self.elf.find_phdr_by_type(ElfUtil.PT_SCE_VERSION)
		note_phdrs = []
		try:
			for phdr in self.elf.phdrs:
				if ElfUtil.phdr_type(phdr) == ElfUtil.PT_NOTE and as_uint64(phdr.get('p_filesz', 0)) > 0:
					note_phdrs.append(phdr)
		except Exception:
			note_phdrs = []

		if not comment_phdr and not version_phdr and not note_phdrs:
			return result

		with open(file_path, 'rb') as f:
			if comment_phdr is not None:
				f.seek(comment_phdr['p_offset'])
				comment_data = f.read(comment_phdr['p_filesz'])
				if len(comment_data) != comment_phdr['p_filesz']:
					comment_data = None
			else:
				comment_data = None

			if version_phdr is not None:
				f.seek(version_phdr['p_offset'])
				version_data = f.read(version_phdr['p_filesz'])
				if len(version_data) != version_phdr['p_filesz']:
					version_data = None
			else:
				version_data = None

			note_datas = []
			for phdr in note_phdrs:
				try:
					f.seek(phdr['p_offset'])
					data = f.read(phdr['p_filesz'])
					if len(data) != phdr['p_filesz']:
						continue
					note_datas.append((phdr, data))
				except Exception:
					continue

		if comment_data:
			result |= self._parse_comment_segment(comment_data)
		if version_data:
			result |= self._parse_version_segment(version_data)
		for phdr, data in note_datas:
			try:
				base = as_uint64(phdr.get('p_vaddr', ida_idaapi.BADADDR))
				result |= self._parse_note_segment(data, base_ea=base)
			except Exception:
				continue

		return result

	def _parse_dynamic_segment(self, dynamic_phdr):
		print('Processing dynamic segment.')

		struct_name = 'Elf64_Dyn'
		struct_size = get_struct_size(struct_name)

		seg = ida_segment.get_segm_by_name('.dynsym')
		if not seg:
			ida_kernwin.warning('Unable to find .dynsym segment, cannot parse dynamic segment.')
			return False
		dynsym_base_ea = seg.start_ea

		ea = dynamic_phdr['p_vaddr']
		end_ea = dynamic_phdr['p_vaddr'] + dynamic_phdr['p_memsz']

		dyns = []
		while ea < end_ea:
			data = ida_bytes.get_bytes(ea, struct_size)
			if len(data) != struct_size:
				raise RuntimeError('Insufficient data of %s structure: 0x%x (expected: 0x%x)' % (struct_name, len(data), struct_size))

			dyn = parse_struct(struct_name, data)
			if dyn['d_tag'] == ElfUtil.DT_NULL:
				break
			dyns.append(dyn)

			ea += struct_size

		if not dyns:
			print('No dynamic tags found.')
			return True

		self.rela_reloc_table = RelaRelocTable()
		self.jmprel_reloc_table = JmpRelRelocTable()
		self.symbol_table = SymbolTable()
		self.string_table = StringTable()
		self.hash_table = HashTable()
		self.id_table = IdTable()

		print('Dynamic tags:')
		for dyn in dyns:
			tag, value = dyn['d_tag'], dyn['d_un']
			print('  %s: 0x%x' % (ElfUtil.stringify_dyn_tag(tag), value))

			if tag == ElfUtil.DT_NEEDED:
				name = read_cstring_at(dynsym_base_ea + value)
				self.needed_modules.append(name)
			elif tag == ElfUtil.DT_SONAME:
				self.soname = read_cstring_at(dynsym_base_ea + value)
			elif tag in [ElfUtil.DT_SCE_NEEDED_MODULE, ElfUtil.DT_SCE_NEEDED_MODULE_PPR]:
				module_id = ObjectInfo.obj_id(value)
				if module_id not in self.modules:
					self.modules[module_id] = ObjectInfo()
				self.modules[module_id].set_info(value)
				self.modules[module_id].update_name(dynsym_base_ea)
			elif tag in [ElfUtil.DT_SCE_EXPORT_LIB, ElfUtil.DT_SCE_EXPORT_LIB_PPR]:
				library_id = ObjectInfo.obj_id(value)
				if library_id not in self.libraries:
					self.libraries[library_id] = ObjectInfo()
				self.libraries[library_id].set_info(value, True)
				self.libraries[library_id].update_name(dynsym_base_ea)
			elif tag == ElfUtil.DT_SCE_IMPORT_LIB_ATTR:
				library_id = ObjectInfo.obj_id(value)
				if library_id not in self.libraries:
					self.libraries[library_id] = ObjectInfo()
				self.libraries[library_id].set_attr(value, False)
			elif tag in [ElfUtil.DT_SCE_MODULE_INFO, ElfUtil.DT_SCE_MODULE_INFO_PPR]:
				module_id = ObjectInfo.obj_id(value)
				if module_id not in self.modules:
					self.modules[module_id] = ObjectInfo()
				self.modules[module_id].set_info(value, True)
				self.modules[module_id].update_name(dynsym_base_ea)
			elif tag == ElfUtil.DT_SCE_MODULE_ATTR:
				module_id = ObjectInfo.obj_id(value)
				if module_id not in self.modules:
					self.modules[module_id] = ObjectInfo()
				self.modules[module_id].set_attr(value)
			elif tag in [ElfUtil.DT_SCE_ORIGINAL_FILENAME, ElfUtil.DT_SCE_ORIGINAL_FILENAME_PPR]:
				self.orig_file_path = read_cstring_at(dynsym_base_ea + value)
			elif tag in [ElfUtil.DT_SCE_IMPORT_LIB, ElfUtil.DT_SCE_IMPORT_LIB_PPR]:
				library_id = ObjectInfo.obj_id(value)
				if library_id not in self.libraries:
					self.libraries[library_id] = ObjectInfo()
				self.libraries[library_id].set_info(value, False)
				self.libraries[library_id].update_name(dynsym_base_ea)
			elif tag == ElfUtil.DT_SCE_EXPORT_LIB_ATTR:
				library_id = ObjectInfo.obj_id(value)
				if library_id not in self.libraries:
					self.libraries[library_id] = ObjectInfo()
				self.libraries[library_id].set_attr(value, True)
			elif tag == ElfUtil.DT_RELA: # ELF RELA Relocation Table
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.rela_reloc_table.ea = ea
			elif tag == ElfUtil.DT_RELASZ: # ELF RELA Relocation Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.rela_reloc_table.size = size
			elif tag == ElfUtil.DT_RELAENT: # ELF RELA Relocation Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					assert size == get_struct_size(self.rela_reloc_table.struct_name())
					self.rela_reloc_table.entry_size = size
			elif tag == ElfUtil.DT_RELACOUNT: # ELF RELA Relocation Table
				count = as_uint64(value)
				if count != ida_idaapi.BADADDR:
					# DT_RELACOUNT is the number of leading RELATIVE relocations,
					# not necessarily total RELA table entry count.
					self.rela_relative_count = count
			elif tag == ElfUtil.DT_JMPREL: # ELF JMPREL Relocation Table
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.jmprel_reloc_table.ea = ea
			elif tag == ElfUtil.DT_PLTRELSZ: # ELF JMPREL Relocation Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.jmprel_reloc_table.size = size
			elif tag == ElfUtil.DT_PLTGOT:
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.got_plt_start_ea = ea
			elif tag == ElfUtil.DT_PLTREL:
				self.relocation_type = as_uint32(value)
				if self.relocation_type != ElfUtil.DT_REL and self.relocation_type != ElfUtil.DT_RELA:
					ida_kernwin.warning('Unsupported PLT relocation type: 0x%x' % self.relocation_type)
			elif tag == ElfUtil.DT_SYMTAB: # ELF Symbol Table
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.symbol_table.ea = ea
			elif tag == ElfUtil.DT_SCE_SYMTABSZ: # ELF Symbol Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.symbol_table.size = size
			elif tag == ElfUtil.DT_SYMENT: # ELF Symbol Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					assert size == get_struct_size(self.symbol_table.struct_name())
					self.symbol_table.entry_size = size
			elif tag == ElfUtil.DT_STRTAB: # ELF String Table
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.string_table.ea = ea
			elif tag == ElfUtil.DT_STRSZ: # ELF String Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.string_table.size = size
			elif tag == ElfUtil.DT_HASH: # ELF Hash Table
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.hash_table.ea = ea
			elif tag == ElfUtil.DT_SCE_HASHSZ: # ELF Hash Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.hash_table.size = size
			elif tag == ElfUtil.DT_SCE_IDTABENTSZ: # ELF ID Table
				size = as_uint64(value)
				if size != ida_idaapi.BADADDR:
					self.id_table.entry_size = size
			elif tag == ElfUtil.DT_INIT:
				self.init_proc_ea = value
			elif tag == ElfUtil.DT_FINI:
				self.term_proc_ea = value
			elif tag == ElfUtil.DT_PREINIT_ARRAY:
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.preinit_array_ea = ea
			elif tag == ElfUtil.DT_PREINIT_ARRAYSZ:
				sz = as_uint64(value)
				if sz != ida_idaapi.BADADDR:
					self.preinit_array_sz = sz
			elif tag == ElfUtil.DT_INIT_ARRAY:
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.init_array_ea = ea
			elif tag == ElfUtil.DT_INIT_ARRAYSZ:
				sz = as_uint64(value)
				if sz != ida_idaapi.BADADDR:
					self.init_array_sz = sz
			elif tag == ElfUtil.DT_FINI_ARRAY:
				ea = as_uint64(value)
				if ea != 0 and ea != ida_idaapi.BADADDR:
					self.fini_array_ea = ea
			elif tag == ElfUtil.DT_FINI_ARRAYSZ:
				sz = as_uint64(value)
				if sz != ida_idaapi.BADADDR:
					self.fini_array_sz = sz
		if self.jmprel_reloc_table.entry_size == ida_idaapi.BADADDR:
			if self.relocation_type == ElfUtil.DT_REL:
				self.jmprel_reloc_table.entry_size = get_struct_size('Elf64_Rel')
			else:
				self.jmprel_reloc_table.entry_size = get_struct_size('Elf64_Rela')

		if self.rela_reloc_table.entry_size == ida_idaapi.BADADDR:
			self.rela_reloc_table.entry_size = get_struct_size(self.rela_reloc_table.struct_name())
		try:
			rela_total = self.rela_reloc_table.get_num_entries()
			# Keep canonical total entry count in the table object.
			self.rela_reloc_table.entry_count = rela_total
			if self.rela_relative_count != ida_idaapi.BADADDR and self.rela_relative_count < rela_total:
				print('Note: DT_RELACOUNT=%d, RELA total=%d (DT_RELACOUNT counts leading RELATIVE relocations).' % (
					self.rela_relative_count, rela_total
				))
		except Exception:
			pass

		if self.id_table.entry_size != ida_idaapi.BADADDR:
			expected_id_entsz = 0x8
			if self.id_table.entry_size != expected_id_entsz:
				ida_kernwin.warning(
					'Unsupported ID table entry size: 0x%x (expected: 0x%x), forcing expected size.' % (
						self.id_table.entry_size,
						expected_id_entsz
					)
				)
				self.id_table.entry_size = expected_id_entsz

		# Sanity checks driven by observed layout diffs (see ps5/elf_layout_compare.py).
		try:
			self._sanity_check_sysv_hash()
		except Exception:
			pass
		try:
			self._coerce_jmprel_layout()
		except Exception:
			pass

		return True

	def _sanity_check_sysv_hash(self):
		"""
		Sanity check the SysV .hash table.

		We compute the expected size from the header:
		nbucket (u32), nchain (u32), buckets[nbucket], chains[nchain]
		and compare it against DT_SCE_HASHSZ when present.
		"""
		if not self.hash_table or self.hash_table.ea in (0, ida_idaapi.BADADDR):
			return False
		if not ida_bytes.is_loaded(self.hash_table.ea):
			return False

		nbucket = ida_bytes.get_dword(self.hash_table.ea)
		nchain = ida_bytes.get_dword(self.hash_table.ea + 4)
		if nbucket in (ida_idaapi.BADADDR,) or nchain in (ida_idaapi.BADADDR,):
			return False
		if nbucket > 1_000_000 or nchain > 1_000_000:
			return False

		expect = (2 + nbucket + nchain) * 4
		if self.hash_table.size in (ida_idaapi.BADADDR, 0):
			self.hash_table.size = expect
			print('Note: inferred DT_SCE_HASHSZ from SysV .hash header: 0x%x' % expect)
			return True

		if self.hash_table.size != expect:
			print('Warning: SysV .hash size mismatch: DT_SCE_HASHSZ=0x%x expected=0x%x (nbucket=%u nchain=%u)' % (
				self.hash_table.size, expect, nbucket, nchain
			))
		return True

	def _coerce_jmprel_layout(self):
		"""
		Best-effort fix for JMPREL layout mismatches.

		Some images/reporting paths can provide inconsistent DT_PLTREL/entry-size info.
		We probe the first record as RELA vs REL and pick the layout that yields a
		plausible x86-64 relocation type (prefer JUMP_SLOT).
		"""
		t = self.jmprel_reloc_table
		if not t:
			return False
		if t.ea in (0, ida_idaapi.BADADDR) or t.size in (0, ida_idaapi.BADADDR):
			return False

		rela_sz = get_struct_size('Elf64_Rela')
		rel_sz = get_struct_size('Elf64_Rel')

		# Initial default from DT_PLTREL if possible.
		if t.entry_size == ida_idaapi.BADADDR:
			if self.relocation_type == ElfUtil.DT_REL:
				t.entry_size = rel_sz
			else:
				t.entry_size = rela_sz

		def probe_first_type(entry_size):
			if entry_size in (0, ida_idaapi.BADADDR):
				return None
			if t.size < entry_size:
				return None
			old = t.entry_size
			try:
				t.entry_size = entry_size
				e = t.get_entry(0)
				return JmpRelRelocTable.Record(e).get_type()
			except Exception:
				return None
			finally:
				t.entry_size = old

		cur_sz = t.entry_size
		alt_sz = rel_sz if cur_sz == rela_sz else rela_sz
		t_cur = probe_first_type(cur_sz)
		t_alt = probe_first_type(alt_sz)

		def plausible(rt):
			return rt is not None and rt != 0xFFFFFFFF and 0 <= rt <= 0x100

		# Prefer whichever yields JUMP_SLOT first; otherwise prefer any plausible type.
		use_alt = False
		if t_alt == JmpRelRelocTable.R_AMD64_JUMP_SLOT and t_cur != JmpRelRelocTable.R_AMD64_JUMP_SLOT:
			use_alt = True
		elif not plausible(t_cur) and plausible(t_alt):
			use_alt = True

		if use_alt:
			print('Note: corrected JMPREL entry layout: 0x%x -> 0x%x (first type 0x%x -> 0x%x).' % (
				cur_sz, alt_sz,
				0xFFFFFFFF if t_cur is None else t_cur,
				0xFFFFFFFF if t_alt is None else t_alt
			))
			t.entry_size = alt_sz
			return True

		# If current still looks broken, keep running but report once.
		if not plausible(t_cur):
			print('Warning: JMPREL first relocation type looks invalid: 0x%x (entry_size=0x%x).' % (
				0xFFFFFFFF if t_cur is None else t_cur, cur_sz
			))
		return False

	def _choose_jmprel_info_off(self):
		"""
		Choose where r_info is located inside a JMPREL entry.

		Normally (Elf64_Rela): r_info at +0x8, addend at +0x10.
		On some setups, parsed layouts appear swapped; detect by scoring candidates.
		"""
		if self._jmprel_info_off is not None:
			return self._jmprel_info_off

		t = self.jmprel_reloc_table
		if not t or not t.is_table_loaded():
			self._jmprel_info_off = 8
			return self._jmprel_info_off

		es = t.entry_size
		if es < 0x10:
			self._jmprel_info_off = 8
			return self._jmprel_info_off

		cands = [8]
		if es >= 0x18:
			cands.append(16)

		limit = min(t.get_num_entries(), 64)
		best_off = 8
		best_score = -1

		for off in cands:
			score = 0
			for i in range(limit):
				ea = t.ea + i * es
				raw = ida_bytes.get_bytes(ea + off, 8)
				if not raw or len(raw) != 8:
					continue
				info = struct.unpack('<Q', raw)[0]
				rt = as_uint32(info)
				sym = as_uint64(info) >> 32
				if rt == JmpRelRelocTable.R_AMD64_JUMP_SLOT:
					score += 10
				elif 0 <= rt <= 0x100 and rt != 0xFFFFFFFF:
					score += 1
				if self.symbols and sym < len(self.symbols):
					score += 1
			if score > best_score:
				best_score = score
				best_off = off

		if best_off != 8:
			print('Note: JMPREL info field appears at +0x%x (non-standard layout).' % best_off)
		self._jmprel_info_off = best_off
		return self._jmprel_info_off

	def _iter_jmprel_records(self, max_count=None):
		"""
		Yield raw JMPREL records as dictionaries:
		{index, r_offset, r_info, r_addend, sym, type}
		"""
		t = self.jmprel_reloc_table
		if not t or not t.is_table_loaded():
			return

		es = t.entry_size
		if es in (0, ida_idaapi.BADADDR):
			return

		total = t.get_num_entries()
		if max_count is not None:
			total = min(total, max_count)

		info_off = self._choose_jmprel_info_off()
		add_off = 16 if es >= 0x18 else None

		for i in range(total):
			ea = t.ea + i * es
			row = ida_bytes.get_bytes(ea, es)
			if not row or len(row) != es:
				break
			try:
				r_offset = struct.unpack('<Q', row[0:8])[0]
				r_info = struct.unpack('<Q', row[info_off:info_off + 8])[0]
				if add_off is not None and add_off + 8 <= es:
					r_addend = struct.unpack('<q', row[add_off:add_off + 8])[0]
				else:
					r_addend = 0
			except Exception:
				continue

			yield {
				'index': i,
				'r_offset': as_uint64(r_offset),
				'r_info': as_uint64(r_info),
				'r_addend': as_uint64(r_addend),
				'sym': as_uint64(r_info) >> 32,
				'type': as_uint32(r_info),
			}

	def _parse_comment_segment(self, data):
		print('Processing comment segment.')

		f = BytesIO(data)

		while True:
			key = f.read(struct.calcsize('4s'))
			if len(key) < struct.calcsize('4s'):
				# Reached end of file.
				break
			key = key.rstrip(b'\0').decode('ascii')

			data = f.read(struct.calcsize('2I'))
			if len(data) != struct.calcsize('2I'):
				ida_kernwin.warning('Truncated data at comment segment.')
				return False

			max_length, length = struct.unpack('<2I', data)
			value = f.read(length)

			if len(value) != length:
				ida_kernwin.warning('Truncated data at comment segment.')
				return False

			# Try to decode value as UTF-8 string.
			try:
				value = value.decode('utf-8').rstrip('\0')
			except:
				pass

			self.prodg_meta_data[key] = value

		params = {
			'PATH': 'Original path',
		}

		for key, desc in params.items():
			if key not in self.prodg_meta_data:
				continue
			print('%s: %s' % (desc, self.prodg_meta_data[key]))

		return True

	def _parse_version_segment(self, data):
		print('Processing version segment.')

		f = BytesIO(data)
		entries = []

		while True:
			data = f.read(struct.calcsize('2H'))
			if data == b'':
				# Reached end of file.
				break
			elif len(data) != struct.calcsize('2H'):
				ida_kernwin.warning('Truncated data at version segment.')
				return False

			reserved, length = struct.unpack('<2H', data)
			if reserved != 0:
				print('Warning! Non-zero reserved field in version segment header: 0x%x' % reserved)
			if length == 0:
				continue

			data = f.read(length)
			if len(data) != length:
				ida_kernwin.warning('Truncated data at version segment.')
				return False

			type_id, data = data[0], data[1:]
			if type_id == 0x8:
				try:
					name, version = data.split(b':', 1)
				except Exception:
					ida_kernwin.warning('Malformed library version record in version segment.')
					continue
				try:
					name = name.decode('ascii', errors='replace')
				except Exception:
					ida_kernwin.warning('Malformed library name in version segment.')
					continue
				version_hex = version.hex().upper()
				entries.append((name, version_hex))
			else:
				ida_kernwin.warning('Unknown type id 0x%x in version info.' % type_id)
				continue

		# Deduplicate noisy repeated entries while preserving appearance order.
		uniq = OrderedDict()  # key: (name, version_hex) -> count
		for name, version_hex in entries:
			key = (name, version_hex)
			if key not in uniq:
				uniq[key] = {'count': 0}
			uniq[key]['count'] += 1

			prev = self.lib_versions.get(name)
			if prev and prev != version_hex:
				print('Warning: library %s has multiple version blobs: %s -> %s' % (name, prev, version_hex))
			self.lib_versions[name] = version_hex

		for (name, version_hex), info in uniq.items():
			line = 'Library %s version: %s' % (name, version_hex)
			if info.get('count', 0) > 1:
				line += ' x%d' % info['count']
			print(line)

		return True

	def _parse_note_segment(self, data, base_ea=ida_idaapi.BADADDR):
		"""
		Parse PT_NOTE payload (Elf64_Nhdr stream).

		We mostly care about GNU build-id, but keep the parser generic.
		"""
		print('Processing note segment.')

		f = BytesIO(data)

		def align4(x):
			return (x + 3) & ~3

		any_note = False
		idx = 0
		while True:
			hdr_off = f.tell()
			hdr = f.read(struct.calcsize('3I'))
			if hdr == b'':
				break
			if len(hdr) != struct.calcsize('3I'):
				break

			namesz, descsz, n_type = struct.unpack('<3I', hdr)
			if namesz > 0x10000 or descsz > 0x100000:
				# Bogus sizes.
				break

			name_bytes = f.read(namesz)
			if len(name_bytes) != namesz:
				break
			f.seek(align4(namesz) - namesz, os.SEEK_CUR)

			desc_bytes = f.read(descsz)
			if len(desc_bytes) != descsz:
				break
			f.seek(align4(descsz) - descsz, os.SEEK_CUR)

			# Decode note name.
			try:
				name = name_bytes.rstrip(b'\0').decode('ascii', errors='replace')
			except Exception:
				name = repr(name_bytes)

			print('  Note #%d: name=%r type=0x%x descsz=0x%x' % (idx, name, n_type, descsz))
			any_note = True

			# GNU build-id: name="GNU", type=NT_GNU_BUILD_ID(3), desc=bytes
			if name == 'GNU' and n_type == 3 and descsz:
				build_id = desc_bytes.hex()
				print('    GNU build-id: %s' % build_id)
				self.gnu_build_id = build_id

				# Annotate the descriptor in the database when mapped.
				if base_ea not in (0, ida_idaapi.BADADDR):
					try:
						# desc starts after nhdr + padded name
						desc_off = hdr_off + struct.calcsize('3I') + align4(namesz)
						desc_ea = base_ea + desc_off
						if ida_bytes.is_loaded(desc_ea):
							set_name_unique(desc_ea, '__gnu_build_id', ida_name.SN_NOCHECK)
					except Exception:
						pass

			idx += 1

		return any_note

	def _fixup_padding_segment(self):
		seg = ida_segment.get_segm_by_name('.sce_padding')
		if not seg:
			image_base = ida_nalt.get_imagebase()

			has_padding = ida_bytes.get_bytes(image_base, ElfUtil.SCE_PADDING_SIZE) == ElfUtil.SCE_PADDING
			if not has_padding:
				return False

			text_seg = ida_segment.get_segm_by_name('.text')
			if not text_seg:
				ida_kernwin.warning('Unable to find .text segment, cannot fixup .sce_padding segment.')
				return False

			if text_seg.start_ea == image_base:
				print('Moving start of .text segment from 0x%x to 0x%x.' % (text_seg.start_ea, text_seg.start_ea + ElfUtil.SCE_PADDING_SIZE))
				ida_segment.set_segm_start(text_seg.start_ea, text_seg.start_ea + ElfUtil.SCE_PADDING_SIZE, ida_segment.SEGMOD_KILL | ida_segment.SEGMOD_SILENT)

			print('Creating .sce_padding segment.')
			seg = ida_segment.segment_t()
			seg.start_ea = image_base
			seg.end_ea = image_base + ElfUtil.SCE_PADDING_SIZE
			seg.bitness = text_seg.bitness
			seg.type = ida_segment.SEG_UNDF
			seg.perm = 0
			ida_segment.add_segm_ex(seg, '.sce_padding', None, ida_segment.ADDSEG_NOAA)

		seg = ida_segment.get_segm_by_name('.sce_padding')
		if not seg:
			return False

		ida_auto.auto_mark_range(seg.start_ea, seg.end_ea, ida_auto.AU_UNK)
		ida_bytes.del_items(seg.start_ea, ida_bytes.DELIT_SIMPLE, ElfUtil.SCE_PADDING_SIZE)

		print('Found .sce_padding segment.')

		return True

	def _link_segments_with_phdrs(self):
		num_segments = ida_segment.get_segm_qty()
		print('Number of segments: %d' % num_segments)

		for i in range(num_segments):
			seg = ida_segment.getnseg(i)
			if not seg:
				continue
			name = ida_segment.get_segm_name(seg)

			phdr = self.elf.find_phdr_by_seg(seg)
			if not phdr:
				continue

			# Ensure segments match PF_* flags. This is important for cases where IDA's ELF loader
			# mis-classifies an executable PT_LOAD as data: later analysis may skip it.
			flags = phdr.get('p_flags', 0)
			want_perm = 0
			if (flags & ElfUtil.PF_READ) != 0:
				want_perm |= ida_segment.SEGPERM_READ
			if (flags & ElfUtil.PF_WRITE) != 0:
				want_perm |= ida_segment.SEGPERM_WRITE
			if (flags & ElfUtil.PF_EXEC) != 0:
				want_perm |= ida_segment.SEGPERM_EXEC

				# If the loader created it as non-code, try to reclassify.
				try:
					if ida_segment.segtype(seg.start_ea) != ida_segment.SEG_CODE and hasattr(ida_segment, 'set_segm_attr') and hasattr(ida_segment, 'SEGATTR_TYPE'):
						if ida_segment.set_segm_attr(seg.start_ea, ida_segment.SEGATTR_TYPE, ida_segment.SEG_CODE):
							print('Reclassified segment %s at 0x%x as code due to PF_X.' % (name, seg.start_ea))
							ida_auto.auto_mark_range(seg.start_ea, seg.end_ea, ida_auto.AU_CODE)
				except Exception as e:
					print('Warning! Unable to reclassify segment %s at 0x%x: %s' % (name, seg.start_ea, e))

			old_perm = seg.perm
			seg.perm |= want_perm
			if seg.perm != old_perm:
				print('Updating %s segment permissions from PHDR flags (0x%x -> 0x%x).' % (name, old_perm, seg.perm))
				ida_segment.update_segm(seg)

	def _fixup_segment_perms(self):
		print('Fixing up segments permissions.')

		seg = ida_segment.get_first_seg()
		while seg:
			name = ida_segment.get_segm_name(seg)
			type_id = ida_segment.segtype(seg.start_ea)

			is_code = (
				type_id == ida_segment.SEG_CODE or
				name in ['.text', '.init', '.fini', '.plt'] or
				name.startswith('.text.')
			)

			old_perm = seg.perm
			if is_code:
				# Preserve existing R/W bits; only ensure EXEC is set.
				seg.perm |= ida_segment.SEGPERM_EXEC

			if seg.perm != old_perm:
				print('Updating %s segment permissions (0x%x -> 0x%x).' % (name, old_perm, seg.perm))
				ida_segment.update_segm(seg)

			seg = ida_segment.get_next_seg(seg.start_ea)

		return True

	def _fixup_init_fini_segments(self):
		print('Fixing up .init and .fini segments.')

		info = { '.init_proc': '.init', '.term_proc': '.fini' }
		segments = {}

		for func_name, segment_name in info.items():
			seg = ida_segment.get_segm_by_name(segment_name)
			if seg:
				continue

			ea = ida_name.get_name_ea(ida_idaapi.BADADDR, func_name)
			if ea == ida_idaapi.BADADDR:
				# Fallback to dynamic tags parsed earlier.
				if func_name == '.init_proc':
					ea = self.init_proc_ea
				elif func_name == '.term_proc':
					ea = self.term_proc_ea
				if ea not in (0, ida_idaapi.BADADDR):
					try:
						set_name_unique(ea, func_name, ida_name.SN_NOCHECK)
					except Exception:
						pass
			if ea == ida_idaapi.BADADDR:
				ida_kernwin.warning('Unable to find %s function address, cannot fixup %s segment.' % (func_name, segment_name))
				continue

			func = ida_funcs.get_func(ea)
			if not func:
				# Ensure a function item exists (post-analysis fallback).
				try:
					ida_ua.create_insn(ea)
				except Exception:
					pass
				try:
					ida_funcs.add_func(ea, ida_idaapi.BADADDR)
				except Exception:
					pass
				func = ida_funcs.get_func(ea)
				if not func:
					ida_kernwin.warning('Unable to find %s function, cannot fixup %s segment.' % (func_name, segment_name))
					continue
			start_ea, end_ea = func.start_ea, func.end_ea

			# Prefer the canonical epilogue marker produced by SDK crtendS.o:
			#   pop rbp; ret  (5D C3)
			# This avoids picking up early returns or tail-jumps inside init_proc.
			if segment_name == '.init':
				try:
					buf = ida_bytes.get_bytes(start_ea, 0x200) or b''
					p = buf.find(b'\x5d\xc3', 0x40 if len(buf) > 0x40 else 0)
					if p >= 0:
						end_ea = start_ea + p + 2  # include the RET byte
				except Exception:
					pass

			text_seg = ida_segment.get_segm_by_name('.text')
			if not text_seg:
				ida_kernwin.warning('Unable to find .text segment, cannot fixup %s segment.' % segment_name)
				continue

			if segment_name == '.init':
				end_ea = align_up(end_ea, 0x10)
				print('Moving start of .text segment from 0x%x to 0x%x.' % (text_seg.start_ea, end_ea))
				ida_segment.set_segm_start(text_seg.start_ea, end_ea, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
			elif segment_name == '.fini':
				start_ea = align_up(start_ea, 0x10)
				print('Moving end of .text segment from 0x%x to 0x%x.' % (text_seg.end_ea, start_ea))
				ida_segment.set_segm_end(text_seg.start_ea, start_ea, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)

			seg = ida_segment.segment_t()
			seg.start_ea = start_ea
			seg.end_ea = end_ea
			seg.bitness = text_seg.bitness
			seg.type = text_seg.type
			seg.perm = text_seg.perm
			segments[segment_name] = seg

		text_seg = ida_segment.get_segm_by_name('.text')
		if not text_seg:
			ida_kernwin.warning('Unable to find .text segment, cannot fixup .init and .proc segments.')
			return False

		for segment_name, seg in segments.items():
			print('Creating %s segment.' % segment_name)
			ida_segment.add_segm_ex(seg, segment_name, ida_segment.get_segm_class(text_seg), ida_segment.ADDSEG_NOSREG)

		return True

	def _fixup_eh_segments(self):
		assert self.elf.is_inited()

		print('Fixing up .eh_frame and .eh_frame_hdr segments.')

		# 1) Ensure .eh_frame_hdr exists (it is described by PT_GNU_EH_FRAME).
		hdr_seg = ida_segment.get_segm_by_name('.eh_frame_hdr')
		if not hdr_seg:
			templ_seg = ida_segment.get_segm_by_name('.rodata')
			if not templ_seg:
				ida_kernwin.warning('Unable to find .rodata segment, cannot fixup .eh_frame_hdr segment.')
				return False

			phdr = self.elf.find_phdr_by_type(ElfUtil.PT_GNU_EH_FRAME)
			if phdr is None:
				ida_kernwin.warning('Unable to find program header for segment .eh_frame_hdr, cannot fixup it.')
				return False

			new_seg = ida_segment.segment_t()
			new_seg.start_ea = phdr['p_vaddr']
			new_seg.end_ea = phdr['p_vaddr'] + phdr['p_memsz']
			new_seg.bitness = templ_seg.bitness
			new_seg.type = templ_seg.type
			new_seg.perm = templ_seg.perm

			print('Creating .eh_frame_hdr segment.')
			if not ida_segment.add_segm_ex(new_seg, '.eh_frame_hdr', ida_segment.get_segm_class(templ_seg), ida_segment.ADDSEG_NOSREG):
				ida_kernwin.warning('Unable to create .eh_frame_hdr segment (add_segm_ex failed).')

			hdr_seg = ida_segment.get_segm_by_name('.eh_frame_hdr')

		if not hdr_seg:
			ida_kernwin.warning('Unable to find .eh_frame_hdr segment, cannot fixup .eh_frame segment.')
			return False

		# 2) Parse .eh_frame_hdr to locate .eh_frame.
		try:
			hdr_info = gcc_extab.decode_eh_frame_hdr(hdr_seg, verbose=False)
			exc_eh_frame_ptr = hdr_info.get('eh_frame_ptr', ida_idaapi.BADADDR) if isinstance(hdr_info, dict) else ida_idaapi.BADADDR
		except Exception as e:
			print('Error parsing .eh_frame_hdr: %s' % e)
			return True

		if exc_eh_frame_ptr == ida_idaapi.BADADDR:
			ida_kernwin.warning('Unable to resolve .eh_frame pointer from .eh_frame_hdr.')
			return True

		# 3) Ensure .eh_frame segment exists. It can be located before or after .eh_frame_hdr.
		eh_seg = ida_segment.get_segm_by_name('.eh_frame')
		if eh_seg:
			return True

		print('Found .eh_frame start at 0x%x.' % exc_eh_frame_ptr)

		# Determine end by scanning CIE/FDE records.
		eh_end_ea = gcc_extab.find_eh_frame_end(exc_eh_frame_ptr)
		if eh_end_ea <= exc_eh_frame_ptr:
			ida_kernwin.warning('Unable to determine .eh_frame size, skipping segment creation.')
			return True

		print('Calculated .eh_frame end at 0x%x (size: 0x%x).' % (eh_end_ea, eh_end_ea - exc_eh_frame_ptr))

		new_seg = ida_segment.segment_t()
		new_seg.start_ea = exc_eh_frame_ptr
		new_seg.end_ea = eh_end_ea
		new_seg.bitness = hdr_seg.bitness
		new_seg.type = hdr_seg.type
		new_seg.perm = hdr_seg.perm

		print('Creating .eh_frame segment.')
		if not ida_segment.add_segm_ex(new_seg, '.eh_frame', ida_segment.get_segm_class(hdr_seg), ida_segment.ADDSEG_NOSREG):
			ida_kernwin.warning('Unable to create .eh_frame segment (add_segm_ex failed).')

		return True

	def _collect_eh_fde_info_with_gcc_extab(self, eh_seg, hdr_seg=None, comments_enabled=True, verbose=False):
		"""
		Parse all CIE/FDE entries in .eh_frame via gcc_extab formatter.
		Primary source is .eh_frame_hdr table (if available), with fallback to linear .eh_frame walk.
		Returns list of dicts:
		{start, end, lsda_ptr, lsda_end, lsda_entries, lsda_callsites, fde_ea, hdr_start}.
		"""
		if not eh_seg:
			return []

		results = []
		old_comments = None
		seen_skip_diags = set()

		try:
			if hasattr(gcc_extab, 'get_comments_enabled'):
				old_comments = bool(gcc_extab.get_comments_enabled())
		except Exception:
			old_comments = None

		try:
			try:
				if hasattr(gcc_extab, 'set_comments_enabled'):
					gcc_extab.set_comments_enabled(bool(comments_enabled))
			except Exception:
				pass

			try:
				if hasattr(gcc_extab, 'reset_parse_state'):
					gcc_extab.reset_parse_state()
			except Exception:
				pass

			def parse_one_fde(curr, hdr_start=ida_idaapi.BADADDR, source='eh_frame'):
				loc_start = ida_idaapi.BADADDR
				loc_end = ida_idaapi.BADADDR
				skip_diag = None
				try:
					loc_start, loc_end, _ = gcc_extab.format_cie_fde(curr)
				except Exception as e:
					print('Warning: gcc_extab.format_cie_fde failed at 0x%x: %s' % (curr, e))
					if verbose:
						print(traceback.format_exc())
				try:
					if hasattr(gcc_extab, 'get_last_skip_diag'):
						skip_diag = gcc_extab.get_last_skip_diag()
				except Exception:
					skip_diag = None

				fde_info = None
				try:
					if hasattr(gcc_extab, 'get_last_fde_info'):
						fde_info = gcc_extab.get_last_fde_info()
				except Exception:
					fde_info = None

				if isinstance(fde_info, dict) and fde_info.get('kind') == 'fde':
					start = fde_info.get('loc_start', loc_start)
					end = fde_info.get('loc_end', loc_end)
					lsda_ptr = fde_info.get('lsda_ptr', ida_idaapi.BADADDR)
					lsda_end = fde_info.get('lsda_end', ida_idaapi.BADADDR)
					lsda_entries = int(fde_info.get('lsda_entries', 0) or 0)
					lsda_callsites = list(fde_info.get('lsda_callsites', []) or [])
				else:
					start = loc_start
					end = loc_end
					lsda_ptr = ida_idaapi.BADADDR
					lsda_end = ida_idaapi.BADADDR
					lsda_entries = 0
					lsda_callsites = []

				if start not in (None, 0, ida_idaapi.BADADDR) and end not in (None, 0, ida_idaapi.BADADDR) and end > start:
					results.append({
						'start': as_uint64(start),
						'end': as_uint64(end),
						'lsda_ptr': as_uint64(lsda_ptr) if lsda_ptr not in (None, 0, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
						'lsda_end': as_uint64(lsda_end) if lsda_end not in (None, 0, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
						'lsda_entries': lsda_entries,
						'lsda_callsites': lsda_callsites,
						'fde_ea': curr,
						'hdr_start': hdr_start if hdr_start not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
						'source': source,
					})
				elif isinstance(skip_diag, dict):
					reason = str(skip_diag.get('reason', 'unknown'))
					entry_ea = skip_diag.get('entry_ea', curr)
					detail = str(skip_diag.get('detail', '') or '')
					key = (
						as_uint64(entry_ea) if entry_ea not in (None, ida_idaapi.BADADDR) else curr,
						reason,
						as_uint64(skip_diag.get('cie_ea', ida_idaapi.BADADDR)) if skip_diag.get('cie_ea', ida_idaapi.BADADDR) not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
						as_uint64(skip_diag.get('cie_field_ea', ida_idaapi.BADADDR)) if skip_diag.get('cie_field_ea', ida_idaapi.BADADDR) not in (None, ida_idaapi.BADADDR) else ida_idaapi.BADADDR,
					)
					if key not in seen_skip_diags:
						seen_skip_diags.add(key)
						extra = []
						for k in ('cie_ea', 'cie_field_ea', 'field_ea', 'fde_encoding'):
							v = skip_diag.get(k, ida_idaapi.BADADDR)
							if v not in (None, ida_idaapi.BADADDR):
								try:
									extra.append('%s=0x%x' % (k, as_uint64(v)))
								except Exception:
									extra.append('%s=%r' % (k, v))
						msg = '[ps5_elf] Skipping .eh_frame entry @0x%x: reason=%s' % (curr, reason)
						if detail:
							msg += ' (%s)' % detail
						if extra:
							msg += ' [' + ', '.join(extra) + ']'
						print(msg)
				elif verbose:
					print('[ps5_elf] Skipping .eh_frame entry @0x%x: no valid FDE range produced.' % curr)

			# 1) Primary pass: use .eh_frame_hdr table if available.
			hdr_entries = []
			try:
				if hdr_seg and hasattr(gcc_extab, 'collect_fde_ptrs_from_eh_frame_hdr'):
					hdr_entries = gcc_extab.collect_fde_ptrs_from_eh_frame_hdr(hdr_seg, eh_seg=eh_seg, verbose=verbose)
			except Exception as e:
				if verbose:
					print('[ps5_elf] .eh_frame_hdr table collection failed: %s' % e)
			if hdr_entries and verbose:
				print('[ps5_elf] Using .eh_frame_hdr table entries: %d' % len(hdr_entries))

			for idx, rec in enumerate(hdr_entries):
				if (idx & 0x3FF) == 0:
					try:
						if ida_kernwin.user_cancelled():
							break
					except Exception:
						pass
				parse_one_fde(as_uint64(rec.get('fde_ea', ida_idaapi.BADADDR)), rec.get('hdr_start', ida_idaapi.BADADDR), source='eh_frame_hdr')

			# 2) Fallback pass: linear walk .eh_frame only if hdr table is absent/empty or yielded no FDEs.
			if not hdr_entries or not results:
				if verbose:
					print('[ps5_elf] Falling back to linear .eh_frame walk.')
				curr = eh_seg.start_ea
				end_ea = eh_seg.end_ea
				idx = 0
				while curr + 4 <= end_ea and ida_bytes.is_loaded(curr):
					if (idx & 0x3FF) == 0:
						try:
							if ida_kernwin.user_cancelled():
								break
						except Exception:
							pass

					length = ida_bytes.get_dword(curr)
					if length in (None, ida_idaapi.BADADDR):
						break
					if length == 0:
						# Standard CFI terminator.
						break

					if length == 0xFFFFFFFF:
						if curr + 12 > end_ea:
							break
						real_len = ida_bytes.get_qword(curr + 4)
						next_ea = curr + 12 + real_len
					else:
						next_ea = curr + 4 + length

					if next_ea <= curr:
						break
					if next_ea > end_ea:
						next_ea = end_ea

					parse_one_fde(curr, source='eh_frame')
					curr = next_ea
					idx += 1
		finally:
			try:
				if old_comments is not None and hasattr(gcc_extab, 'set_comments_enabled'):
					gcc_extab.set_comments_enabled(old_comments)
			except Exception:
				pass

		return results

	def _fixup_funcs_from_eh_frame(self):
		"""
		Function recovery/bounds correction using full gcc_extab CIE/FDE parsing.
		"""
		if self.settings is None:
			self.settings = self._settings_load()
		s = self.settings or {}
		if not bool(s.get('eh_funcs_enable', True)):
			return False

		eh_seg = ida_segment.get_segm_by_name('.eh_frame')
		hdr_seg = ida_segment.get_segm_by_name('.eh_frame_hdr')
		if not eh_seg:
			return False

		max_range = int(s.get('eh_funcs_maxrange', 0x100000))
		max_range = max(0x100, min(max_range, 0x10000000))
		create_missing = bool(s.get('eh_funcs_create_missing', True))
		adjust_bounds = bool(s.get('eh_funcs_adjust_bounds', True))
		clamp_to_next = bool(s.get('eh_funcs_clamp_to_next', True))
		skip_plt = bool(s.get('eh_funcs_skip_plt', True))
		allow_shrink = bool(s.get('eh_funcs_shrink', False))
		verbose = bool(s.get('eh_funcs_verbose', False))
		comments_enabled = bool(s.get('gcc_extab_comments', True))

		def in_exec_segment(ea):
			seg = ida_segment.getseg(ea)
			return bool(seg and (seg.perm & ida_segment.SEGPERM_EXEC) != 0)

		def is_plt_seg_at(ea):
			if not skip_plt:
				return False
			seg = ida_segment.getseg(ea)
			if not seg:
				return False
			try:
				n = ida_segment.get_segm_name(seg) or ''
			except Exception:
				n = ''
			return n.startswith('.plt')

		fde_info = self._collect_eh_fde_info_with_gcc_extab(eh_seg, hdr_seg=hdr_seg, comments_enabled=comments_enabled, verbose=verbose)
		if not fde_info:
			return False

		created = 0
		changed = 0
		skipped = 0
		ranges = []

		for rec in fde_info:
			start = rec.get('start', ida_idaapi.BADADDR)
			end = rec.get('end', ida_idaapi.BADADDR)

			if start in (0, ida_idaapi.BADADDR) or end in (0, ida_idaapi.BADADDR) or end <= start:
				skipped += 1
				continue
			if (end - start) > max_range:
				skipped += 1
				continue
			if not in_exec_segment(start) or not in_exec_segment(end - 1):
				skipped += 1
				continue
			if is_plt_seg_at(start):
				skipped += 1
				continue

			ranges.append((as_uint64(start), as_uint64(end)))

		if not ranges:
			return False

		ranges.sort(key=lambda x: x[0])
		dedup = []
		for start, end in ranges:
			if dedup and dedup[-1][0] == start:
				if end > dedup[-1][1]:
					dedup[-1] = (start, end)
			else:
				dedup.append((start, end))
		ranges = dedup

		if clamp_to_next and len(ranges) > 1:
			tmp = []
			for idx, (start, end) in enumerate(ranges):
				if idx + 1 < len(ranges):
					nxt = ranges[idx + 1][0]
					if nxt > start and end > nxt:
						end = nxt
				tmp.append((start, end))
			ranges = tmp

		for idx, (start, end) in enumerate(ranges):
			if (idx & 0x1FF) == 0:
				try:
					ida_kernwin.replace_wait_box('PS5 ELF post-analysis\nAdjust functions from .eh_frame\nApplying ranges: %d/%d' % (idx, len(ranges)))
				except Exception:
					pass
				try:
					if ida_kernwin.user_cancelled():
						print('Fixing up functions from .eh_frame canceled by user.')
						break
				except Exception:
					pass

			if end <= start:
				continue

			try:
				nf = ida_funcs.get_next_func(start)
			except Exception:
				nf = None
			if nf and nf.start_ea > start and end > nf.start_ea:
				end = nf.start_ea

			seg = ida_segment.getseg(start)
			if seg and end > seg.end_ea:
				end = seg.end_ea
			if end <= start:
				continue

			func = ida_funcs.get_func(start)
			if func and func.start_ea != start:
				continue

			if not func:
				if not create_missing:
					continue
				try:
					ida_ua.create_insn(start)
				except Exception:
					pass
				try:
					ok = ida_funcs.add_func(start, end)
				except Exception:
					ok = False
				if not ok:
					try:
						ok = ida_funcs.add_func(start, ida_idaapi.BADADDR)
					except Exception:
						ok = False
				if ok:
					created += 1
					if verbose:
						print('Created function from .eh_frame: 0x%x..0x%x' % (start, end))
				continue

			if not adjust_bounds:
				continue

			want_end = end
			if want_end == func.end_ea:
				continue
			if want_end < func.end_ea and not allow_shrink:
				continue
			if (want_end - func.start_ea) > max_range:
				continue

			if verbose:
				print('Setting function 0x%x end to 0x%x from .eh_frame (old: 0x%x).' % (func.start_ea, want_end, func.end_ea))

			try:
				if ida_funcs.set_func_end(func.start_ea, want_end):
					nf = ida_funcs.get_func(func.start_ea) or func
					ida_funcs.reanalyze_function(nf, nf.start_ea, want_end, False)
					changed += 1
			except Exception:
				pass

		if created or changed:
			print('Fixing up functions from .eh_frame: created=%d changed=%d skipped=%d (FDEs=%d).' % (created, changed, skipped, len(fde_info)))
		return bool(created or changed)

	def _fixup_lsda_from_eh_frame(self):
		"""
		LSDA recovery using gcc_extab full FDE/LSDA formatting pass.
		"""
		if self.settings is None:
			self.settings = self._settings_load()
		s = self.settings or {}
		if not bool(s.get('lsda_enable', True)):
			return False

		eh_seg = ida_segment.get_segm_by_name('.eh_frame')
		hdr_seg = ida_segment.get_segm_by_name('.eh_frame_hdr')
		if not eh_seg:
			return False

		verbose = bool(s.get('lsda_verbose', False))
		comments_enabled = bool(s.get('gcc_extab_comments', True))
		fde_info = self._collect_eh_fde_info_with_gcc_extab(eh_seg, hdr_seg=hdr_seg, comments_enabled=comments_enabled, verbose=verbose)
		if not fde_info:
			return False

		lsda_seen = {}
		lsda_tables = 0
		lsda_callsites = 0
		changed = False
		lsda_min = ida_idaapi.BADADDR
		lsda_max = ida_idaapi.BADADDR

		for rec in fde_info:
			fstart = rec.get('start', ida_idaapi.BADADDR)
			fend = rec.get('end', ida_idaapi.BADADDR)
			lsda_ea = rec.get('lsda_ptr', ida_idaapi.BADADDR)
			lsda_end = rec.get('lsda_end', ida_idaapi.BADADDR)
			lsda_entries = int(rec.get('lsda_entries', 0) or 0)
			lsda_callsite_recs = list(rec.get('lsda_callsites', []) or [])

			if fstart in (0, ida_idaapi.BADADDR) or fend in (0, ida_idaapi.BADADDR):
				continue
			if lsda_ea in (0, ida_idaapi.BADADDR) or not ida_bytes.is_loaded(lsda_ea):
				continue
			if lsda_ea in lsda_seen:
				continue
			lsda_seen[lsda_ea] = True

			lsda_tables += 1
			lsda_callsites += max(max(0, lsda_entries), len(lsda_callsite_recs))

			end_ea = as_uint64(lsda_end if lsda_end not in (None, 0, ida_idaapi.BADADDR) else (lsda_ea + 1))
			if end_ea <= lsda_ea:
				end_ea = lsda_ea + 1
			# Keep each LSDA table within the segment that contains its start.
			# This avoids runaway ranges on malformed metadata, without tying everything to lsda_min.
			try:
				lsda_seg = ida_segment.getseg(lsda_ea)
				if lsda_seg and end_ea > lsda_seg.end_ea:
					end_ea = lsda_seg.end_ea
			except Exception:
				pass
			if end_ea <= lsda_ea:
				continue

			if lsda_min == ida_idaapi.BADADDR or lsda_ea < lsda_min:
				lsda_min = lsda_ea
			if lsda_max == ida_idaapi.BADADDR or end_ea > lsda_max:
				lsda_max = end_ea

			used = set_name_unique(lsda_ea, '__lsda_%X' % fstart, ida_name.SN_NOCHECK)
			if used:
				changed = True
			if comments_enabled:
				ida_bytes.set_cmt(lsda_ea, 'LSDA for function 0x%x..0x%x' % (fstart, fend), False)

			if hasattr(gcc_extab, 'safe_add_dref'):
				gcc_extab.safe_add_dref(fstart, lsda_ea, create_from=False, create_to=False)
			else:
				try:
					ida_xref.add_dref(fstart, lsda_ea, ida_xref.dr_O | ida_xref.XREF_USER)
				except Exception:
					pass

			for idx, ent in enumerate(lsda_callsite_recs):
				try_start = ent.get('try_start', ida_idaapi.BADADDR)
				try_end = ent.get('try_end', ida_idaapi.BADADDR)
				landing = ent.get('landing', 0)
				action = ent.get('action', 0)
				try:
					idx_tag = int(ent.get('index', idx))
				except Exception:
					idx_tag = idx
				try:
					action = int(action)
				except Exception:
					action = 0

				if comments_enabled and try_start not in (None, 0, ida_idaapi.BADADDR) and try_end not in (None, 0, ida_idaapi.BADADDR):
					try_start = as_uint64(try_start)
					try_end = as_uint64(try_end)
					if try_end > try_start and ida_bytes.is_loaded(try_start):
						try:
							ida_bytes.set_cmt(try_start, 'LSDA try[%d]: [0x%x..0x%x) action=%d' % (idx_tag, try_start, try_end, action), False)
						except Exception:
							pass

				if landing not in (None, 0, ida_idaapi.BADADDR):
					landing = as_uint64(landing)
					if comments_enabled and ida_bytes.is_loaded(landing):
						try:
							ida_bytes.set_cmt(landing, 'LSDA landing pad for 0x%x (entry %d, action=%d)' % (fstart, idx_tag, action), False)
						except Exception:
							pass
					if hasattr(gcc_extab, 'safe_add_dref'):
						gcc_extab.safe_add_dref(lsda_ea, landing, create_from=True, create_to=False)
					else:
						try:
							ida_xref.add_dref(lsda_ea, landing, ida_xref.dr_O | ida_xref.XREF_USER)
						except Exception:
							pass

		if lsda_min != ida_idaapi.BADADDR and lsda_max != ida_idaapi.BADADDR and lsda_max > lsda_min:
			seg = ida_segment.get_segm_by_name('.gcc_except_table')
			if not seg:
				templ = ida_segment.getseg(lsda_min)
				if templ:
					new_seg = ida_segment.segment_t()
					new_seg.start_ea = lsda_min
					new_seg.end_ea = min(lsda_max, templ.end_ea)
					new_seg.bitness = templ.bitness
					new_seg.type = templ.type
					new_seg.perm = templ.perm
					if new_seg.end_ea > new_seg.start_ea:
						if ida_segment.add_segm_ex(new_seg, '.gcc_except_table', ida_segment.get_segm_class(templ), ida_segment.ADDSEG_NOSREG):
							changed = True
			else:
				try:
					extend_to = lsda_max
					# Do not overlap next segment.
					next_seg = ida_segment.get_next_seg(seg.start_ea)
					if next_seg and extend_to > next_seg.start_ea:
						extend_to = next_seg.start_ea
					if extend_to > seg.end_ea:
						ida_segment.set_segm_end(seg.start_ea, extend_to, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
						changed = True
				except Exception:
					pass

		if lsda_tables:
			print('LSDA recovery: tables=%d callsites=%d range=[0x%x..0x%x).' % (
				lsda_tables,
				lsda_callsites,
				lsda_min if lsda_min != ida_idaapi.BADADDR else 0,
				lsda_max if lsda_max != ida_idaapi.BADADDR else 0
			))
		return bool(changed or lsda_tables)

	def _fixup_param_segment(self):
		assert self.elf.is_inited()

		if self.file_type == ElfUtil.ET_SCE_EXEC_ASLR:
			phdr_type = ElfUtil.PT_SCE_PROCPARAM
			segment_name = '.sce_process_param'
			struct_name = 'sceProcessParam'
			expected_magic = ElfUtil.SCE_PROCESS_PARAM_MAGIC
			handler_cb = self._fixup_process_param_segment
		else:
			phdr_type = ElfUtil.PT_SCE_MODULE_PARAM
			segment_name = '.sce_module_param'
			struct_name = 'sceModuleParam'
			expected_magic = ElfUtil.SCE_MODULE_PARAM_MAGIC
			handler_cb = self._fixup_module_param_segment

		phdr = self.elf.find_phdr_by_type(phdr_type)
		if phdr is None:
			ida_kernwin.warning('Unable to find program header for segment %s, cannot fixup it.' % segment_name)
			return False

		seg = ida_segment.get_segm_by_name(segment_name)
		if not seg:
			seg = ida_segment.get_segm_by_name('.rodata')
			if not seg:
				ida_kernwin.warning('Unable to find .rodata segment, cannot fixup %s segment.' % segment_name)
				return False

			new_seg = ida_segment.segment_t()
			new_seg.start_ea = phdr['p_vaddr']
			# Prefer exact PHDR size. Some PS5 param segments end at non-0x10 boundaries (e.g. start+0x60 with start%0x10!=0).
			# If IDA rejects it for some reason, fall back to a conservative alignment.
			exact_end = phdr['p_vaddr'] + phdr['p_memsz']
			new_seg.end_ea = exact_end

			new_seg.bitness = seg.bitness
			new_seg.type = seg.type
			new_seg.perm = seg.perm

			print('Creating %s segment.' % segment_name)
			if not ida_segment.add_segm_ex(new_seg, segment_name, ida_segment.get_segm_class(seg), ida_segment.ADDSEG_NOSREG):
				new_seg.end_ea = align_up(exact_end, 0x10)
				ida_segment.add_segm_ex(new_seg, segment_name, ida_segment.get_segm_class(seg), ida_segment.ADDSEG_NOSREG)

			seg = ida_segment.get_segm_by_name(segment_name)

		if not seg:
			ida_kernwin.warning('Unable to find %s segment, cannot fixup it.' % segment_name)
			return False

		print('Processing %s segment.' % segment_name)

		# Most observed PS5 binaries store a size/end pointer prefix (QWORD) and the real struct begins at +8.
		# A few toolchains might omit the prefix; detect by magic.
		prefix_len = struct.calcsize('Q')
		try:
			m0 = ida_bytes.get_bytes(seg.start_ea, 4) or b''
			m8 = ida_bytes.get_bytes(seg.start_ea + prefix_len, 4) or b''
		except Exception:
			m0, m8 = b'', b''

		if m0 == expected_magic:
			prefix_len = 0
		elif m8 == expected_magic:
			prefix_len = struct.calcsize('Q')
		else:
			# Unknown layout; assume the common prefix layout but keep it best-effort.
			prefix_len = struct.calcsize('Q')

		# SCE module param layout is typically:
		#   uint64 size; uint32 magic; ...
		# so the "prefix" is part of the structure. Treat it as prefixless.
		if segment_name == '.sce_module_param':
			prefix_len = 0
		elif segment_name == '.sce_process_param':
			# SCE process param also starts with in-struct size at +0x00 and magic at +0x08.
			# Prefer prefixless parsing when this canonical layout is detected.
			try:
				sz0 = ida_bytes.get_qword(seg.start_ea)
				m8p = ida_bytes.get_bytes(seg.start_ea + struct.calcsize('Q'), 4) or b''
				if m8p == expected_magic and sz0 not in (0, ida_idaapi.BADADDR) and 0x20 <= sz0 <= phdr['p_memsz']:
					prefix_len = 0
			except Exception:
				pass

		size_or_end = ida_bytes.get_qword(seg.start_ea) if prefix_len else ida_idaapi.BADADDR
		phdr_end = phdr['p_vaddr'] + phdr['p_memsz']
		size = phdr['p_memsz']

		if prefix_len:
			if size_or_end == ida_idaapi.BADADDR or size_or_end < struct.calcsize('Q'):
				ida_kernwin.warning('Unexpected size of %s structure.' % struct_name)
				return False

			# Some binaries store an absolute end pointer instead of a size.
			size = size_or_end
			try:
				if size_or_end > seg.start_ea and size_or_end <= phdr_end:
					derived = size_or_end - seg.start_ea
					if derived >= struct.calcsize('Q') and derived <= phdr['p_memsz']:
						print('%s structure end pointer: 0x%x (derived size: 0x%x).' % (struct_name, size_or_end, derived))
						size = derived
			except Exception:
				pass
		else:
			# Prefixless layout: for module param, the first qword is usually the size.
			if segment_name == '.sce_module_param':
				try:
					sz0 = ida_bytes.get_qword(seg.start_ea)
					if sz0 not in (0, ida_idaapi.BADADDR) and sz0 <= phdr['p_memsz'] and sz0 >= 0x20:
						size = sz0
						print('Note: %s uses in-struct size field 0x%x.' % (struct_name, size))
					else:
						print('Note: %s appears prefixless; using PHDR size 0x%x.' % (struct_name, size))
				except Exception:
					print('Note: %s appears prefixless; using PHDR size 0x%x.' % (struct_name, size))
			else:
				# For other params, trust PHDR size and parse from the segment start.
				print('Note: %s appears prefixless; using PHDR size 0x%x.' % (struct_name, size))

		print('%s structure size: 0x%x' % (struct_name, size))

		# Prefer an exact end to avoid creating phantom bytes at the end of short param segments.
		end_ea = seg.start_ea + size
		if end_ea > phdr_end:
			# Don't let a bogus size grow past the PHDR range.
			end_ea = phdr_end
		if seg.end_ea != end_ea:
			print('Moving end of %s segment from 0x%x to 0x%x.' % (segment_name, seg.end_ea, end_ea))
			ok = ida_segment.set_segm_end(seg.start_ea, end_ea, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
			if not ok:
				# Some IDA versions might refuse odd ends; fall back to a conservative alignment.
				end_ea_al = align_up(end_ea, 0x10)
				if end_ea_al != end_ea:
					ida_segment.set_segm_end(seg.start_ea, end_ea_al, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)

		data = ida_bytes.get_bytes(seg.start_ea, size)
		if len(data) != size:
			raise RuntimeError('Insufficient data of %s structure: 0x%x (expected: 0x%x)' % (struct_name, len(data), size))

		return handler_cb(segment_name, struct_name, data[prefix_len:])

	def _fixup_size_prefixed_qword_table(self, base_ea, desc, max_sz=0x2000):
		"""
		Best-effort: interpret memory at base_ea as:
		+0x00 uint64 size
		+0x08 uint64 kind/version/count (unknown)
		+0x10 uint64[] payload
		"""
		if base_ea in [0, ida_idaapi.BADADDR] or not ida_bytes.is_loaded(base_ea):
			return False

		try:
			sz = ida_bytes.get_qword(base_ea)
			if sz in [0, ida_idaapi.BADADDR] or sz < 0x10 or sz > max_sz:
				return False

			seg = ida_segment.getseg(base_ea)
			if seg and base_ea + sz > seg.end_ea:
				# If claimed size goes past the segment, do not trust it.
				return False

			# Make the table readable in IDA: qwords across the whole blob (best effort).
			for ea in range(base_ea, base_ea + sz, 8):
				if not ida_bytes.is_loaded(ea):
					break
				ida_bytes.create_qword(ea, 8, True)

			kind = ida_bytes.get_qword(base_ea + 8)
			print('  %s @0x%x: size=0x%x kind=0x%x' % (desc, base_ea, sz, kind))

			# Summarize payload pointers (helpful for reverse engineering).
			n_total = max(0, (sz - 0x10) // 8)
			n_nonzero = 0
			for i in range(n_total):
				ptr = ida_bytes.get_qword(base_ea + 0x10 + i * 8)
				if ptr not in [0, ida_idaapi.BADADDR]:
					n_nonzero += 1
			if n_total:
				print('    payload qwords: %d (%d non-zero)' % (n_total, n_nonzero))
			return True
		except Exception:
			return False

	def _fixup_libc_param(self, libc_param_ea):
		if libc_param_ea in [0, ida_idaapi.BADADDR] or not ida_bytes.is_loaded(libc_param_ea):
			return False

		print('Processing libc param structure (best effort).')
		set_name_unique(libc_param_ea, 'sceLibcParam', ida_name.SN_NOCHECK)

		def resolve_ptr(val):
			# Some fields store offsets (e.g. 0xA8) relative to libc_param base.
			if val in [0, ida_idaapi.BADADDR]:
				return val
			try:
				if val < 0x100000:
					cand = libc_param_ea + val
					if ida_bytes.is_loaded(cand):
						return cand
			except Exception:
				pass
			return val

		def qptr(off, label):
			ea = libc_param_ea + off
			try:
				if ida_bytes.is_loaded(ea):
					ida_bytes.create_qword(ea, 8, True)
				raw = ida_bytes.get_qword(ea) if ida_bytes.is_loaded(ea) else ida_idaapi.BADADDR
				ptr = resolve_ptr(raw)
				if raw not in [0, ida_idaapi.BADADDR]:
					if ptr != raw:
						print('  %s: 0x%x (offset +0x%x -> 0x%x)' % (label, raw, raw, ptr))
					else:
						print('  %s: 0x%x' % (label, ptr))
				return ptr
			except Exception:
				return ida_idaapi.BADADDR

		mem_param_ptr = qptr(0x00, 'kernel_mem_param_ptr?')
		need = qptr(0x48, 'need_libc_str_ptr')

		if need not in [0, ida_idaapi.BADADDR] and ida_bytes.is_loaded(need):
			try:
				s = read_cstring_at(need, encoding='utf-8')
				if s:
					print('  need_libc_str: %s' % s)
			except Exception:
				pass

		# Common sub-structures.
		if mem_param_ptr not in [0, ida_idaapi.BADADDR]:
			set_name_unique(mem_param_ptr, 'sceKernelMemParam', ida_name.SN_NOCHECK)
			self._fixup_size_prefixed_qword_table(mem_param_ptr, 'kernel_mem_param', max_sz=0x800)

		return True

	def _fixup_process_param_segment(self, segment_name, struct_name, data):
		# Canonical PS5 layout (0x60):
		#   +0x00 uint64 size
		#   +0x08 uint32 magic ("ORBI")
		#   +0x0C uint32 entry_count
		#   +0x10 uint32 unknown
		#   +0x14 uint32 sdk_version
		#   +0x18..+0x50 8 x uint64 pointers
		#   +0x58 uint64 flags
		fmt_full = '<Q4I9Q'
		fmt_legacy = '<4s3I9Q'  # Fallback for older prefix-skipped callers.
		data_size = len(data)
		full_size = struct.calcsize(fmt_full)
		legacy_size = struct.calcsize(fmt_legacy)
		if data_size < min(full_size, legacy_size):
			raise RuntimeError('Unsupported size of %s structure: 0x%x (expected at least: 0x%x)' % (
				struct_name, data_size, min(full_size, legacy_size)
			))

		size = ida_idaapi.BADADDR
		entry_count = 0
		unknown = 0
		sdk_version = 0
		process_name_ea = ida_idaapi.BADADDR
		user_main_thread_name_ea = ida_idaapi.BADADDR
		user_main_thread_priority_ea = ida_idaapi.BADADDR
		user_main_thread_stack_size_ea = ida_idaapi.BADADDR
		libc_param_ea = ida_idaapi.BADADDR
		kernel_mem_param_ea = ida_idaapi.BADADDR
		kernel_fs_param_ea = ida_idaapi.BADADDR
		process_preload_enabled_ea = ida_idaapi.BADADDR
		flags = ida_idaapi.BADADDR
		offset = 0

		try:
			magic_at_8 = data[8:12]
		except Exception:
			magic_at_8 = b''

		if data_size >= full_size and magic_at_8 == ElfUtil.SCE_PROCESS_PARAM_MAGIC:
			(size, magic_u32, entry_count, unknown, sdk_version,
			 process_name_ea, user_main_thread_name_ea, user_main_thread_priority_ea,
			 user_main_thread_stack_size_ea, libc_param_ea, kernel_mem_param_ea,
			 kernel_fs_param_ea, process_preload_enabled_ea, flags) = struct.unpack(fmt_full, data[:full_size])
			if magic_u32 != int.from_bytes(ElfUtil.SCE_PROCESS_PARAM_MAGIC, 'little'):
				raise RuntimeError('Invalid magic in %s structure: 0x%08x' % (struct_name, magic_u32))
			offset = full_size
		else:
			# Legacy mode: data already starts at magic (size was consumed as prefix).
			(magic, entry_count, unknown, sdk_version,
			 process_name_ea, user_main_thread_name_ea, user_main_thread_priority_ea,
			 user_main_thread_stack_size_ea, libc_param_ea, kernel_mem_param_ea,
			 kernel_fs_param_ea, process_preload_enabled_ea, flags) = struct.unpack(fmt_legacy, data[:legacy_size])
			if magic != ElfUtil.SCE_PROCESS_PARAM_MAGIC:
				raise RuntimeError('Invalid magic in %s structure: 0x%08x' % (struct_name, int.from_bytes(magic, 'little')))
			offset = legacy_size

		remain = max(0, data_size - offset)
		# If newer SDK adds more fields, keep them visible for later reverse-engineering.
		if remain > 0:
			extra = data[offset:offset + min(remain, 0x80)]
			hex_preview = ' '.join('%02X' % b for b in extra)
			print('  Extra process param bytes: 0x%x (preview %d bytes): %s%s' % (
				remain, len(extra), hex_preview, ' ...' if remain > len(extra) else ''
			))

		print('Process info:')
		print('  Magic: 0x%s' % ElfUtil.SCE_PROCESS_PARAM_MAGIC.hex())
		if size not in (0, ida_idaapi.BADADDR):
			print('  Size: 0x%x' % size)
		print('  Entry count: %d' % entry_count)
		print('  SDK version: 0x%x' % sdk_version)
		print('  Unknown: 0x%x' % unknown)
		print('  Process name ea: 0x%x' % process_name_ea)
		print('  User main thread ea: 0x%x' % user_main_thread_name_ea)
		print('  User main thread priority ea: 0x%x' % user_main_thread_priority_ea)
		print('  User main thread stack size ea: 0x%x' % user_main_thread_stack_size_ea)
		print('  Libc param ea: 0x%x' % libc_param_ea)
		if kernel_mem_param_ea != ida_idaapi.BADADDR:
			print('  Kernel mem param ea: 0x%x' % kernel_mem_param_ea)
		if kernel_fs_param_ea != ida_idaapi.BADADDR:
			print('  Kernel fs param ea: 0x%x' % kernel_fs_param_ea)
		if process_preload_enabled_ea != ida_idaapi.BADADDR:
			print('  Process preload enabled ea: 0x%x' % process_preload_enabled_ea)
		if flags != ida_idaapi.BADADDR:
			print('  Flags: 0x%x' % flags)

		def try_print_cstring(desc, ea):
			if ea in [0, ida_idaapi.BADADDR]:
				return
			try:
				if not ida_bytes.is_loaded(ea):
					return
				s = read_cstring_at(ea, encoding='utf-8')
				if s:
					print('  %s: %s' % (desc, s))
			except Exception:
				pass

		def try_print_qword_value(desc, ea):
			if ea in [0, ida_idaapi.BADADDR]:
				return
			try:
				if not ida_bytes.is_loaded(ea):
					return
				v = ida_bytes.get_qword(ea)
				if v != ida_idaapi.BADADDR:
					print('  %s @0x%x: 0x%x' % (desc, ea, v))
			except Exception:
				pass

		def try_print_dword_or_qword_value(desc, ea):
			# PS5 process param often points to uint32 values stored inside .got, sometimes unaligned.
			if ea in [0, ida_idaapi.BADADDR]:
				return
			try:
				if not ida_bytes.is_loaded(ea):
					return
				if (ea & 7) != 0:
					v = ida_bytes.get_dword(ea)
					if v != ida_idaapi.BADADDR:
						print('  %s @0x%x (u32): 0x%x' % (desc, ea, v))
					return

				vq = ida_bytes.get_qword(ea)
				if vq == ida_idaapi.BADADDR:
					return
				lo = vq & 0xFFFFFFFF
				hi = (vq >> 32) & 0xFFFFFFFF
				# Prefer the low dword when the qword looks like a sign/zero-extended uint32.
				if hi in [0, 0xFFFFFFFF] and lo <= 0x10000000:
					print('  %s @0x%x (u32): 0x%x' % (desc, ea, lo))
				else:
					print('  %s @0x%x: 0x%x' % (desc, ea, vq))
			except Exception:
				pass

		try_print_cstring('Process name', process_name_ea)
		try_print_cstring('User main thread name', user_main_thread_name_ea)
		try_print_dword_or_qword_value('User main thread priority', user_main_thread_priority_ea)
		try_print_dword_or_qword_value('User main thread stack size', user_main_thread_stack_size_ea)

		# Add stable names for common process-param targets (helps later import/reloc analysis).
		try:
			if process_name_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(process_name_ea, 'sceProcessName', ida_name.SN_NOCHECK)
			if user_main_thread_name_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(user_main_thread_name_ea, 'sceUserMainThreadName', ida_name.SN_NOCHECK)
			if user_main_thread_priority_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(user_main_thread_priority_ea, 'sceUserMainThreadPriority', ida_name.SN_NOCHECK)
			if user_main_thread_stack_size_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(user_main_thread_stack_size_ea, 'sceUserMainThreadStackSize', ida_name.SN_NOCHECK)
			if libc_param_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(libc_param_ea, '_sceLibcParam', ida_name.SN_NOCHECK)
			if kernel_mem_param_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(kernel_mem_param_ea, '_sceKernelMemParam', ida_name.SN_NOCHECK)
			if kernel_fs_param_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(kernel_fs_param_ea, '_sceKernelFsParam', ida_name.SN_NOCHECK)
			if process_preload_enabled_ea not in (0, ida_idaapi.BADADDR):
				set_name_unique(process_preload_enabled_ea, 'sceProcessPreloadEnabled', ida_name.SN_NOCHECK)
		except Exception:
			pass

		# Best-effort: carve RELRO subranges for common process-param blocks in executables.
		# This helps IDA plugins/tools that rely on segment names (e.g. .data.rel.ro.*).
		try:
			self._carve_exec_param_relro_segments([
				(libc_param_ea, '.data.rel.ro._sceLibcParam'),
				(kernel_mem_param_ea, '.data.rel.ro._sceKernelMemParam'),
				(kernel_fs_param_ea, '.data.rel.ro._sceKernelFsParam'),
			])
		except Exception:
			pass

		# libc_param points to a rich structure with nested size-prefixed blobs/tables.
		if libc_param_ea not in [0, ida_idaapi.BADADDR]:
			try:
				self._fixup_libc_param(libc_param_ea)
			except Exception:
				pass

		return True

	def _get_gnu_relro_ranges(self):
		ranges = []
		try:
			for phdr in getattr(self.elf, 'phdrs', []) or []:
				if ElfUtil.phdr_type(phdr) != ElfUtil.PT_GNU_RELRO:
					continue
				start = as_uint64(phdr.get('p_vaddr', ida_idaapi.BADADDR))
				sz = as_uint64(phdr.get('p_memsz', 0))
				if start in (0, ida_idaapi.BADADDR) or sz in (0, ida_idaapi.BADADDR):
					continue
				end = start + sz
				if end > start:
					ranges.append((start, end))
		except Exception:
			return []
		return ranges

	def _carve_exec_param_relro_segments(self, blocks):
		"""
		Executables often place process-param helper blobs in PT_GNU_RELRO.

		When those blobs are tightly packed, splitting them into named segments makes:
		- import stubs easier to spot
		- third-party scripts/plugins happier (some expect .data.rel.ro.* names)

		This is intentionally conservative: if splitting fails or looks unsafe, we only add labels.
		"""
		if self.file_type != ElfUtil.ET_SCE_EXEC_ASLR:
			return False

		relro_ranges = self._get_gnu_relro_ranges()
		if not relro_ranges:
			return False

		def in_relro(ea):
			for s, e in relro_ranges:
				if s <= ea < e:
					return True
			return False

		# Filter/normalize block list.
		cands = []
		for ea, seg_name in blocks or []:
			if ea in (0, ida_idaapi.BADADDR) or not isinstance(seg_name, str) or not seg_name:
				continue
			if not ida_bytes.is_loaded(ea):
				continue
			if not in_relro(ea):
				continue
			seg = ida_segment.getseg(ea)
			if not seg:
				continue
			# Only carve inside non-executable writable ranges (typical RELRO).
			if (seg.perm & ida_segment.SEGPERM_EXEC) != 0:
				continue
			if (seg.perm & ida_segment.SEGPERM_WRITE) == 0:
				continue
			# Require qword alignment; most of these tables are pointer-heavy.
			if (ea & 7) != 0:
				continue
			cands.append((ea, seg_name))

		if len(cands) < 2:
			return False

		# Group by containing segment to avoid cross-segment splits.
		by_seg = {}
		for ea, seg_name in cands:
			seg = ida_segment.getseg(ea)
			if not seg:
				continue
			by_seg.setdefault(seg.start_ea, []).append((ea, seg_name))

		split_fn = getattr(ida_segment, 'split_segm', None)
		if not callable(split_fn):
			# Without split support we can't safely carve; labels were still applied earlier.
			return False

		changed = False
		for seg_start, items in by_seg.items():
			seg = ida_segment.getseg(seg_start)
			if not seg:
				continue

			items = sorted(set(items), key=lambda x: x[0])
			span = items[-1][0] - items[0][0]
			# Heuristic: only carve when the blocks are in a compact region.
			if span > 0x8000:
				continue

			# Split at each boundary (excluding segment start).
			for ea, _ in items:
				seg2 = ida_segment.getseg(ea)
				if not seg2 or seg2.start_ea == ea:
					continue
				try:
					tmp = '.split_%X' % ea
					split_fn(ea, tmp, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
				except Exception:
					continue

			# Rename newly created segments.
			for ea, desired in items:
				seg2 = ida_segment.getseg(ea)
				if not seg2 or seg2.start_ea != ea:
					continue
				try:
					final = desired
					if ida_segment.get_segm_by_name(final) is not None:
						final = '%s.%X' % (desired, ea)
					ida_segment.set_segm_name(seg2, final)
					changed = True
				except Exception:
					pass

		return changed

	def _fixup_module_param_segment(self, segment_name, struct_name, data):
		# Newer understanding (matches SDK expectations):
		# struct sce_module_param {
		#   uint64_t size;            // 0x00
		#   uint32_t magic;           // 0x08
		#   uint32_t version;         // 0x0C
		#   uint32_t module_flags;    // 0x10
		#   uint32_t sdk_version;     // 0x14
		#   uint64_t reserved;        // 0x18
		# };
		fmt = '<QIIIIQ'
		data_size = len(data)
		expected_size = struct.calcsize(fmt)
		if data_size < expected_size:
			raise RuntimeError('Unsupported size of %s structure: 0x%x (expected: 0x%x)' % (struct_name, data_size, expected_size))
		elif data_size > expected_size:
			print('Warning! Size of %s structure is larger than expected: 0x%x (expected: 0x%x)' % (struct_name, data_size, expected_size))

		size, magic_u32, version, module_flags, sdk_version, reserved = struct.unpack(fmt, data[:expected_size])

		magic_expected = int.from_bytes(ElfUtil.SCE_MODULE_PARAM_MAGIC, 'little')
		if magic_u32 != magic_expected:
			raise RuntimeError('Invalid magic in %s structure: 0x%08x' % (struct_name, magic_u32))

		print('Module info:')
		print('  Size: 0x%x' % size)
		print('  Magic: 0x%08x' % magic_u32)
		print('  Version: %u' % version)
		print('  Module flags: 0x%08x' % module_flags)
		print('  SDK version: 0x%08x' % sdk_version)
		print('  Reserved: 0x%016x' % reserved)

		return True

	def _fixup_data_segment(self):
		seg = ida_segment.get_segm_by_name('.data')
		if seg:
			# Segment already exists, skipping it.
			return False

		seg = self._find_last_rw_seg()
		if not seg:
			ida_kernwin.warning('Unable to find R/W segment, cannot fixup .data segment.')
			return False

		seg_name = ida_segment.get_segm_name(seg)
		if seg_name.startswith('.'):
			ida_kernwin.warning('R/W segment starts with dot already, cannot fixup .data segment.')
			return False

		ida_segment.set_segm_name(seg, '.data')

		return True

	def _fixup_extra_segments(self):
		print('Fixing up extra .data segments.')

		first_seg, last_seg = ida_segment.get_first_seg(), ida_segment.get_last_seg()

		seg = first_seg
		while seg:
			name = ida_segment.get_segm_name(seg)
			sclass = ida_segment.get_segm_class(seg)
			idx = ida_segment.get_segm_num(seg.start_ea)

			if name.lower() == 'load' and not name.startswith('.') and sclass == 'DATA':
				print('Renaming extra R/W %s segment #%03d to .data.' % (name, idx))
				ida_segment.set_segm_name(seg, '.data')

			seg = ida_segment.get_next_seg(seg.start_ea)
			if seg == last_seg:
				break

		print('Merging similar neighboring segments.')

		seg1 = first_seg
		while seg1:
			name1 = ida_segment.get_segm_name(seg1)
			sclass1 = ida_segment.get_segm_class(seg1)
			idx1 = ida_segment.get_segm_num(seg1.start_ea)

			#print('Processing segment #%03d: %s' % (idx1, name1))

			finished = False
			while not finished:
				seg2 = ida_segment.get_next_seg(seg1.start_ea)
				if not seg2:
					finished = True
					break
				is_last = seg2 == last_seg

				name2 = ida_segment.get_segm_name(seg2)
				sclass2 = ida_segment.get_segm_class(seg2)
				idx2 = ida_segment.get_segm_num(seg2.start_ea)

				#print('Comparing with segment #%03d: %s' % (idx2, name2))

				if name1 != name2 or seg1.perm != seg2.perm or seg1.end_ea != seg2.start_ea:
					#print('Merging done: params mismatch')
					finished = True
					break

				print('Merging segments #%03d(%s) and #%03d(%s): [0x%x;0x%x) / [0x%x;0x%x)' % (idx1, name1, idx2, name2, seg1.start_ea, seg1.end_ea, seg2.start_ea, seg2.end_ea))

				end_ea = seg2.end_ea
				assert end_ea >= seg1.end_ea

				ida_segment.del_segm(seg2.start_ea, ida_segment.SEGMOD_KEEP)
				ida_segment.set_segm_end(seg1.start_ea, end_ea, ida_segment.SEGMOD_KEEP)
				ida_segment.update_segm(seg1)

				if is_last:
					#print('Merging done: was last segment')
					break

			seg1 = ida_segment.get_next_seg(seg1.start_ea)
			if seg1 == last_seg:
				break

		return True

	def _fixup_got_segments(self):
		print('Fixing up .got and .got.plt segments.')

		result = False

		# DT_PLTGOT is not always the start of the .got.plt region on PS5 PRX.
		# Some linkers point DT_PLTGOT into the middle of GOTPLT (often at the first/third JUMP_SLOT),
		# which breaks .plt recovery and import decoding. Refine it using JUMP_SLOT relocations.
		try:
			self._refine_got_plt_start_from_jmprel()
		except Exception:
			pass

		def pick_bound_after(ea, candidates):
			best = ida_idaapi.BADADDR
			for c in candidates:
				if c in (0, ida_idaapi.BADADDR):
					continue
				if c > ea and (best == ida_idaapi.BADADDR or c < best):
					best = c
			return best

		ctors_seg = ida_segment.get_segm_by_name('.ctors')
		dtors_seg = ida_segment.get_segm_by_name('.dtors')
		mod_param_seg = ida_segment.get_segm_by_name('.sce_module_param')

		ctors_start = ctors_seg.start_ea if ctors_seg else ida_idaapi.BADADDR
		dtors_start = dtors_seg.start_ea if dtors_seg else ida_idaapi.BADADDR
		mod_param_start = mod_param_seg.start_ea if mod_param_seg else ida_idaapi.BADADDR

		if self.got_plt_start_ea != ida_idaapi.BADADDR:
			print('Address of .got.plt section: 0x%x' % self.got_plt_start_ea)
			got_plt_end = pick_bound_after(self.got_plt_start_ea, [ctors_start, dtors_start, mod_param_start])

			# IDA/Hex-Rays treats '.got.plt' as read-only based on the NAME, which causes
			# unwanted constant propagation. Prefer a neutral name, but accept existing ones.
			seg = ida_segment.get_segm_by_name('.gotplt') or ida_segment.get_segm_by_name('.got.plt')
			if not seg:
				seg = ida_segment.getseg(self.got_plt_start_ea)
				if not seg:
					ida_kernwin.warning('Unable to find segment which includes .got.plt, cannot fixup .got.plt segment.')
					return False

				if got_plt_end == ida_idaapi.BADADDR:
					got_plt_end = seg.end_ea
				# Sanity clamp to avoid overlaps when the input is odd/corrupt.
				if got_plt_end <= self.got_plt_start_ea:
					got_plt_end = seg.end_ea

				new_seg = ida_segment.segment_t()
				new_seg.start_ea = self.got_plt_start_ea
				new_seg.end_ea = got_plt_end
				new_seg.bitness = seg.bitness
				new_seg.type = seg.type
				new_seg.perm = seg.perm

				print('Creating .gotplt segment.')
				ida_segment.add_segm_ex(new_seg, '.gotplt', ida_segment.get_segm_class(seg), 0)
			else:
				# If user already has .got.plt, try to rename it (best effort).
				try:
					if ida_segment.get_segm_name(seg) == '.got.plt' and ida_segment.get_segm_by_name('.gotplt') is None:
						ida_segment.set_segm_name(seg, '.gotplt')
				except Exception:
					pass
				# If bounds are now better known (e.g. after .ctors/.dtors discovery), update existing segment.
				try:
					if got_plt_end == ida_idaapi.BADADDR:
						got_plt_end = seg.end_ea
					if got_plt_end > self.got_plt_start_ea and got_plt_end != seg.end_ea:
						ida_segment.set_segm_end(seg.start_ea, got_plt_end, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
				except Exception:
					pass

			result |= True

		if self.got_start_ea != ida_idaapi.BADADDR:
			print('Address of .got section: 0x%x' % self.got_start_ea)
			got_end = self.got_plt_start_ea if self.got_plt_start_ea != ida_idaapi.BADADDR else ida_idaapi.BADADDR

			# Hex-Rays also treats '.got' as read-only based on the NAME, so use a neutral
			# segment name to avoid constant propagation.
			seg = ida_segment.get_segm_by_name('.gotrw') or ida_segment.get_segm_by_name('.got')
			if not seg:
				seg = ida_segment.getseg(self.got_start_ea)
				if not seg:
					ida_kernwin.warning('Unable to find segment which includes .got, cannot fixup .got segment.')
					return False

				if got_end == ida_idaapi.BADADDR:
					got_end = seg.end_ea
				if got_end <= self.got_start_ea:
					got_end = seg.end_ea

				new_seg = ida_segment.segment_t()
				new_seg.start_ea = self.got_start_ea
				new_seg.end_ea = got_end
				new_seg.bitness = seg.bitness
				new_seg.type = seg.type
				new_seg.perm = seg.perm

				print('Creating .gotrw segment.')
				ida_segment.add_segm_ex(new_seg, '.gotrw', ida_segment.get_segm_class(seg), 0)
			else:
				# If user already has .got, try to rename it (best effort).
				try:
					if ida_segment.get_segm_name(seg) == '.got' and ida_segment.get_segm_by_name('.gotrw') is None:
						ida_segment.set_segm_name(seg, '.gotrw')
				except Exception:
					pass
				# Keep .gotrw clipped to .gotplt if we learned better bounds later.
				try:
					if got_end != ida_idaapi.BADADDR and got_end > self.got_start_ea and got_end != seg.end_ea:
						ida_segment.set_segm_end(seg.start_ea, got_end, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT)
				except Exception:
					pass

			result |= True

		return result

	def _refine_got_plt_start_from_jmprel(self):
		"""
		Refine got_plt_start_ea using JUMP_SLOT relocations.

		On x86_64, the first JUMP_SLOT relocation typically targets GOTPLT[3] (offset +0x18).
		So: gotplt_start ~= min(JUMP_SLOT.r_offset) - 0x18.
		"""
		if not self.jmprel_reloc_table or not self.jmprel_reloc_table.is_table_loaded():
			return False

		min_off = None
		for rec in self._iter_jmprel_records():
			if rec.get('type') != JmpRelRelocTable.R_AMD64_JUMP_SLOT:
				continue
			off = as_uint64(rec.get('r_offset', ida_idaapi.BADADDR))
			if off in (0, ida_idaapi.BADADDR):
				continue
			if min_off is None or off < min_off:
				min_off = off

		if min_off is None:
			return False

		cand = (min_off - 0x18) & ~0x7
		if cand in (0, ida_idaapi.BADADDR) or cand >= min_off:
			return False

		# Basic plausibility: must be mapped/loaded and in the same segment as JUMP_SLOT targets.
		seg1 = ida_segment.getseg(min_off)
		seg2 = ida_segment.getseg(cand)
		if not seg1 or not seg2 or seg1.start_ea != seg2.start_ea:
			return False

		if not ida_bytes.is_loaded(cand):
			# It can still be valid even if unloaded (some loaders map sparse), but avoid
			# making things worse automatically.
			return False

		if self.got_plt_start_ea != cand:
			print('Refined .got.plt start: 0x%x -> 0x%x (from JUMP_SLOT min=0x%x)' % (self.got_plt_start_ea, cand, min_off))
			self.got_plt_start_ea = cand
			return True

		return False

	def _refine_got_start_from_rela(self):
		"""
		Best-effort refine of got_start_ea using GLOB_DAT/64 relocations.

		Some binaries don't reference the first GOT slot in term_proc (or term_proc is atypical),
		so got_start_ea derived from scanning .term_proc can be too late. We approximate GOT start
		as the minimum r_offset among GLOB_DAT/64 relocations that land before .got.plt.
		"""
		if not self.rela_reloc_table or not self.rela_reloc_table.is_table_loaded():
			return False
		if self.got_plt_start_ea in (0, ida_idaapi.BADADDR):
			return False

		min_off = None
		for i in range(self.rela_reloc_table.get_num_entries()):
			entry = self.rela_reloc_table.get_entry(i)
			if not entry:
				continue
			rec = RelaRelocTable.Record(entry)
			rt = rec.get_type()
			if rt not in (RelaRelocTable.R_AMD64_GLOB_DAT, RelaRelocTable.R_AMD64_64):
				continue
			off = as_uint64(rec.entry.get('r_offset', ida_idaapi.BADADDR))
			if off in (0, ida_idaapi.BADADDR):
				continue
			if off >= self.got_plt_start_ea:
				continue
			if min_off is None or off < min_off:
				min_off = off

		if min_off is None:
			return False

		cand = min_off & ~0x7
		seg1 = ida_segment.getseg(self.got_plt_start_ea)
		seg2 = ida_segment.getseg(cand)
		if not seg1 or not seg2 or seg1.start_ea != seg2.start_ea:
			return False

		if self.got_start_ea in (0, ida_idaapi.BADADDR) or cand < self.got_start_ea:
			print('Refined .got start: 0x%x -> 0x%x (from RELA GLOB_DAT/64 min=0x%x)' % (self.got_start_ea, cand, min_off))
			self.got_start_ea = cand
			return True

		return False

	def _fixup_ctors_dtors_segments(self):
		print('Fixing up .ctors and .dtors segments.')

		# The linker must build two lists of these functions - a list of initialization functions, called __CTOR_LIST__, and a list of termination functions, called __DTOR_LIST__.
		#
		# Each list always begins with an ignored function pointer (which may hold 0, -1, or a count of the function pointers after it, depending on the environment).
		# This is followed by a series of zero or more function pointers to constructors (or destructors), followed by a function pointer containing zero.

		data_seg = ida_segment.get_segm_by_name('.data')
		if not data_seg:
			ida_kernwin.warning('Unable to find .data segment, cannot fixup .ctors and .dtors segments.')
			return False
		seg_class, seg_bitness, seg_type, seg_perm = ida_segment.get_segm_class(data_seg), data_seg.bitness, data_seg.type, data_seg.perm

		dtors_start_ea = dtors_end_ea = ida_idaapi.BADADDR
		ctors_start_ea = ctors_end_ea = ida_idaapi.BADADDR

		# Primary: use the SDK-style init/fini procs (more accurate when ctor/dtor lists are non-empty).
		try:
			ea_pair = self._fixup_dtors_segment()
			if ea_pair:
				dtors_start_ea, dtors_end_ea = ea_pair
		except Exception as e:
			print('Warning: _fixup_dtors_segment failed: %s' % e)

		if dtors_start_ea != ida_idaapi.BADADDR and dtors_end_ea != ida_idaapi.BADADDR:
			seg = ida_segment.segment_t()
			seg.start_ea = dtors_start_ea
			seg.end_ea = dtors_end_ea
			seg.bitness = seg_bitness
			seg.type = seg_type
			seg.perm = seg_perm

			print('Creating .dtors segment.')
			ida_segment.add_segm_ex(seg, '.dtors', seg_class, 0)
		else:
			ida_kernwin.warning('Unable to find .dtors segment.')

		# With .dtors created, we can attempt the ctor scan logic that depends on it.
		try:
			ea_pair = self._fixup_ctors_segment()
			if ea_pair:
				ctors_start_ea, ctors_end_ea = ea_pair
		except Exception as e:
			print('Warning: _fixup_ctors_segment failed: %s' % e)

		if ctors_start_ea != ida_idaapi.BADADDR and ctors_end_ea != ida_idaapi.BADADDR:
			seg = ida_segment.segment_t()
			seg.start_ea = ctors_start_ea
			seg.end_ea = ctors_end_ea
			seg.bitness = seg_bitness
			seg.type = seg_type
			seg.perm = seg_perm

			print('Creating .ctors segment.')
			ida_segment.add_segm_ex(seg, '.ctors', seg_class, 0)
		else:
			ida_kernwin.warning('Unable to find .ctors segment.')

		# Fallback (ported from ps5/elf_layout_compare.py): scan RELRO for the common pattern [-1, 0]
		# close to .sce_module_param. This covers many "no global ctors/dtors" PRX and avoids hard-fails.
		if (ida_segment.get_segm_by_name('.ctors') is None) or (ida_segment.get_segm_by_name('.dtors') is None):
			try:
				pair = self._scan_relro_for_ctors_dtors()
				if pair:
					fb_ctors_start, fb_dtors_start = pair
					if ida_segment.get_segm_by_name('.ctors') is None:
						seg = ida_segment.segment_t()
						seg.start_ea = fb_ctors_start
						seg.end_ea = fb_ctors_start + 0x10
						seg.bitness = seg_bitness
						seg.type = seg_type
						seg.perm = seg_perm
						print('Creating .ctors segment (RELRO scan fallback).')
						ida_segment.add_segm_ex(seg, '.ctors', seg_class, 0)
					if ida_segment.get_segm_by_name('.dtors') is None:
						seg = ida_segment.segment_t()
						seg.start_ea = fb_dtors_start
						seg.end_ea = fb_dtors_start + 0x10
						seg.bitness = seg_bitness
						seg.type = seg_type
						seg.perm = seg_perm
						print('Creating .dtors segment (RELRO scan fallback).')
						ida_segment.add_segm_ex(seg, '.dtors', seg_class, 0)
			except Exception as e:
				print('Warning: RELRO ctor/dtor scan failed: %s' % e)

		return True

	def _scan_relro_for_ctors_dtors(self):
		"""
		RELRO scan for empty ctor/dtor tables.

		Ported from ps5/elf_layout_compare.py scan_ctors_dtors():
		- Search PT_GNU_RELRO for the 16-byte pattern [-1, 0]
		- Prefer a hit close below .sce_module_param
		- If two adjacent hits exist (h and h+0x10), treat them as (.ctors, .dtors)
		Returns: (ctors_start_ea, dtors_start_ea) or None.
		"""
		if not self.elf or not getattr(self.elf, 'phdrs', None):
			return None

		mod_seg = ida_segment.get_segm_by_name('.sce_module_param')
		mod_va = mod_seg.start_ea if mod_seg else ida_idaapi.BADADDR
		if mod_va in (0, ida_idaapi.BADADDR):
			return None

		relro = None
		for phdr in self.elf.phdrs:
			try:
				if ElfUtil.phdr_type(phdr) == ElfUtil.PT_GNU_RELRO and as_uint64(phdr.get('p_filesz', 0)) > 0:
					relro = phdr
					break
			except Exception:
				continue
		if not relro:
			return None

		start = as_uint64(relro.get('p_vaddr', ida_idaapi.BADADDR))
		sz = as_uint64(relro.get('p_filesz', 0))
		if start in (0, ida_idaapi.BADADDR) or sz in (0, ida_idaapi.BADADDR):
			return None
		end = start + sz
		if end <= start:
			return None

		hits = []
		for ea in range(start, end - 0x10 + 1, 8):
			if not ida_bytes.is_loaded(ea) or not ida_bytes.is_loaded(ea + 8):
				continue
			a = ida_bytes.get_qword(ea)
			b = ida_bytes.get_qword(ea + 8)
			if a == 0xFFFFFFFFFFFFFFFF and b == 0:
				hits.append(ea)
		if not hits:
			return None

		# Prefer close below module_param.
		cands = [h for h in hits if h < mod_va and (mod_va - h) <= 0x400]
		if not cands:
			cands = hits
		cands = sorted(set(cands))
		hset = set(hits)

		for h in cands:
			if (h + 0x10) in hset:
				# [h..h+0x10) is .ctors, [h+0x10..h+0x20) is .dtors
				# Also create basic names to help later analysis.
				try:
					ida_bytes.create_qword(h, 8, True)
					ida_bytes.create_qword(h + 8, 8, True)
					ida_name.set_name(h, '__CTOR_LIST__', ida_name.SN_NOCHECK)
					ida_name.set_name(h + 8, '__CTOR_END__', ida_name.SN_NOCHECK)
				except Exception:
					pass
				try:
					ida_bytes.create_qword(h + 0x10, 8, True)
					ida_bytes.create_qword(h + 0x18, 8, True)
					ida_name.set_name(h + 0x10, '__DTOR_LIST__', ida_name.SN_NOCHECK)
					ida_name.set_name(h + 0x18, '__DTOR_END__', ida_name.SN_NOCHECK)
				except Exception:
					pass
				return (h, h + 0x10)

		# Single hit only: treat it as .ctors and place .dtors right after it.
		h = cands[-1]
		try:
			ida_bytes.create_qword(h, 8, True)
			ida_bytes.create_qword(h + 8, 8, True)
			ida_name.set_name(h, '__CTOR_LIST__', ida_name.SN_NOCHECK)
			ida_name.set_name(h + 8, '__CTOR_END__', ida_name.SN_NOCHECK)
		except Exception:
			pass
		return (h, h + 0x10)

	def _fixup_init_fini_array_segments(self):
		"""
		Handle modern toolchains that use .preinit_array/.init_array/.fini_array instead of __CTOR_LIST__/__DTOR_LIST__.
		We only create segments/names/data items; we do not attempt to identify or auto-create all constructor functions.
		"""
		print('Fixing up .preinit_array/.init_array/.fini_array segments.')

		def fix_array(seg_name, start_ea, size, start_sym, end_sym):
			start_ea = as_uint64(start_ea)
			size = as_uint64(size)
			if start_ea in [0, ida_idaapi.BADADDR] or size in [0, ida_idaapi.BADADDR]:
				return False

			end_ea = start_ea + size
			if end_ea <= start_ea:
				return False
			if size > 0x1000000:
				# Probably corrupted/invalid; avoid spending minutes creating items.
				print('Warning: suspiciously large %s size: 0x%x, clamping analysis.' % (seg_name, size))

			# Name start/end symbols even if we can't create a segment (overlap, etc.).
			set_name_unique(start_ea, start_sym, ida_name.SN_NOCHECK)
			set_name_unique(end_ea, end_sym, ida_name.SN_NOCHECK)

			# Create segment if not present.
			seg = ida_segment.get_segm_by_name(seg_name)
			if not seg:
				templ = ida_segment.getseg(start_ea) or ida_segment.get_segm_by_name('.data') or ida_segment.get_segm_by_name('.rodata')
				if templ:
					new_seg = ida_segment.segment_t()
					new_seg.start_ea = start_ea
					new_seg.end_ea = end_ea
					new_seg.bitness = templ.bitness
					new_seg.type = templ.type
					new_seg.perm = templ.perm
					if ida_segment.add_segm_ex(new_seg, seg_name, ida_segment.get_segm_class(templ), 0):
						seg = ida_segment.get_segm_by_name(seg_name)
				if not seg:
					ida_kernwin.warning('Unable to create %s segment, leaving it as data only.' % seg_name)

			# Create qwords for entries (best effort).
			entry_sz = struct.calcsize('Q')
			count = size // entry_sz
			max_count = min(count, 0x20000)  # hard cap for safety
			if count != max_count:
				print('Warning: %s entry count %d too large, clamping to %d.' % (seg_name, count, max_count))

			for i in range(max_count):
				ea = start_ea + i * entry_sz
				if not ida_bytes.is_loaded(ea):
					break
				ida_bytes.create_qword(ea, entry_sz, True)
				try:
					idc.op_offset(ea, 0, idc.REF_OFF64)
				except Exception:
					pass

				# If the entry points to code, create a function (best effort).
				ptr = ida_bytes.get_qword(ea)
				if ptr in (0, ida_idaapi.BADADDR) or not idc.is_loaded(ptr):
					continue
				ptr_seg = ida_segment.getseg(ptr)
				if not ptr_seg or (ptr_seg.perm & ida_segment.SEGPERM_EXEC) == 0:
					continue
				if ida_funcs.get_func(ptr) is None:
					try:
						ida_funcs.add_func(ptr, ida_idaapi.BADADDR)
					except Exception:
						pass

			return True

		result = False
		result |= fix_array('.preinit_array', self.preinit_array_ea, self.preinit_array_sz, '__preinit_array_start', '__preinit_array_end')
		result |= fix_array('.init_array', self.init_array_ea, self.init_array_sz, '__init_array_start', '__init_array_end')
		result |= fix_array('.fini_array', self.fini_array_ea, self.fini_array_sz, '__fini_array_start', '__fini_array_end')
		return result

	def _fixup_ctors_segment(self):
		# static func_ptr __CTOR_LIST__[1] = { (func_ptr) (-1) };
		# ...
		# static func_ptr __CTOR_END__[1] = { (func_ptr) 0 };
		#
		# static void __do_global_ctors_aux()
		# {
		#   func_ptr* p;
		#   for (p = __CTOR_END__ - 1; *p != (func_ptr)-1; --p)
		#     (*p)();
		# }

		dtors_seg = ida_segment.get_segm_by_name('.dtors')
		if not dtors_seg:
			ida_kernwin.warning('Unable to find .dtors segment, cannot fixup .ctors segment.')
			return None
		dtors_start_ea, dtors_end_ea = dtors_seg.start_ea, dtors_seg.end_ea
		if dtors_start_ea == ida_idaapi.BADADDR or dtors_end_ea == ida_idaapi.BADADDR:
			ida_kernwin.warning('Unexpected .dtors segment addresses, cannot fixup .ctors segment.')
			return None

		ea = ida_name.get_name_ea(ida_idaapi.BADADDR, '.init_proc')
		if ea == ida_idaapi.BADADDR:
			ea = self.init_proc_ea
			if ea not in (0, ida_idaapi.BADADDR):
				try:
					set_name_unique(ea, '.init_proc', ida_name.SN_NOCHECK)
				except Exception:
					pass
		if ea == ida_idaapi.BADADDR:
			ida_kernwin.warning('Unable to find .init_proc, cannot fixup .ctors segment.')
			return None
		if not ida_funcs.get_func(ea):
			try:
				ida_ua.create_insn(ea)
			except Exception:
				pass
			try:
				ida_funcs.add_func(ea, ida_idaapi.BADADDR)
			except Exception:
				pass

		preinit_array_end_ea = ida_idaapi.BADADDR
		got_plt_end_ea = ida_idaapi.BADADDR
		cmp_found = mov_found = lea_found = False
		mov_reg = None
		for ea in idautils.FuncItems(ea):
			if not cmp_found and check_insn_format(ea, 'cmp', [(ida_ua.o_reg, None), (ida_ua.o_mem, None)]):
				value = idc.get_operand_value(ea, 1)
				if value != ida_idaapi.BADADDR and preinit_array_end_ea == ida_idaapi.BADADDR:
					preinit_array_end_ea = value
				cmp_found = True
			elif not mov_found and check_insn_format(ea, 'mov', [(ida_ua.o_reg, None), (ida_ua.o_phrase, None)]):
				# XXX: Cannot use ida_ua.print_operand because it returns garbage data.
				mov_reg = idc.print_operand(ea, 1).lower().strip().lstrip('[').rstrip(']')
				mov_found = True
			elif not lea_found and mov_found and mov_reg is not None and check_insn_format(ea, 'lea', [(ida_ua.o_reg, mov_reg), (ida_ua.o_mem, None)]):
				value = idc.get_operand_value(ea, 1)
				if value != ida_idaapi.BADADDR and got_plt_end_ea == ida_idaapi.BADADDR:
					got_plt_end_ea = value
				lea_found = True

		ctors_end_ea = dtors_start_ea - 0x8
		if ida_bytes.get_qword(ctors_end_ea) != 0:
			raise RuntimeError('Unexpected end of constructors table.')
		ida_bytes.create_qword(ctors_end_ea, 0x8, True)
		ida_name.set_name(ctors_end_ea, '__CTOR_END__', ida_name.SN_NOCHECK)
		ctors_start_ea = ctors_end_ea - 0x8
		while ida_bytes.get_qword(ctors_start_ea) != ida_idaapi.BADADDR:
			ctors_start_ea -= 0x8
		ida_bytes.create_qword(ctors_start_ea, 0x8, True)
		ida_name.set_name(ctors_start_ea, '__CTOR_LIST__', ida_name.SN_NOCHECK)
		ctors_end_ea += 0x8

		if preinit_array_end_ea != ida_idaapi.BADADDR:
			ida_name.set_name(preinit_array_end_ea, '_G__preinit_array_end', ida_name.SN_NOCHECK)

		return (ctors_start_ea, ctors_end_ea)

	def _fixup_dtors_segment(self):
		# static func_ptr __DTOR_LIST__[1] = { (func_ptr) (-1) };
		# ...
		# static func_ptr __DTOR_END__[1] = { (func_ptr) 0 };
		#
		# static void __do_global_dtors_aux()
		# {
		#   func_ptr* p;
		#   for (p = __DTOR_LIST__ + 1; *p; ++p)
		#     (*p)();
		# }

		ea = ida_name.get_name_ea(ida_idaapi.BADADDR, '.term_proc')
		if ea == ida_idaapi.BADADDR:
			ea = self.term_proc_ea
			if ea not in (0, ida_idaapi.BADADDR):
				try:
					set_name_unique(ea, '.term_proc', ida_name.SN_NOCHECK)
				except Exception:
					pass
		if ea == ida_idaapi.BADADDR:
			ida_kernwin.warning('Unable to find .term_proc, cannot fixup .dtors segment.')
			return None
		if not ida_funcs.get_func(ea):
			try:
				ida_ua.create_insn(ea)
			except Exception:
				pass
			try:
				ida_funcs.add_func(ea, ida_idaapi.BADADDR)
			except Exception:
				pass

		# Derive .got start from raw bytes in term_proc (more robust than relying on IDA instruction decoding).
		def update_got_start(cand):
			if cand in (0, ida_idaapi.BADADDR):
				return
			# Keep the smallest known GOT start (RELA min offset is usually more accurate).
			if self.got_start_ea in (0, ida_idaapi.BADADDR) or cand < self.got_start_ea:
				self.got_start_ea = cand

		# Ported from ps5/elf_layout_compare.py infer_got_start_from_term_proc().
		try:
			b = ida_bytes.get_bytes(ea, 0x80) or b''
			cand = []
			# cmp byte ptr [rip+disp32], 0 : 80 3D <disp32> 00
			for i in range(0, max(0, len(b) - 7)):
				if b[i:i+2] == b'\x80\x3d' and b[i+6] == 0x00:
					disp = struct.unpack_from('<i', b, i+2)[0]
					cand.append((ea + i + 7 + disp) & 0xFFFFFFFFFFFFFFFF)
			# cmp qword ptr [rip+disp32], 0 : 48 83 3D <disp32> 00
			for i in range(0, max(0, len(b) - 8)):
				if b[i:i+3] == b'\x48\x83\x3d' and b[i+7] == 0x00:
					disp = struct.unpack_from('<i', b, i+3)[0]
					cand.append((ea + i + 8 + disp) & 0xFFFFFFFFFFFFFFFF)
			# cmp dword ptr [rip+disp32], 0 : 83 3D <disp32> 00
			for i in range(0, max(0, len(b) - 7)):
				if b[i:i+2] == b'\x83\x3d' and b[i+6] == 0x00:
					disp = struct.unpack_from('<i', b, i+2)[0]
					cand.append((ea + i + 7 + disp) & 0xFFFFFFFFFFFFFFFF)
			if cand:
				update_got_start(cand[-1])
		except Exception:
			pass

		last_lea_value = None
		for ea in idautils.FuncItems(ea):
			if check_insn_format(ea, 'cmp', [(ida_ua.o_mem, None), (ida_ua.o_imm, 0)]):
				value = idc.get_operand_value(ea, 0)
				if value != ida_idaapi.BADADDR:
					update_got_start(value)
			elif check_insn_format(ea, 'lea', [(ida_ua.o_reg, None), (ida_ua.o_mem, None)]):
				value = idc.get_operand_value(ea, 1)
				if value != ida_idaapi.BADADDR:
					last_lea_value = value
			elif check_insn_format(ea, 'add', [(ida_ua.o_reg, None), (ida_ua.o_imm, None)]):
				value = idc.get_operand_value(ea, 1)
				if value != 0x8:
					continue
				if last_lea_value is None:
					raise RuntimeError('Unexpected instructions at .term_proc().')
				break
		if last_lea_value is None:
			raise RuntimeError('Unexpected instructions at .term_proc().')

		# last_lea_value should equals to: __DTOR_LIST__ + 0x10.
		dtors_start_ea = last_lea_value - 0x10
		start_q = ida_bytes.get_qword(dtors_start_ea)
		# Accept "empty list" sentinels produced by SDK crtbegin/crtend objects.
		if start_q not in (ida_idaapi.BADADDR, 0xFFFFFFFFFFFFFFFF, 0x0):
			raise RuntimeError('Unexpected start of destructors table.')
		ida_bytes.create_qword(dtors_start_ea, 0x8, True)
		ida_name.set_name(dtors_start_ea, '__DTOR_LIST__', ida_name.SN_NOCHECK)

		dtors_end_ea = dtors_start_ea + 0x8
		while ida_bytes.get_qword(dtors_end_ea) != 0:
			dtors_end_ea += 0x8
		ida_bytes.create_qword(dtors_end_ea, 0x8, True)
		ida_name.set_name(dtors_end_ea, '__DTOR_END__', ida_name.SN_NOCHECK)
		dtors_end_ea += 0x8

		return (dtors_start_ea, dtors_end_ea)

	def _fixup_bss_segment(self):
		seg = ida_segment.get_segm_by_name('.bss')
		if seg:
			# Segment already exists, skipping it.
			return False

		# Preferred method: use PT_LOAD headers (p_memsz > p_filesz) to locate BSS.
		# This is robust even when section headers are missing/corrupted (common in PS5 binaries).
		try:
			cands = []
			for phdr in getattr(self.elf, 'phdrs', []) or []:
				p_type = ElfUtil.phdr_type(phdr)
				if p_type != ElfUtil.PT_LOAD:
					continue
				flags = phdr.get('p_flags', 0)
				if (flags & ElfUtil.PF_WRITE) == 0:
					continue
				p_filesz = as_uint64(phdr.get('p_filesz', 0))
				p_memsz = as_uint64(phdr.get('p_memsz', 0))
				if p_memsz == ida_idaapi.BADADDR or p_filesz == ida_idaapi.BADADDR:
					continue
				if p_memsz <= p_filesz:
					continue

				va = as_uint64(phdr.get('p_vaddr', ida_idaapi.BADADDR))
				if va in (0, ida_idaapi.BADADDR):
					continue
				bss_start = va + p_filesz
				bss_end = va + p_memsz
				if bss_end <= bss_start:
					continue

				# If the computed start does not land in a writable segment, skip:
				# some binaries have tiny RW tails overlapping special read-only segments.
				s = ida_segment.getseg(bss_start)
				if not s or (s.perm & ida_segment.SEGPERM_WRITE) == 0:
					continue

				cands.append((bss_end - bss_start, bss_end, bss_start, bss_end, va))

			if cands:
				_, _, bss_start_ea, bss_end_ea, va = max(cands)

				# If there is already a dedicated writable segment that exactly matches the range, just convert it.
				existing = ida_segment.getseg(bss_start_ea)
				if existing and existing.start_ea == bss_start_ea and existing.end_ea == bss_end_ea and (existing.perm & ida_segment.SEGPERM_WRITE):
					print('Marking existing segment as .bss.')
					try:
						ida_segment.set_segm_name(existing, '.bss')
					except Exception:
						ida_segment.set_segm_name(existing, '.bss')
					existing.type = ida_segment.SEG_BSS
					existing.perm = ida_segment.SEGPERM_READ | ida_segment.SEGPERM_WRITE
					ida_segment.update_segm(existing)
					return True

				# Shrink any writable segments that overlap the BSS tail, to avoid overlaps.
				for i in range(ida_segment.get_segm_qty()):
					s = ida_segment.getnseg(i)
					if not s or (s.perm & ida_segment.SEGPERM_WRITE) == 0:
						continue
					if s.start_ea < bss_start_ea < s.end_ea:
						try:
							ida_segment.set_segm_end(s.start_ea, bss_start_ea, ida_segment.SEGMOD_KEEP)
						except Exception:
							pass
					elif bss_start_ea <= s.start_ea and s.end_ea <= bss_end_ea:
						# A fully-contained writable segment inside BSS is almost certainly an artifact.
						try:
							ida_segment.del_segm(s.start_ea, ida_segment.SEGMOD_KILL | ida_segment.SEGMOD_SILENT)
						except Exception:
							pass

				templ = ida_segment.getseg(va) or self._find_last_rw_seg()
				if not templ:
					return False

				print('Creating .bss segment.')
				new_seg = ida_segment.segment_t()
				new_seg.start_ea = bss_start_ea
				new_seg.end_ea = bss_end_ea
				new_seg.type = ida_segment.SEG_BSS
				new_seg.bitness = templ.bitness
				new_seg.perm = ida_segment.SEGPERM_READ | ida_segment.SEGPERM_WRITE
				ida_segment.add_segm_ex(new_seg, '.bss', ida_segment.get_segm_class(templ), ida_segment.ADDSEG_NOSREG)
				return True
		except Exception:
			pass

		# Fallback: scan the last writable segment for the first unloaded byte.
		data_seg = self._find_last_rw_seg()
		if not data_seg:
			return False

		bss_start_ea = ida_idaapi.BADADDR
		ea = data_seg.start_ea
		end = data_seg.end_ea
		chunk = 0x1000

		while ea != ida_idaapi.BADADDR and ea < end:
			sz = min(chunk, end - ea)
			buf = ida_bytes.get_bytes(ea, sz)
			if buf is None:
				ea2 = ea
				limit = ea + sz
				while ea2 != ida_idaapi.BADADDR and ea2 < limit:
					if not idc.is_loaded(ea2):
						bss_start_ea = ea2
						break
					ea2 = ida_bytes.next_addr(ea2)
				if bss_start_ea != ida_idaapi.BADADDR:
					break
			ea = ea + sz
		if bss_start_ea == ida_idaapi.BADADDR:
			return False
		bss_end_ea = data_seg.end_ea

		print('Creating .bss segment.')
		new_seg = ida_segment.segment_t()
		new_seg.start_ea = bss_start_ea
		new_seg.end_ea = bss_end_ea
		new_seg.type = ida_segment.SEG_BSS
		new_seg.bitness = data_seg.bitness
		new_seg.perm = ida_segment.SEGPERM_READ | ida_segment.SEGPERM_WRITE
		ida_segment.add_segm_ex(new_seg, '.bss', ida_segment.get_segm_class(data_seg), ida_segment.ADDSEG_NOSREG)

		return True

	def fixup_func_bounds(self, func, max_func_end_ea):
		if self._func_bounds_fixup_active:
			return
		self._func_bounds_fixup_active = True
		try:
			end_ea = func.end_ea

			# Respect IDA's suggested maximum.
			if max_func_end_ea != ida_idaapi.BADADDR and end_ea >= max_func_end_ea:
				return

			insn_len = len(ps5_elf_plugin_t.UD2_INSN_BYTES)
			read_len = insn_len
			if max_func_end_ea != ida_idaapi.BADADDR:
				read_len = min(read_len, max_func_end_ea - end_ea)
				if read_len < insn_len:
					return

			data = ida_bytes.get_bytes(end_ea, read_len)
			if not data or data[:insn_len] != ps5_elf_plugin_t.UD2_INSN_BYTES:
				return

			new_end_ea = end_ea + insn_len
			if max_func_end_ea != ida_idaapi.BADADDR:
				new_end_ea = min(new_end_ea, max_func_end_ea)

			if new_end_ea == func.end_ea:
				return

			print('Setting function 0x%x end to 0x%x (old: 0x%x).' % (func.start_ea, new_end_ea, func.end_ea))
			if ida_funcs.set_func_end(func.start_ea, new_end_ea):
				nf = ida_funcs.get_func(func.start_ea) or func
				ida_funcs.reanalyze_function(nf, nf.start_ea, new_end_ea, False)
		finally:
			self._func_bounds_fixup_active = False

	def _fixup_symbols(self):
		print('Fixing up symbols.')

		if not self.symbol_table or not self.symbol_table.is_table_loaded():
			ida_kernwin.warning('Symbol table is not loaded, cannot fixup symbols.')
			return False

		if not self.string_table or not self.string_table.is_loaded():
			ida_kernwin.warning('String table is not loaded, cannot fixup symbols.')
			return False

		# Avoid duplicate symbol descriptors when pre-analysis is retried.
		self.symbols = []

		for i in range(self.symbol_table.get_num_entries()):
			entry = self.symbol_table.get_entry(i)
			if entry is None:
				ida_kernwin.warning('No entry for symbol table entry #%d.' % i)
				return False

			symbol = SymbolTable.Symbol(entry)

			self.symbols.append(symbol)

			# Prospero uses NID-encoded names for imports/exports. In practice, many UND symbols
			# are STT_NOTYPE (especially on some SDK/toolchain combos). Parse those too, otherwise
			# imports may remain undecoded and later fixups (GOT/PLT) will skip them.
			if symbol.get_type() not in (SymbolTable.STT_OBJECT, SymbolTable.STT_FUNC, SymbolTable.STT_NOTYPE):
				continue

			mangled_name = self.string_table.get_string(symbol.entry['st_name'])
			if not mangled_name:
				continue

			parts = mangled_name.split('#', 2)
			if len(parts) != 3:
				# Not a Prospero-style symbol.
				continue

			symbol_name_enc, lid_enc, mid_enc = parts
			try:
				nid = ObjectInfo.decode_nid(symbol_name_enc)
				lid = ObjectInfo.decode_obj_id(lid_enc)
				mid = ObjectInfo.decode_obj_id(mid_enc)
			except Exception:
				# Corrupted/unknown encoding.
				continue

			module = self.modules.get(mid)
			if not module:
				ida_kernwin.warning('No module with ID: 0x%x (symbol #%d).' % (mid, i))
				continue
			module_name = module.name

			library = self.libraries.get(lid)
			if not library:
				ida_kernwin.warning('No library with ID: 0x%x (symbol #%d).' % (lid, i))
				continue
			library_name = library.name
			role = getattr(library, 'role', ObjectInfo.ROLE_UNKNOWN)
			is_export = bool(role & ObjectInfo.ROLE_EXPORT)
			if role == ObjectInfo.ROLE_UNKNOWN and library.is_export is not None:
				# Backward-compat fallback if role is missing.
				is_export = bool(library.is_export)

			symbol_name = self.nids[nid] if nid in self.nids else nid

			symbol.set_descriptor(module_name, library_name, symbol_name, is_export)

		# Normalize TLS symbol metadata for later relocation handling.
		try:
			self._prepare_tls_symbol_metadata()
		except Exception:
			pass

		return True

	def _fixup_plt_segment(self):
		print('Fixing up .plt segment.')

		if not self.jmprel_reloc_table.is_table_loaded():
			ida_kernwin.warning('Jmprel relocation table is not loaded, cannot fixup .plt segment.')
			return False

		if not self.string_table.is_loaded():
			ida_kernwin.warning('String table is not loaded, cannot fixup .plt segment.')
			return False

		jmprel_entry_count = self.jmprel_reloc_table.get_num_entries()

		got_plt_seg = ida_segment.get_segm_by_name('.gotplt') or ida_segment.get_segm_by_name('.got.plt')
		if not got_plt_seg:
			ida_kernwin.warning('Unable to find .got.plt segment, cannot fixup .plt segment.')
			return False

		# Derive the total PLT entry count (including PLT0) from GOTPLT size and relocation count.
		# Ported from ps5/elf_layout_compare.py.
		gotplt_qwords = max(0, (got_plt_seg.end_ea - got_plt_seg.start_ea) // 8)
		extra = gotplt_qwords - jmprel_entry_count - 2
		if extra < 0:
			extra = 0
		plt_entries = jmprel_entry_count + extra
		if plt_entries <= 0:
			plt_entries = jmprel_entry_count + 1

		target_ea = got_plt_seg.start_ea + struct.calcsize('Q')
		xrefs = list(idautils.XrefsTo(target_ea, ida_xref.XREF_DATA))
		plt_start_ea = ida_idaapi.BADADDR
		if xrefs:
			xref_type, plt_start_ea = xrefs[0].type, xrefs[0].frm
			if xref_type != ida_xref.dr_R:
				print('Warning: unexpected xref type to .got.plt[1]: 0x%x (using xref source anyway).' % xref_type)
		else:
			# Fallback: derive .plt location from DT_FINI and computed PLT entry count.
			#
			# In many PS5 PRX, .plt ends right before .fini (term_proc), and stub size is 0x10.
			# PLT size ~= plt_entries * 0x10.
			if self.term_proc_ea == ida_idaapi.BADADDR or self.term_proc_ea == 0:
				ida_kernwin.warning('Unable to find xrefs to .got.plt and no DT_FINI, cannot fixup .plt segment.')
				return False

			plt_end_ea = as_uint64(self.term_proc_ea)
			plt_size = plt_entries * 0x10
			cand = align_down(plt_end_ea - plt_size, 0x10)

			# Validate PLT0 header by opcodes (ignore operand immediates):
			#   FF 35 xx xx xx xx    push qword ptr [rip+imm32]
			#   FF 25 xx xx xx xx    jmp  qword ptr [rip+imm32]
			hdr = ida_bytes.get_bytes(cand, 12)
			if hdr and len(hdr) >= 12 and hdr[0:2] == b'\xFF\x35' and hdr[6:8] == b'\xFF\x25':
				plt_start_ea = cand
				print('Derived .plt start from DT_FINI/GOTPLT: 0x%x (end=0x%x, entries=%d relocs=%d gotplt_qwords=%d)' % (
					plt_start_ea, plt_end_ea, plt_entries, jmprel_entry_count, gotplt_qwords
				))
			else:
				ida_kernwin.warning('Unable to find xrefs to .got.plt and derived .plt header does not match, cannot fixup .plt segment.')
				return False

		# Validate PLT0 header by opcodes (ignore operand immediates):
		#   FF 35 xx xx xx xx    push qword ptr [rip+imm32]
		#   FF 25 xx xx xx xx    jmp  qword ptr [rip+imm32]
		hdr = ida_bytes.get_bytes(plt_start_ea, 12)
		if not hdr or len(hdr) < 12 or hdr[0:2] != b'\xFF\x35' or hdr[6:8] != b'\xFF\x25':
			ida_kernwin.warning('Unexpected .plt header, cannot fixup .plt segment.')
			return False

		super_seg = ida_segment.getseg(plt_start_ea)
		if not super_seg:
			ida_kernwin.warning('Unable to find segment which includes .plt, cannot fixup .plt segment.')
			return False

		def is_plt_stub_start(ea):
			# Typical stub (16 bytes, aligned) in PS5:
			#   FF 25 ?? ?? ?? ??   jmp qword ptr [rip+imm32]
			#   68 imm32            push imm32
			#   E9 rel32            jmp rel32
			#
			# Some toolchains may encode push as imm8 (6A xx). Keep that variant too.
			if not ida_bytes.is_loaded(ea) or not ida_bytes.is_loaded(ea + 6):
				return False
			if ida_bytes.get_byte(ea) != 0xFF or ida_bytes.get_byte(ea + 1) != 0x25:
				return False
			push_op = ida_bytes.get_byte(ea + 6)
			if push_op == 0x68:
				return ida_bytes.is_loaded(ea + 11) and ida_bytes.get_byte(ea + 11) == 0xE9
			if push_op == 0x6A:
				return ida_bytes.is_loaded(ea + 8) and ida_bytes.get_byte(ea + 8) == 0xE9
			return False

		# Find the first stub start after PLT0.
		search_start = plt_start_ea + 12
		plt_base_ea = ida_idaapi.BADADDR
		cand = ida_bytes.find_bytes('FF 25', range_start=search_start, range_end=super_seg.end_ea, flags=ida_search.SEARCH_DOWN | ida_search.SEARCH_CASE)
		while cand != ida_idaapi.BADADDR:
			if is_plt_stub_start(cand):
				plt_base_ea = cand
				break
			cand = ida_bytes.find_bytes('FF 25', range_start=cand + 1, range_end=super_seg.end_ea, flags=ida_search.SEARCH_DOWN | ida_search.SEARCH_CASE)

		if plt_base_ea == ida_idaapi.BADADDR:
			ida_kernwin.warning('Unable to find .plt stubs base ea, cannot fixup .plt segment.')
			return False

		PLT_STUB_SIZE = 0x10

		# Do not blindly trust jmprel count: some binaries are not fully relocated/standard,
		# and creating an oversized .plt segment causes analysis failures.
		max_count = min(jmprel_entry_count, max(0, (super_seg.end_ea - plt_base_ea) // PLT_STUB_SIZE))
		plt_stub_count = 0
		for i in range(max_count):
			if not is_plt_stub_start(plt_base_ea + i * PLT_STUB_SIZE):
				break
			plt_stub_count += 1

		if plt_stub_count == 0:
			ida_kernwin.warning('Unable to validate any .plt stubs, skipping .plt segment creation.')
			return False

		# Prefer the computed total entry count to set .plt size; it matches retail PRX layouts.
		plt_end_ea = align_up(plt_start_ea + plt_entries * PLT_STUB_SIZE, 0x10)
		if plt_end_ea > super_seg.end_ea:
			plt_end_ea = align_up(plt_base_ea + plt_stub_count * PLT_STUB_SIZE, 0x10)

		seg = ida_segment.get_segm_by_name('.plt')
		if not seg:
			new_seg = ida_segment.segment_t()
			new_seg.start_ea = plt_start_ea
			new_seg.end_ea = plt_end_ea
			new_seg.bitness = super_seg.bitness
			new_seg.type = super_seg.type
			new_seg.perm = super_seg.perm

			print('Creating .plt segment.')
			ida_segment.add_segm_ex(new_seg, '.plt', ida_segment.get_segm_class(super_seg), 0)
		else:
			# Segment already exists, skipping it.
			pass

		idaldr_node = ida_netnode.netnode('$ IDALDR node for ids loading $')
		if not idaldr_node:
			ida_kernwin.warning('Unable to find netnode for imports.')

		records = list(self._iter_jmprel_records(max_count=min(jmprel_entry_count, plt_stub_count)))
		if not records:
			ida_kernwin.warning('Unable to decode JMPREL records, cannot rename .plt imports.')
			return False

		skipped = 0
		reported = 0
		for i, record in enumerate(records):
			reloc_type = record.get('type', 0xFFFFFFFF)
			if reloc_type != JmpRelRelocTable.R_AMD64_JUMP_SLOT:
				# Do not hard-fail: some binaries may have mixed/invalid records.
				# Keep PLT recovery best-effort for the rest of entries.
				if reported < 8:
					print('Warning: skipping unsupported jmprel relocation type 0x%x at entry #%d.' % (reloc_type, i))
					reported += 1
				skipped += 1
				continue

			symbol_idx = as_uint64(record.get('sym', ida_idaapi.BADADDR))
			if symbol_idx >= len(self.symbols):
				ida_kernwin.warning('Symbol index #%d out of range for jmprel relocation table entry #%d.' % (symbol_idx, i))
				return False
			symbol = self.symbols[symbol_idx]

			if not symbol.has_descriptor():
				ida_kernwin.warning('Symbol #%d has no descriptor for jmprel relocation table entry #%d.' % (symbol_idx, i))
				return False

			name = symbol.get_name()
			name_ex = symbol.get_name_ex()
			comment = symbol.get_name_comment()

			stub_name = '/B%s' % name_ex
			stub_ptr_name = '/PG%s' % name_ex

			stub_ptr_ea = as_uint64(record.get('r_offset', ida_idaapi.BADADDR))
			stub_ea = ida_bytes.get_qword(stub_ptr_ea)
			stub_is_valid = stub_ea not in (0, ida_idaapi.BADADDR) and ida_bytes.is_loaded(stub_ea)
			used_stub_name = None
			func_ea = plt_base_ea + i * PLT_STUB_SIZE

			#print('Renaming stub pointer %s to %s at 0x%x.' % (ida_name.get_name(stub_ptr_ea), stub_ptr_name, stub_ptr_ea))
			used_stub_ptr_name = set_name_unique(stub_ptr_ea, stub_ptr_name, ida_name.SN_NOCHECK)
			ida_bytes.set_cmt(stub_ptr_ea, '', False)

			if stub_is_valid:
				#print('Renaming stub %s to %s at 0x%x.' % (ida_name.get_name(stub_ea), stub_name, stub_ea))
				used_stub_name = set_name_unique(stub_ea, stub_name, ida_name.SN_NOCHECK)
				ida_bytes.set_cmt(stub_ea, '', False)

			func = ida_funcs.get_func(func_ea)
			if not func:
				ida_funcs.add_func(func_ea, ida_idaapi.BADADDR)

			#print('Renaming function %s to %s at 0x%x.' % (ida_name.get_name(func_ea), name, func_ea))
			used_func_name = set_name_unique(func_ea, name, ida_name.SN_NOCHECK, fallback_names=[name_ex])
			ida_bytes.set_cmt(func_ea, comment, False)

			if stub_is_valid:
				func = ida_funcs.get_func(stub_ea)
				if not func:
					ida_funcs.add_func(stub_ea, ida_idaapi.BADADDR)

			func = ida_funcs.get_func(func_ea)
			if func:
				func.flags |= ida_funcs.FUNC_LIB
				ida_funcs.update_func(func)

			if stub_is_valid:
				func = ida_funcs.get_func(stub_ea)
				if func:
					func.flags |= ida_funcs.FUNC_LIB
					ida_funcs.update_func(func)

			if idaldr_node and stub_is_valid:
				idaldr_node.supset_ea(stub_ea, used_stub_name or stub_name, ida_netnode.stag)

		if skipped > reported:
			print('Warning: skipped %d additional unsupported jmprel entries.' % (skipped - reported))
		if skipped:
			print('JMPREL summary: processed=%d skipped=%d' % (len(records) - skipped, skipped))

		return True

	def _fixup_relocations(self):
		print('Fixing up relocations.')

		if not self.rela_reloc_table.is_table_loaded():
			ida_kernwin.warning('Rela relocation table is not loaded, cannot fixup relocations.')
			return False

		if not self.string_table.is_loaded():
			ida_kernwin.warning('String table is not loaded, cannot fixup relocations.')
			return False

		idaldr_node = ida_netnode.netnode('$ IDALDR node for ids loading $')
		if not idaldr_node:
			ida_kernwin.warning('Unable to find netnode for imports.')

		rela_entry_count = self.rela_reloc_table.get_num_entries()
		seg_is_got_cache = {}

		def is_got_slot(ea):
			seg = ida_segment.getseg(ea)
			if not seg:
				return False
			key = seg.start_ea
			if key in seg_is_got_cache:
				return seg_is_got_cache[key]
			try:
				name = ida_segment.get_segm_name(seg) or ''
			except Exception:
				name = ''
			v = ('got' in name.lower())
			seg_is_got_cache[key] = v
			return v

		def try_add_slot_dref(slot_ea, dst_ea):
			if slot_ea in (0, ida_idaapi.BADADDR):
				return False
			if dst_ea in (0, ida_idaapi.BADADDR):
				return False
			try:
				if not idc.is_loaded(slot_ea):
					return False
				if not idc.is_loaded(dst_ea):
					return False
			except Exception:
				return False

		def symbol_name_safe(symbol, symbol_idx):
			try:
				if symbol and symbol.has_descriptor():
					return symbol.get_name_ex()
			except Exception:
				pass
			return 'sym_%d' % symbol_idx

		def tls_info_from_symbol(symbol):
			abs_ea = getattr(symbol, 'tls_abs_ea', ida_idaapi.BADADDR)
			off = getattr(symbol, 'tls_offset', ida_idaapi.BADADDR)
			if abs_ea not in (0, ida_idaapi.BADADDR) and off not in (ida_idaapi.BADADDR,):
				return abs_ea, off
			try:
				raw = as_uint64(symbol.entry.get('st_value', 0))
			except Exception:
				raw = 0
			return self._resolve_tls_value(raw)[:2]
			if hasattr(gcc_extab, 'safe_add_dref'):
				try:
					return bool(gcc_extab.safe_add_dref(slot_ea, dst_ea, create_from=True, create_to=False))
				except Exception:
					return False
			try:
				if not ida_bytes.is_head(ida_bytes.get_full_flags(slot_ea)):
					return False
				ida_xref.add_dref(slot_ea, dst_ea, ida_xref.dr_O | ida_xref.XREF_USER)
				return True
			except Exception:
				return False

		for i in range(rela_entry_count):
			if (i & 0x3FF) == 0:
				try:
					ida_kernwin.replace_wait_box('PS5 ELF pre-analysis\nApply relocations\nRELA entries: %d/%d' % (i, rela_entry_count))
				except Exception:
					pass
				try:
					if ida_kernwin.user_cancelled():
						print('Fixing up relocations canceled by user.')
						return False
				except Exception:
					pass
			entry = self.rela_reloc_table.get_entry(i)
			if entry is None:
				ida_kernwin.warning('No entry for rela relocation table entry #%d.' % i)
				return False

			record = RelaRelocTable.Record(entry)
			reloc_type = record.get_type()

			target_ea, addend = as_uint64(record.entry['r_offset']), as_uint64(record.entry['r_addend'])

			if reloc_type in [RelaRelocTable.R_AMD64_GLOB_DAT, RelaRelocTable.R_AMD64_64]:
				# For GLOB_DAT/64 relocations r_offset usually points to a GOT slot (IDA: ".gotrw"/".got").
				# Name the slot itself (like an import pointer). Optionally rename its pointee stub too.
				slot_ea = target_ea
				symbol_idx = record.get_symbol_idx()
				if symbol_idx >= len(self.symbols):
					continue

				symbol = self.symbols[symbol_idx]
				if not symbol.has_descriptor():
					continue

				name = symbol.get_name()
				if not name:
					continue

				# Ensure qword item and make it an offset.
				try:
					ida_bytes.create_qword(slot_ea, 8, True)
				except Exception:
					pass
				try:
					idc.op_offset(slot_ea, 0, idc.REF_OFF64)
				except Exception:
					pass

				name_ex = symbol.get_name_ex()
				comment = symbol.get_name_comment()
				slot_qword = ida_bytes.get_qword(slot_ea)
				pointee = slot_qword
				# Many PS5 images keep GOT slots zero in the file and resolve them at runtime.
				# For non-UND symbols we can still recover a meaningful target from dynsym+addend.
				if pointee in (0, ida_idaapi.BADADDR) and not symbol.is_undef:
					try:
						sym_ea = as_uint64(symbol.entry.get('st_value', 0))
					except Exception:
						sym_ea = 0
					if sym_ea not in (0, ida_idaapi.BADADDR):
						pointee = as_uint64(sym_ea + addend)

				# Prefer __imp_* naming for undefined imports (functions and data). This mirrors SDK-style
				# naming and makes imports visible even when they are resolved via GLOB_DAT rather than PLT.
				if name_ex and symbol.is_undef:
					slot_name = '__imp_%s' % name_ex
					used = set_name_unique(slot_ea, slot_name, ida_name.SN_NOCHECK)
					ida_bytes.set_cmt(slot_ea, comment, False)
					if idaldr_node and used:
						idaldr_node.supset_ea(slot_ea, used, ida_netnode.stag)

					# If the slot points at an extern placeholder or a local thunk, still rename it
					# so NID-only names (e.g. pDBDcY6uLSA_B_C) become meaningful.
					if pointee not in (0, ida_idaapi.BADADDR):
						stub_name = '/B%s' % name_ex
						try:
							set_name_unique(pointee, stub_name, ida_name.SN_NOCHECK, fallback_names=[name])
							ida_bytes.set_cmt(pointee, comment, False)
							if idaldr_node:
								idaldr_node.supset_ea(pointee, stub_name, ida_netnode.stag)
						except Exception:
							pass
					try_add_slot_dref(slot_ea, pointee)
					continue

				seg = ida_segment.getseg(slot_ea)
				seg_name = ida_segment.get_segm_name(seg) if seg else ''
				prefix = 'got_' if (seg_name and 'got' in seg_name) else 'ptr_'
				slot_name = prefix + (name_ex or name)
				used = set_name_unique(slot_ea, slot_name, ida_name.SN_NOCHECK, fallback_names=[prefix + name])
				if idaldr_node and used:
					idaldr_node.supset_ea(slot_ea, used, ida_netnode.stag)

				# Optionally name the pointed-to address if it's already resolved and mapped.
				if pointee not in (0, ida_idaapi.BADADDR) and idc.is_loaded(pointee):
					set_name_unique(pointee, name, ida_name.SN_NOCHECK, fallback_names=[symbol.get_name_ex()])
				try_add_slot_dref(slot_ea, pointee)
			elif reloc_type == RelaRelocTable.R_AMD64_RELATIVE:
				# Helpful for GOT-like slots: keep data xrefs even when file bytes are zero and
				# runtime relocation writes (base + addend) later.
				slot_ea = target_ea
				if is_got_slot(slot_ea):
					try:
						ida_bytes.create_qword(slot_ea, 8, True)
					except Exception:
						pass
					try_add_slot_dref(slot_ea, addend)
				continue
			elif reloc_type in (
				RelaRelocTable.R_AMD64_DTPMOD64,
				RelaRelocTable.R_AMD64_DTPOFF64,
				RelaRelocTable.R_AMD64_TPOFF64,
				RelaRelocTable.R_AMD64_DTPOFF32,
				RelaRelocTable.R_AMD64_TPOFF32,
			):
				# TLS relocations are usually resolved by runtime loader and may not have meaningful
				# file-time slot contents. Keep best-effort labels/comments/xrefs instead of warning.
				slot_ea = target_ea
				symbol_idx = record.get_symbol_idx()
				symbol = self.symbols[symbol_idx] if 0 <= symbol_idx < len(self.symbols) else None
				sym_name = symbol_name_safe(symbol, symbol_idx)
				abs_ea = ida_idaapi.BADADDR
				tls_off = ida_idaapi.BADADDR
				if symbol:
					abs_ea, tls_off = tls_info_from_symbol(symbol)

				# Data item width follows relocation flavor.
				try:
					if reloc_type in (RelaRelocTable.R_AMD64_DTPOFF32, RelaRelocTable.R_AMD64_TPOFF32):
						ida_bytes.create_dword(slot_ea, 4, True)
					else:
						ida_bytes.create_qword(slot_ea, 8, True)
				except Exception:
					pass

				if reloc_type == RelaRelocTable.R_AMD64_DTPMOD64:
					slot_name = '__tlsmod_%s' % sym_name
					cmt = 'TLS DTPMOD64 (module id), sym=%s' % sym_name
				elif reloc_type in (RelaRelocTable.R_AMD64_DTPOFF64, RelaRelocTable.R_AMD64_DTPOFF32):
					slot_name = '__dtpoff_%s' % sym_name
					if tls_off not in (ida_idaapi.BADADDR,):
						cmt = 'TLS DTPOFF=0x%x, sym=%s' % (as_uint64(tls_off), sym_name)
					else:
						cmt = 'TLS DTPOFF, sym=%s' % sym_name
				else:
					slot_name = '__tpoff_%s' % sym_name
					if tls_off not in (ida_idaapi.BADADDR,):
						cmt = 'TLS TPOFF (model-specific), dtp_off=0x%x, sym=%s' % (as_uint64(tls_off), sym_name)
					else:
						cmt = 'TLS TPOFF (model-specific), sym=%s' % sym_name

				used = set_name_unique(slot_ea, slot_name, ida_name.SN_NOCHECK)
				if used and idaldr_node:
					idaldr_node.supset_ea(slot_ea, used, ida_netnode.stag)
				ida_bytes.set_cmt(slot_ea, cmt, False)
				if abs_ea not in (0, ida_idaapi.BADADDR):
					try_add_slot_dref(slot_ea, abs_ea)
				continue
			else:
				print('Warning! Unsupported relocation type 0x%x for rela relocation table entry #%d.' % (reloc_type, i))
				continue

		# Diagnostics: help track down PRX_NOT_RESOLVED_FUNCTION cases.
		try:
			self._diagnose_undef_without_relocs()
		except Exception:
			pass

		return True

	def _diagnose_undef_without_relocs(self):
		"""
		Report undefined function imports that don't have corresponding relocations.

		This catches cases where the dynsym has UND entries but the loader can't resolve them
		(or they are never referenced through PLT/GOT, so they won't show up as imports).
		"""
		if not self.symbols:
			return False

		used = set()

		# JMPREL -> JUMP_SLOT imports
		if self.jmprel_reloc_table and self.jmprel_reloc_table.is_table_loaded():
			for rec in self._iter_jmprel_records():
				if rec.get('type') != JmpRelRelocTable.R_AMD64_JUMP_SLOT:
					continue
				used.add(as_uint64(rec.get('sym', 0)))

		# RELA -> GLOB_DAT/64 imports (GOTRW)
		if self.rela_reloc_table and self.rela_reloc_table.is_table_loaded():
			for i in range(self.rela_reloc_table.get_num_entries()):
				entry = self.rela_reloc_table.get_entry(i)
				if not entry:
					continue
				rec = RelaRelocTable.Record(entry)
				if rec.get_type() not in (RelaRelocTable.R_AMD64_GLOB_DAT, RelaRelocTable.R_AMD64_64):
					continue
				used.add(rec.get_symbol_idx())

		missing = []
		for idx, sym in enumerate(self.symbols):
			try:
				if not sym.is_undef:
					continue
				# Only highlight function imports (objects often use RELATIVE, etc.)
				if not sym.is_func():
					continue
				if idx in used:
					continue
				if not sym.has_descriptor():
					continue
				missing.append(sym)
			except Exception:
				continue

		if not missing:
			return False

		print('Warning: UND function imports without relocations: %d' % len(missing))
		for s in missing[:20]:
			try:
				print('  - %s' % s.get_name_ex())
			except Exception:
				pass
		if len(missing) > 20:
			print('  (truncated)')
		return True

	def _fixup_exports(self):
		print('Fixing up exports.')

		ea_ordinal_map = {}
		main_module_name = None
		try:
			main_module = self.modules.get(0)
			if main_module and getattr(main_module, 'name', None):
				main_module_name = main_module.name
		except Exception:
			main_module_name = None

		for i in range(ida_entry.get_entry_qty()):
			ordinal = ida_entry.get_entry_ordinal(i)
			ea = ida_entry.get_entry(ordinal)
			ea_ordinal_map[ea] = ordinal

		for i, symbol in enumerate(self.symbols):
			# Prefer explicit export role. Fallback to main-module defined globals for
			# binaries where export role tags are partially missing/inconsistent.
			is_main_defined = (
				(not symbol.is_undef)
				and (main_module_name is not None)
				and (symbol.module_name == main_module_name)
				and (symbol.is_global() or symbol.is_weak())
			)
			if not symbol.is_export and not is_main_defined:
				continue

			if not symbol.has_descriptor():
				continue

			ea, size = symbol.entry['st_value'], symbol.entry['st_size']
			if ea == 0 or ea == ida_idaapi.BADADDR:
				continue

			# Create/refresh function boundaries only for function exports.
			if symbol.is_func():
				func = ida_funcs.get_func(ea)
				if not func:
					ida_bytes.del_items(ea, ida_bytes.DELIT_SIMPLE, size)
					ida_ua.create_insn(ea)
					if size not in (0, ida_idaapi.BADADDR):
						ida_funcs.add_func(ea, ea + size)
					else:
						ida_funcs.add_func(ea, ida_idaapi.BADADDR)

			name = symbol.get_name()

			print('Setting name %s to exported function at 0x%x.' % (name, ea))
			if ea in ea_ordinal_map:
				ordinal = ea_ordinal_map[ea]
				if not ida_entry.rename_entry(ordinal, name, ida_entry.AEF_UTF8):
					used = set_name_unique(ea, name, ida_name.SN_NOCHECK, fallback_names=[symbol.get_name_ex()])
					if used is not None:
						ida_entry.rename_entry(ordinal, used, ida_entry.AEF_UTF8)
			else:
				set_name_unique(ea, name, ida_name.SN_NOCHECK, fallback_names=[symbol.get_name_ex()])
			ida_bytes.set_cmt(ea, '', False)

		return True

	def _fixup_dynsym_segment(self):
		print('Deleting .dynsym segment.')

		seg = ida_segment.get_segm_by_name('.dynsym')
		if not seg:
			ida_kernwin.warning('Unable to find .dynsym segment, cannot fixup .dynsym segment.')
			return False

		ida_segment.del_segm(seg.start_ea, ida_segment.SEGMOD_KILL | ida_segment.SEGMOD_SILENT)

		return True

	def _mark_noret_funcs(self):
		names = [
			'exit', 'exit1', 'abort',
			'__stack_chk_fail',
			'_ZNSt9bad_allocD0Ev', '_ZNSt9bad_allocD1Ev', '_ZNSt9bad_allocD2Ev', '_ZSt11_Xbad_allocv',
			'_ZNSt16invalid_argumentD0Ev', '_ZNSt16invalid_argumentD1Ev', '_ZNSt16invalid_argumentD2Ev', '_ZSt18_Xinvalid_argumentPKc',
			'_ZNSt12length_errorD0Ev', '_ZNSt12length_errorD1Ev', '_ZNSt12length_errorD2Ev', '_ZSt14_Xlength_errorPKc',
			'_ZNSt12out_of_rangeD0Ev', '_ZNSt12out_of_rangeD1Ev', '_ZNSt12out_of_rangeD2Ev', '_ZSt14_Xout_of_rangePKc',
			'_ZNSt14overflow_errorD0Ev', '_ZNSt14overflow_errorD1Ev', '_ZNSt14overflow_errorD2Ev', '_ZSt16_Xoverflow_errorPKc',
			'_ZNSt13runtime_errorD0Ev', '_ZNSt13runtime_errorD1Ev', '_ZNSt13runtime_errorD2Ev', '_ZSt15_Xruntime_errorPKc',
			'_ZNSt17bad_function_callD0Ev', '_ZNSt17bad_function_callD1Ev', '_ZNSt17bad_function_callD2Ev', '_ZSt19_Xbad_function_callv',
			'_ZNSt11regex_errorD0Ev', '_ZNSt11regex_errorD1Ev', '_ZNSt11regex_errorD2Ev',
			'_ZSt10_Rng_abortPKc',
			'_ZSt19_Throw_future_errorRKSt10error_code',
			'_ZSt25_Rethrow_future_exceptionPv', '_ZSt25_Rethrow_future_exceptionSt13exception_ptr',
		]

		for name in names:
			ea = ida_name.get_name_ea(ida_idaapi.BADADDR, name)
			if ea == ida_idaapi.BADADDR:
				continue

			func = ida_funcs.get_func(ea)
			if not func:
				continue

			func.flags |= ida_funcs.FUNC_NORET
			ida_funcs.update_func(func)

			ida_auto.reanalyze_callers(ea, True)

	def _find_last_rw_seg(self):
		rw_seg = None

		seg, first_seg = ida_segment.get_last_seg(), ida_segment.get_first_seg()
		while seg and seg != first_seg:
			name = ida_segment.get_segm_name(seg)
			sclass = ida_segment.get_segm_class(seg)
			if seg.perm == ida_segment.SEGPERM_READ | ida_segment.SEGPERM_WRITE:
				rw_seg = seg
				break
			seg = ida_segment.get_prev_seg(seg.start_ea)

		return rw_seg

	def _print_analysis_summary(self):
		if self.soname is not None:
			print('Name: %s' % self.soname)
		if self.orig_file_path is not None:
			print('Original file path: %s' % self.orig_file_path)

		if self.init_proc_ea != ida_idaapi.BADADDR:
			print('Address of .init_proc function: 0x%x' % self.init_proc_ea)
		if self.term_proc_ea != ida_idaapi.BADADDR:
			print('Address of .term_proc function: 0x%x' % self.term_proc_ea)

		if self.needed_modules:
			print('Needed modules: %s' % ', '.join(self.needed_modules))
		for id, info in self.modules.items():
			print('Module #%03d: %s' % (id, repr(info)))
		for id, info in self.libraries.items():
			print('Library #%03d: %s' % (id, repr(info)))

		if self.relocation_type is not None:
			print('Relocation type: 0x%x' % self.relocation_type)

	def _ensure_analysis_context(self):
		# Load global plugin settings once; analysis stages use self.settings.
		if self.settings is None:
			self.settings = self._settings_load()

		# Ensure ELF helper is initialized for this IDB.
		if self.elf is None or not getattr(self.elf, 'is_inited', lambda: False)():
			self.elf = ElfUtil()
		if not self.elf.is_inited():
			raise RuntimeError('Netnode for elf is not initialized.')

	def _run_with_progress(self, stage_name, steps):
		"""
		Run named steps with a wait box and periodic UI updates.
		Returns False if user canceled.
		"""
		total = len(steps)
		try:
			ida_kernwin.show_wait_box('%s\nStarting...' % stage_name)
		except Exception:
			pass

		try:
			for idx, step in enumerate(steps, 1):
				strict = False
				if len(step) >= 3:
					label, cb, strict = step[0], step[1], bool(step[2])
				else:
					label, cb = step[0], step[1]
				msg = '%s\n[%d/%d] %s' % (stage_name, idx, total, label)
				print('[%s] %d/%d: %s' % (stage_name, idx, total, label))
				try:
					ida_kernwin.replace_wait_box(msg)
				except Exception:
					pass
				try:
					ida_kernwin.refresh_idaview_anyway()
				except Exception:
					pass
				try:
					if ida_kernwin.user_cancelled():
						print('[%s] Canceled by user at step %d/%d.' % (stage_name, idx, total))
						return False
				except Exception:
					pass
				ok = cb()
				if strict and ok is False:
					print('[%s] Step failed at %d/%d: %s' % (stage_name, idx, total, label))
					return False
			return True
		finally:
			try:
				ida_kernwin.hide_wait_box()
			except Exception:
				pass

	def _enable_jump_rename_and_reanalyze(self):
		"""
		After plugin-driven renaming/fixups are complete, enable IDA's jump-function
		renaming and run one reanalysis pass so J_* names are applied consistently.
		"""
		try:
			ida_ida.inf_set_rename_jumpfunc(True)
		except Exception:
			return False

		try:
			start_ea = ida_ida.inf_get_min_ea()
			end_ea = ida_ida.inf_get_max_ea()
			if start_ea == ida_idaapi.BADADDR or end_ea == ida_idaapi.BADADDR or end_ea <= start_ea:
				return False
			print('Running reanalysis after enabling rename_jumpfunc (0x%x..0x%x).' % (start_ea, end_ea))
			rc = ida_auto.plan_and_wait(start_ea, end_ea, True)
			return bool(rc)
		except Exception:
			try:
				ida_kernwin.msg('[ps5_elf] Reanalysis after enabling rename_jumpfunc failed:\n')
				ida_kernwin.msg(traceback.format_exc() + '\n')
			except Exception:
				pass
			return False

	def pre_initial_analysis(self):
		if self._pre_analysis_done:
			return True

		self._ensure_analysis_context()
		print('Performing pre initial auto analysis.')
		def step_fixup_segments():
			for i in range(ida_segment.get_segm_qty()):
				seg = ida_segment.getnseg(i)
				if seg:
					self._fixup_segment(seg)

		def step_refine_got():
			try:
				self._refine_got_plt_start_from_jmprel()
			except Exception:
				pass
			try:
				self._refine_got_start_from_rela()
			except Exception:
				pass

		steps = [
			('Normalize initial segments', step_fixup_segments),
			('Parse dynamic/extra segments', self._parse_extra_segments, True),
			('Fix segment permissions', self._fixup_segment_perms),
			('Link segments with PHDRs', self._link_segments_with_phdrs),
			('Create .sce_padding', self._fixup_padding_segment),
			('Process .sce_*_param', self._fixup_param_segment),
			('Fix .data segment', self._fixup_data_segment),
			('Fix .eh_frame/.eh_frame_hdr', self._fixup_eh_segments),
			('Fix init/fini arrays', self._fixup_init_fini_array_segments),
			('Refine GOT/GOTPLT starts', step_refine_got),
			('Fix .got/.got.plt segments', self._fixup_got_segments),
			('Fix .bss segment', self._fixup_bss_segment),
			('Fix extra .data segments', self._fixup_extra_segments),
			('Decode symbols', self._fixup_symbols, True),
			('Apply relocations', self._fixup_relocations, True),
		]

		ok = self._run_with_progress('PS5 ELF pre-analysis', steps)
		if not ok:
			return False

		# Keep jump-function auto-rename disabled:
		# it can rewrite names to J_* and interfere with deterministic post-fixups.
		ida_ida.inf_set_rename_jumpfunc(False)

		self._pre_analysis_done = True
		return True

	def post_initial_analysis(self):
		if self._post_analysis_done:
			return True
		if self._post_analysis_running:
			return False
		self._post_analysis_running = True

		try:
			# Fallback for IDA sessions where loader_finished wasn't observed by hooks.
			if not self._pre_analysis_done:
				self.pre_initial_analysis()

			self._ensure_analysis_context()
			print('Performing post initial auto analysis.')

			# Heuristic/late passes that benefit from initial IDA analysis.
			steps = [
				('Fix .init/.fini segments', self._fixup_init_fini_segments),
				('Fix .ctors/.dtors segments', self._fixup_ctors_dtors_segments),
				('Refresh .got/.got.plt bounds', self._fixup_got_segments),
				('Process TLS template', self._fixup_tls_template),
				('Adjust functions from .eh_frame', self._fixup_funcs_from_eh_frame),
				('Apply GNU_RELRO permissions', self._fixup_relro_segments),
				('Fix .plt segment and names', self._fixup_plt_segment, True),
				('Apply exports', self._fixup_exports, True),
				('Drop transient .dynsym', self._fixup_dynsym_segment),
				('Mark known no-return functions', self._mark_noret_funcs),
				('Enable J_* rename and reanalyze', self._enable_jump_rename_and_reanalyze),
				# Run LSDA recovery last, after reanalysis has created/stabilized item heads.
				('Recover LSDA/.gcc_except_table', self._fixup_lsda_from_eh_frame),
			]
			ok = self._run_with_progress('PS5 ELF post-analysis', steps)
			if not ok:
				return False

			self._print_analysis_summary()
			self._post_analysis_done = True
			return True
		finally:
			self._post_analysis_running = False

	def _collect_pt_tls_templates(self):
		"""
		Collect normalized PT_TLS templates from ELF program headers.
		Returns list of dicts: {start, filesz, memsz, end}.
		"""
		out = []
		if not self.elf or not getattr(self.elf, 'phdrs', None):
			return out
		for phdr in self.elf.phdrs:
			try:
				if ElfUtil.phdr_type(phdr) != ElfUtil.PT_TLS:
					continue
				start = as_uint64(phdr.get('p_vaddr', ida_idaapi.BADADDR))
				memsz = as_uint64(phdr.get('p_memsz', 0))
				filesz = as_uint64(phdr.get('p_filesz', 0))
			except Exception:
				continue
			if start in (0, ida_idaapi.BADADDR) or memsz in (0, ida_idaapi.BADADDR):
				continue
			end = start + memsz
			if end <= start:
				continue
			if filesz > memsz:
				filesz = memsz
			out.append({
				'start': start,
				'filesz': filesz,
				'memsz': memsz,
				'end': end,
			})
		return out

	def _resolve_tls_value(self, value):
		"""
		Resolve potentially-absolute TLS symbol value into:
		  (abs_ea, dtp_off, template_index)
		Returns BADADDR values when unresolved.
		"""
		raw = as_uint64(value)
		tpls = self._tls_templates or self._collect_pt_tls_templates()
		if not tpls:
			return ida_idaapi.BADADDR, ida_idaapi.BADADDR, -1
		# Common PS5 case: st_value already equals runtime VA inside PT_TLS.
		for idx, t in enumerate(tpls):
			start = t['start']
			end = t['end']
			if start <= raw < end:
				return raw, as_uint64(raw - start), idx
		# Fallback: raw may already be DTP offset.
		for idx, t in enumerate(tpls):
			memsz = t['memsz']
			if raw < memsz:
				return as_uint64(t['start'] + raw), raw, idx
		return ida_idaapi.BADADDR, ida_idaapi.BADADDR, -1

	def _prepare_tls_symbol_metadata(self):
		"""
		Annotate STT_TLS symbols with normalized metadata:
		  symbol.tls_abs_ea, symbol.tls_offset, symbol.tls_template_idx
		"""
		if not self.symbols:
			return False
		self._tls_templates = self._collect_pt_tls_templates()
		if not self._tls_templates:
			return False
		total = 0
		resolved = 0
		abs_to_off = 0
		for symbol in self.symbols:
			try:
				if not symbol.is_tls() or symbol.is_undef:
					continue
			except Exception:
				continue
			total += 1
			try:
				raw = as_uint64(symbol.entry.get('st_value', 0))
			except Exception:
				raw = 0
			abs_ea, tls_off, idx = self._resolve_tls_value(raw)
			symbol.tls_abs_ea = abs_ea
			symbol.tls_offset = tls_off
			symbol.tls_template_idx = idx
			if abs_ea not in (0, ida_idaapi.BADADDR) and tls_off not in (ida_idaapi.BADADDR,):
				resolved += 1
				if raw == abs_ea:
					abs_to_off += 1
		if total:
			print('TLS symbols: resolved=%d/%d (abs->off=%d).' % (resolved, total, abs_to_off))
		return True

	def _fixup_tls_template(self):
		"""
		Best-effort TLS annotations based on PT_TLS program headers.

		The Prospero linker scripts place:
		- .tdata into PT_TLS and also into the RELRO load
		- .tbss only into PT_TLS

		In practice many PS5 binaries have a tiny/empty TLS template, and some are malformed enough
		that IDA reports "Illegal total size of the TLS template". We keep this non-invasive:
		we only create labels and print a summary, without splitting segments.
		"""
		if not self.elf or not getattr(self.elf, 'phdrs', None):
			return False

		self._tls_templates = self._collect_pt_tls_templates()
		if not self._tls_templates:
			return False

		print('Fixing up TLS template (PT_TLS).')

		# Optional: create bytes/qwords for the initialized TLS image.
		# Keep default off: it can be noisy and doesn't help much unless you're specifically reversing TLS.
		if self.settings is None:
			self.settings = self._settings_load()
		create_items = bool((self.settings or {}).get('tls_items', False))

		changed = False
		for idx, t in enumerate(self._tls_templates):
			start = t['start']
			memsz = t['memsz']
			filesz = t['filesz']
			end = t['end']
			tdata_start = start
			tdata_end = start + filesz
			tbss_start = tdata_end
			tbss_end = end

			print('  PT_TLS #%d: vaddr=0x%x filesz=0x%x memsz=0x%x' % (idx, start, filesz, memsz))

			# Use unique-ish names if multiple TLS headers exist.
			suffix = '' if idx == 0 else ('_%d' % idx)
			set_name_unique(tdata_start, '__tls_start%s' % suffix, ida_name.SN_NOCHECK)
			set_name_unique(tbss_end, '__tls_end%s' % suffix, ida_name.SN_NOCHECK)

			if filesz:
				set_name_unique(tdata_start, '__tdata_start%s' % suffix, ida_name.SN_NOCHECK)
				set_name_unique(tdata_end, '__tdata_end%s' % suffix, ida_name.SN_NOCHECK)
			if tbss_end > tbss_start:
				set_name_unique(tbss_start, '__tbss_start%s' % suffix, ida_name.SN_NOCHECK)
				set_name_unique(tbss_end, '__tbss_end%s' % suffix, ida_name.SN_NOCHECK)

			if create_items and filesz:
				# Make the initialized TLS image visible as bytes (best effort).
				# We avoid forcing it if the range isn't mapped/loaded.
				for ea in range(tdata_start, tdata_end):
					try:
						if not ida_segment.getseg(ea):
							break
						if ida_bytes.is_loaded(ea):
							ida_bytes.create_byte(ea, 1, True)
					except Exception:
						break
				changed = True

		return changed

	def _fixup_relro_segments(self):
		"""
		Apply PT_GNU_RELRO semantics: memory ranges that become read-only after relocations.

		We do this after _fixup_relocations() to match runtime behavior.
		By default we keep GOT segments writable to avoid Hex-Rays treating them as constants too aggressively.
		"""
		if not self.elf or not getattr(self.elf, 'phdrs', None):
			return False

		relro_phdrs = []
		for phdr in self.elf.phdrs:
			try:
				if ElfUtil.phdr_type(phdr) == ElfUtil.PT_GNU_RELRO:
					relro_phdrs.append(phdr)
			except Exception:
				continue

		if not relro_phdrs:
			return False

		print('Fixing up GNU_RELRO segments.')

		# Optional strictness: include GOT-like segments in RELRO.
		# Default off to avoid Hex-Rays constant propagation hazards.
		if self.settings is None:
			self.settings = self._settings_load()
		relro_got = bool((self.settings or {}).get('relro_got', False))
		if relro_got:
			print('  Note: applying RELRO to GOT segments (settings: relro_got=1).')

		def is_got_seg(seg):
			if not seg:
				return False
			try:
				name = ida_segment.get_segm_name(seg) or ''
			except Exception:
				name = ''
			name_l = name.lower()
			return ('got' in name_l)

		def unique_seg_name(base, start_ea):
			base = str(base)
			if ida_segment.get_segm_by_name(base) is None:
				return base
			cand = '%s_%X' % (base, start_ea)
			if ida_segment.get_segm_by_name(cand) is None:
				return cand
			for i in range(1, 1000):
				cand = '%s_%X_%d' % (base, start_ea, i)
				if ida_segment.get_segm_by_name(cand) is None:
					return cand
			return '%s_%X_%d' % (base, start_ea, 1000)

		changed = False

		def split_at(ea):
			# Helper to keep splitting logic consistent and quiet.
			if not hasattr(ida_segment, 'split_segm'):
				return False
			try:
				return bool(ida_segment.split_segm(ea, ida_segment.SEGMOD_KEEP | ida_segment.SEGMOD_SILENT))
			except Exception:
				return False

		for idx, phdr in enumerate(relro_phdrs):
			start = as_uint64(phdr.get('p_vaddr', ida_idaapi.BADADDR))
			sz = as_uint64(phdr.get('p_memsz', 0))
			if start in (0, ida_idaapi.BADADDR) or sz in (0, ida_idaapi.BADADDR):
				continue
			end = start + sz
			if end <= start:
				continue

			print('  PT_GNU_RELRO #%d: [0x%x; 0x%x)' % (idx, start, end))

			ea = start
			while ea < end:
				seg = ida_segment.getseg(ea)
				if not seg:
					next_seg = ida_segment.get_next_seg(ea)
					if not next_seg or next_seg.start_ea >= end:
						break
					ea = next_seg.start_ea
					continue

				ovl_start = max(start, seg.start_ea)
				ovl_end = min(end, seg.end_ea)
				if ovl_end <= ovl_start:
					ea = ovl_end
					continue

				# Skip GOT-like segments by default.
				if is_got_seg(seg) and not relro_got:
					ea = ovl_end
					continue

				if (seg.perm & ida_segment.SEGPERM_WRITE) == 0:
					ea = ovl_end
					continue

				# Ensure we can isolate the RELRO-covered part by splitting (best effort).
				did_split = False
				if ovl_start > seg.start_ea and ovl_start < seg.end_ea:
					if split_at(ovl_start):
						did_split = True
						seg = ida_segment.getseg(ovl_start)
						if not seg:
							ea = ovl_end
							continue

				# Recompute overlap against the (possibly) split segment.
				ovl_start = max(start, seg.start_ea)
				ovl_end = min(end, seg.end_ea)
				if ovl_end <= ovl_start:
					ea = ovl_end
					continue

				if ovl_end < seg.end_ea:
					if split_at(ovl_end):
						did_split = True
						seg = ida_segment.getseg(ovl_start)
						if not seg:
							ea = ovl_end
							continue

				# Now seg should match the RELRO-covered region (or a close superset if splits failed).
				old = seg.perm
				seg.perm = (seg.perm | ida_segment.SEGPERM_READ) & ~ida_segment.SEGPERM_WRITE
				if seg.perm != old:
					print('    Updating segment %s perms (0x%x -> 0x%x).' % (ida_segment.get_segm_name(seg), old, seg.perm))
					ida_segment.update_segm(seg)
					changed = True

				if did_split:
					# Name the isolated RELRO part for readability, but don't fight existing meaningful names.
					try:
						old_name = ida_segment.get_segm_name(seg) or ''
					except Exception:
						old_name = ''
					if 'relro' not in old_name.lower():
						try:
							ida_segment.set_segm_name(seg, unique_seg_name('.relro', seg.start_ea))
						except Exception:
							pass

				# Other overlap patterns are rare; keep them as-is to avoid breaking segment layout.
				ea = ovl_end

		return changed

	def run(self, arg):
		# Invoked from Edit -> Plugins -> PS5 elf plugin: open settings dialog.
		self.show_settings_dialog()
		return True

def PLUGIN_ENTRY():
	return ps5_elf_plugin_t()
