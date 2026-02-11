## IDA PS5 .elf plugin (c) 2021-2026 by flatz, drakmor

# Instructions
* Put all files into their corresponding directories by keeping this directory's structure.
* Use `64-bit IDA` and standard `ELF64 for x86-64 (Unknown) [elf64.dll]` when loading `.elf`/`.prx` file.
* Apply any kernel options that you use usually.
* If you see warning `Unsupported or unknown image type`, then press `Yes`, thus ignoring it.
* Wait till plugin complete its own work. I use many heuristics to locate a lot of useful information within .elf file, so please be patient.
* Ignore all possible warnings that may happen during processing. Some of structures are getting updates from one version of SDK to another, that may cause warnings as well until they will be fully supported.
* If you want to add new symbols or edit existing ones, then update file `cfg/ps5_symbols.txt` and `til/prospero.til` optionally.

# Notes
* If you use some cracked version of IDA and see annoying `__usercall` calling conventions that breaks code analysis when decompiling x64 functions, then it can be fixed by appending `idapro` to `DISABLE_USERCALL` list at `cfg/hexrays.cfg`. Another solution is modifying artificially broken `hexx64.dll` plugin by changing `idapro` string written there to `hexx64`, e.g.:
  `69 64 61 70 72 6F 00 00 72 73 70 00 72 62 70 00` -> `68 65 78 78 36 34 00 00 72 73 70 00 72 62 70 00`

# What's New

* Analysis pipeline was reworked into clearer pre/post stages with progress reporting and better stability on large PRX/EBOOT files.
* Segment recovery and layout fixups were improved for `.init/.fini`, `.plt`, `.got/.got.plt`, `.bss`, `.eh_frame`, `.eh_frame_hdr`, RELRO-related ranges, and extra split data/code ranges.
* Dynamic metadata handling was improved (mixed import/export library role tags, cleaner module/library parsing, less noisy duplicate version output).
* Import/export processing is more robust: better symbol descriptor handling, improved naming fallbacks, and safer export renaming behavior.
* Relocation processing was hardened:
  * safer xref creation (fewer bad `add_dref` scenarios),
  * improved JMPREL decoding/fallback behavior,
  * better GOT/GOTRW import pointer naming,
  * support for key TLS relocation kinds (`DTPMOD64`, `DTPOFF*`, `TPOFF*`) with comments/naming.
* Exception/unwind analysis was heavily improved:
  * better CIE/FDE diagnostics,
  * `.eh_frame_hdr`-guided FDE collection,
  * LSDA/`.gcc_except_table` recovery with optional comments.
* Function boundary refinement from unwind metadata is more reliable and configurable.
* TLS/RELRO handling was improved.
* Settings UX
    
# Known bugs
* Need to update some structures to reflect more fields that it may take.
* Need to parse exception handler sections properly because their format was changed since PS4. Could be useful to tweak function boundaries even more.

P.S. PRs with bug fixes and improvements are welcome.
