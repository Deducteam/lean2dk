#!/usr/bin/env python3
"""Set SG_READ_ONLY on the __DATA_CONST segment of a freshly-linked Mach-O.

Newer macOS dyld (Darwin 25.x+) refuses to load a binary whose __DATA_CONST
segment lacks the SG_READ_ONLY flag, aborting with:

    dyld: __DATA_CONST segment missing SG_READ_ONLY flag in <path>

The Lean v4.18 toolchain's linker leaves this flag clear, so locally-linked
executables (e.g. .lake/build/bin/lean2dk) won't launch on such systems. This
script patches the flag in post-build and ad-hoc re-signs the binary.

It is a deliberate no-op on non-macOS hosts and on inputs that are not thin
arm64/x86_64 Mach-O executables, so it is safe to wire into the build
unconditionally. It is also idempotent (skips files already patched).
"""
import platform
import struct
import subprocess
import sys

MH_MAGIC_64 = 0xFEEDFACF      # thin little-endian 64-bit Mach-O
LC_SEGMENT_64 = 0x19
SG_READ_ONLY = 0x10


def patch(path: str) -> None:
    if platform.system() != "Darwin":
        print(f"patch_macho: not macOS, skipping {path}")
        return

    with open(path, "rb") as f:
        data = bytearray(f.read())

    if len(data) < 32 or struct.unpack_from("<I", data, 0)[0] != MH_MAGIC_64:
        # not a thin 64-bit Mach-O (e.g. fat binary or ELF) -- nothing to do
        print(f"patch_macho: not a thin 64-bit Mach-O, skipping {path}")
        return

    ncmds = struct.unpack_from("<I", data, 16)[0]
    off = 32  # sizeof(mach_header_64)
    changed = False
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, off)
        if cmd == LC_SEGMENT_64:
            segname = data[off + 8: off + 24].split(b"\x00")[0].decode()
            if segname == "__DATA_CONST":
                flags_off = off + 68  # cmd,cmdsize,segname[16],4xu64,maxprot,initprot,nsects
                flags = struct.unpack_from("<I", data, flags_off)[0]
                if flags & SG_READ_ONLY:
                    print(f"patch_macho: __DATA_CONST already has SG_READ_ONLY in {path}")
                    return
                struct.pack_into("<I", data, flags_off, flags | SG_READ_ONLY)
                changed = True
                print(f"patch_macho: __DATA_CONST flags {flags:#x} -> {flags | SG_READ_ONLY:#x} in {path}")
        off += cmdsize

    if changed:
        with open(path, "wb") as f:
            f.write(data)
        # modifying the binary invalidates its code signature; re-sign ad-hoc
        subprocess.run(["codesign", "-f", "-s", "-", path], check=True)
        print(f"patch_macho: re-signed {path} ad-hoc")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: patch_macho.py <path-to-binary>")
    patch(sys.argv[1])
