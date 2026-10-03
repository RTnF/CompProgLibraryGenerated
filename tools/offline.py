"""Run a command with socket creation disabled, including its descendants."""

import ctypes
import ctypes.util
import errno
import subprocess
import sys


def disable_network():
    library = ctypes.util.find_library("seccomp")
    if sys.platform != "linux" or library is None:
        raise RuntimeError("offline checks require Linux and libseccomp")
    seccomp = ctypes.CDLL(library)
    seccomp.seccomp_init.argtypes = [ctypes.c_uint32]
    seccomp.seccomp_init.restype = ctypes.c_void_p
    seccomp.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    seccomp.seccomp_syscall_resolve_name.restype = ctypes.c_int
    seccomp.seccomp_rule_add.argtypes = [ctypes.c_void_p, ctypes.c_uint32,
                                       ctypes.c_int, ctypes.c_uint]
    seccomp.seccomp_rule_add.restype = ctypes.c_int
    seccomp.seccomp_load.argtypes = [ctypes.c_void_p]
    seccomp.seccomp_load.restype = ctypes.c_int
    seccomp.seccomp_release.argtypes = [ctypes.c_void_p]
    context = seccomp.seccomp_init(0x7FFF0000)  # SCMP_ACT_ALLOW
    if not context:
        raise RuntimeError("cannot initialize network restrictions")
    try:
        # socketpair remains available for local process communication.
        # connect/send* also deny use of any inherited network socket.
        for name in (b"socket", b"connect", b"sendto", b"sendmsg", b"sendmmsg"):
            number = seccomp.seccomp_syscall_resolve_name(name)
            if number < 0:
                raise RuntimeError(f"unknown network syscall: {name!r}")
            result = seccomp.seccomp_rule_add(
                context, 0x00050000 | errno.EPERM, number, 0,
            )
            if result != 0:
                raise RuntimeError(f"cannot restrict {name!r}: {result}")
        result = seccomp.seccomp_load(context)
        if result != 0:
            raise RuntimeError(f"cannot load network restrictions: {result}")
    finally:
        seccomp.seccomp_release(context)


def main():
    command = sys.argv[1:]
    if not command:
        raise RuntimeError("usage: python3 tools/offline.py COMMAND [ARG ...]")
    disable_network()
    result = subprocess.run(command, close_fds=True)
    return result.returncode if result.returncode >= 0 else 128 - result.returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
