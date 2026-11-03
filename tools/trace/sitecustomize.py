"""Record the repository files a check reads (loaded through PYTHONPATH by tools/check_cache.py).

The audit hook runs in every Python process of a check (children inherit the environment) and appends one line per
observation to the file named by CHECK_TRACE_FILE: `r <path>` for an opened file, `d <path>` for a listed directory
`i <path>` for a directory listed by the import system, `n <name>` for the top-level name of a loaded module and `a <path>` for a command-line argument of a subprocess that names an existing file or directory.
"""
import os
import re
import sys

_path = os.environ.get("CHECK_TRACE_FILE")
_root = os.environ.get("CHECK_TRACE_ROOT")
if _path and _root:
    _out = open(_path, "a", buffering=1)

    def _record(kind, value):
        try:
            if isinstance(value, bytes):
                value = os.fsdecode(value)
            if not isinstance(value, (str, os.PathLike)):
                return
            absolute = os.path.abspath(os.fspath(value))
            if absolute == _root or absolute.startswith(_root + os.sep):
                _out.write(f"{kind} {absolute}\n")
        except Exception:
            pass

    _IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)", re.M)
    _MODULE = re.compile(r"^Proofs(\.[A-Za-z_][A-Za-z_0-9]*)*$")

    def _modules_of(argument):
        """Record the project Lean modules a subprocess is told about: a module name, or the imports of a .lean file."""
        if _MODULE.match(argument):
            _out.write(f"m {argument}\n")
        elif argument.endswith(".lean") and os.path.isfile(argument):
            with open(argument, errors="replace") as handle:
                for name in _IMPORT.findall(handle.read()):
                    if name == "Proofs" or name.startswith("Proofs."):
                        _out.write(f"m {name}\n")

    def _lake_build(words):
        # `lake build` without a target builds the whole project.
        if words and os.path.basename(words[0]) == "lake" and "build" in words[1:] \
                and not any(_MODULE.match(w) for w in words[1:]):
            _out.write("m Proofs\n")

    def _hook(event, args):
        if event == "open":
            _record("r", args[0])
        elif event in ("os.listdir", "os.scandir"):
            if args and args[0] is not None:
                # The directory listings made by Python's import system do not depend on files that are never
                # imported: they are recorded separately and only the names of imported modules matter (`n` lines).
                caller = sys._getframe(1)
                if caller.f_code.co_filename.startswith("<frozen importlib"):
                    _record("i", args[0])
                else:
                    _record("d", args[0])
        elif event == "subprocess.Popen":
            try:
                words = [os.fsdecode(a) if isinstance(a, bytes) else str(a) for a in args[1]]
                for argument in words:
                    _record("a", argument)
                    if "=" in argument:
                        _record("a", argument.split("=", 1)[1])
                    _modules_of(argument)
                if args[2] is not None:
                    _record("a", args[2])
                _lake_build(words)
            except Exception:
                pass

    sys.addaudithook(_hook)

    import atexit

    def _modules():
        # A module whose bytecode is current is not re-read from source, so list the loaded sources explicitly.
        for module in list(sys.modules.values()):
            _record("r", getattr(module, "__file__", None))
        for name in list(sys.modules):
            if name and "\n" not in name and " " not in name:
                _out.write(f"n {name.partition('.')[0]}\n")

    atexit.register(_modules)
