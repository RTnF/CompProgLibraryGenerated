"""Content-addressed cache of successful checks.

A check is skipped when everything it read the last time it succeeded is unchanged. The dependencies of a Python check
are recorded automatically by `tools/trace/sitecustomize.py` (opened files, listed directories, file arguments of
subprocesses, loaded modules, the C++ headers those files include, and the whole Lean project when `lake` or `lean`
is run). Other commands give their dependencies explicitly. Only successes are cached, the cache lives in the untracked
`.cache/` directory, and `--no-cache` (or an absent `.cache/`, as in CI) runs everything.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
from process_supervisor import capture as supervised_capture

ROOT = Path(__file__).resolve().parents[1]
CACHE_FILE = ROOT / ".cache/check-results.json"
TRACE_DIR = ROOT / "tools/trace"
IGNORED = (".cache", ".lake", ".tools", ".git", "__pycache__", "benchmarks/local")
LEAN_TREE = ["Proofs.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "Proofs", "verification"]
INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.M)
enabled = True
_lock = threading.Lock()


def _ignored(path):
    relative = path.relative_to(ROOT).as_posix()
    return any(relative == name or relative.startswith(name + "/") or f"/{name}/" in f"/{relative}"
               for name in IGNORED)


def _files_under(path):
    if path.is_file():
        yield path
    elif path.is_dir():
        for item in sorted(path.rglob("*")):
            if item.is_file() and not _ignored(item):
                yield item


def cpp_closure(paths):
    """The given C++ files and every project file they include through quotes (transitively)."""
    seen, pending = set(), [Path(p).resolve() for p in paths]
    while pending:
        path = pending.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        if path.suffix not in (".hpp", ".h", ".cpp"):
            continue
        text = path.read_text(errors="replace")
        for name in INCLUDE.findall(text):
            for base in (path.parent, ROOT, ROOT / "library", ROOT / "experiments/library/cpp"):
                candidate = (base / name).resolve()
                if candidate.is_file():
                    pending.append(candidate)
                    break
    return sorted(seen)


def _environment():
    parts = [sys.version.split()[0]]
    for command in (["g++", "-dumpfullversion"],):
        try:
            parts.append(subprocess.check_output(command, text=True, stderr=subprocess.DEVNULL).strip())
        except (OSError, subprocess.CalledProcessError):
            parts.append("none")
    toolchain = ROOT / "lean-toolchain"
    parts.append(toolchain.read_text().strip() if toolchain.is_file() else "")
    return "|".join(parts)


def _import_listing(path, names):
    """The entries of an import-path directory that could be imported under a name the check actually imported."""
    if not path.is_dir():
        return b"missing"
    return "\n".join(sorted(child.name for child in path.iterdir()
                            if child.name.partition(".")[0] in names)).encode()


def fingerprint(files, directories=(), import_dirs=(), names=()):
    digest = hashlib.sha256()
    digest.update(_environment().encode())
    for path in sorted({Path(p).resolve() for p in files}):
        digest.update(b"F" + str(path.relative_to(ROOT)).encode())
        digest.update(hashlib.sha256(path.read_bytes()).digest() if path.is_file() else b"missing")
    for path in sorted({Path(p).resolve() for p in directories}):
        digest.update(b"D" + str(path.relative_to(ROOT)).encode())
        digest.update("\n".join(sorted(child.name for child in path.iterdir())).encode() if path.is_dir() else b"missing")
    names = set(names)
    for path in sorted({Path(p).resolve() for p in import_dirs}):
        digest.update(b"I" + str(path.relative_to(ROOT)).encode())
        digest.update(_import_listing(path, names))
    return digest.hexdigest()


def _load():
    with _lock:
        try:
            return json.loads(CACHE_FILE.read_text())
        except (OSError, ValueError):
            return {}


def _store(name, files, directories, digest, import_dirs=(), names=()):
    with _lock:
        _store_locked(name, files, directories, digest, import_dirs, names)


def _store_locked(name, files, directories, digest, import_dirs=(), names=()):
    try:
        cache = json.loads(CACHE_FILE.read_text())
    except (OSError, ValueError):
        cache = {}
    cache[name] = {"files": [str(Path(p).relative_to(ROOT)) for p in sorted({Path(p).resolve() for p in files})],
                   "directories": [str(Path(p).relative_to(ROOT)) for p in sorted({Path(p).resolve() for p in directories})],
                   "import_dirs": [str(Path(p).resolve().relative_to(ROOT)) for p in sorted({Path(p).resolve() for p in import_dirs})],
                   "names": sorted(set(names)),
                   "digest": digest}
    CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
    temporary = CACHE_FILE.with_suffix(".tmp")
    temporary.write_text(json.dumps(cache, indent=1, sort_keys=True) + "\n")
    os.replace(temporary, CACHE_FILE)


def _hit(name):
    entry = _load().get(name)
    if not enabled or not entry:
        return False
    files = [ROOT / p for p in entry["files"]]
    directories = [ROOT / p for p in entry["directories"]]
    try:
        import_dirs = [ROOT / p for p in entry.get("import_dirs", [])]
        return fingerprint(files, directories, import_dirs, entry.get("names", [])) == entry["digest"]
    except OSError:
        return False


LEAN_IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)", re.M)


def lean_module_files(modules):
    """The project source files of the given modules and, transitively, of the project modules they import."""
    seen, pending = set(), list(modules)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        path = ROOT / (name.replace(".", "/") + ".lean")
        if name == "Proofs":
            path = ROOT / "Proofs.lean"
        if not path.is_file():
            continue
        yield path
        for imported in LEAN_IMPORT.findall(path.read_text(errors="replace")):
            if imported == "Proofs" or imported.startswith("Proofs."):
                pending.append(imported)


def _expand_lean(files, directories, modules):
    for item in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        files.add(ROOT / item)
    if "Proofs" in modules:
        for item in LEAN_TREE:
            path = ROOT / item
            if path.is_dir():
                files.update(_files_under(path))
            elif path.is_file():
                files.add(path)
    else:
        files.update(lean_module_files(modules))


def _parse_trace(trace_path):
    files, directories = set(), set()
    import_dirs, names = set(), set()
    uses_lean = False
    modules = set()
    for line in Path(trace_path).read_text().splitlines():
        kind, _, value = line.partition(" ")
        if kind == "m":
            modules.add(value)
            continue
        if kind == "n":
            names.add(value)
            continue
        path = Path(value)
        try:
            path.relative_to(ROOT)
        except ValueError:
            continue
        if _ignored(path) and path.name not in ("lake", "lean"):
            continue
        if path.name in ("lake", "lean", "leanchecker") or ".tools/elan" in value:
            uses_lean = True
            continue
        if kind == "i":
            import_dirs.add(path)
        elif kind == "d":
            directories.add(path)
        elif path.is_file():
            files.add(path)
        elif path.is_dir() and kind == "a":
            directories.add(path)
    cpp = [p for p in files if p.suffix in (".cpp", ".hpp", ".h")]
    files.update(cpp_closure(cpp))
    if uses_lean or modules:
        _expand_lean(files, directories, modules)
    return files, directories, import_dirs, names


def run_traced(name, command, cwd=ROOT, extra_files=(), timeout=None, **kwargs):
    """Run a Python check unless an identical earlier run succeeded; its dependencies are traced automatically."""
    if _hit(name):
        print(f"(cached) {name}")
        return
    with tempfile.TemporaryDirectory(prefix="trace-") as directory:
        trace = Path(directory) / "trace.log"
        trace.write_text("")
        environment = os.environ.copy()
        environment["CHECK_TRACE_FILE"] = str(trace)
        environment["CHECK_TRACE_ROOT"] = str(ROOT)
        environment["PYTHONPATH"] = os.pathsep.join(filter(None, [str(TRACE_DIR), environment.get("PYTHONPATH")]))
        try:
            supervised_capture(command, cwd=cwd, env=environment, timeout=timeout,
                               text=True, **kwargs)
        except subprocess.CalledProcessError as error:
            # Checks run in parallel, so their output is shown only when one fails.
            sys.stderr.write((error.stdout or "") + (error.stderr or ""))
            raise
        files, directories, import_dirs, names = _parse_trace(trace)
    files.update(Path(p).resolve() for p in extra_files)
    files = {p for p in files if p.is_file()}
    _store(name, files, directories, fingerprint(files, directories, import_dirs, names), import_dirs, names)


def cached_call(name, files, function):
    """Call `function` unless an identical earlier call succeeded; its dependencies are given explicitly.

    `files` may contain directories, which stand for every file below them. Name the check so that the options that
    change its meaning (compiler flags, modes) are part of the name."""
    expanded = set()
    directories = set()
    for item in files:
        path = Path(item).resolve()
        if path.is_dir():
            expanded.update(_files_under(path))
            directories.add(path)
        else:
            expanded.add(path)
    if _hit(name):
        print(f"(cached) {name}")
        return
    function()
    _store(name, expanded, directories, fingerprint(expanded, directories))


def run_with_deps(name, command, files, cwd=ROOT, **kwargs):
    cached_call(name, files, lambda: subprocess.run(command, cwd=cwd, check=True, **kwargs))
