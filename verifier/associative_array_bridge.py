"""Check the reviewed C++ AST and emit its trusted Lean translation."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tomllib

from merge_sort_bridge import elan_binary, gcc_include_dirs, normalized


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "library/associative_array.hpp"
TEMPLATE = ROOT / "verifier/associative_array_model.lean.in"
OUTPUT = ROOT / "Proofs/Generated/AssociativeArray.lean"
AST_SHA256 = "a13e8ae708ff997e87742af9420139d82cad9c6302db25c9cefa8b9b4cec349a"
SOURCE_SHA256 = "05f51f13e2fa37efab5b23d1aac020ee63e0ac3dd474ef98b8121b29e96a9712"
CLANG_VERSION = "clang version 22.1.4"


def digest_ast() -> str:
    lean = subprocess.check_output([elan_binary(), "which", "lean"], text=True).strip()
    clang = str(Path(lean).with_name("clang"))
    version = subprocess.check_output([clang, "--version"], text=True).splitlines()[0]
    if not version.startswith(CLANG_VERSION):
        raise RuntimeError(f"expected {CLANG_VERSION}, found {version}")
    command = [clang, "-x", "c++", "-std=c++17", "-fsyntax-only"]
    for directory in gcc_include_dirs():
        command += ["-isystem", directory]
    trees = []
    for name, kind in (("AssociativeArray", "TypeAliasDecl"),
                       ("associative_array_set", "FunctionDecl"),
                       ("associative_array_get", "FunctionDecl")):
        ast_command = command + [
            "-Xclang", "-ast-dump=json",
            "-Xclang", f"-ast-dump-filter=cp::{name}", str(SOURCE),
        ]
        ast = json.loads(subprocess.check_output(ast_command, text=True, cwd=ROOT))
        if ast.get("kind") != kind or ast.get("name") != name:
            raise RuntimeError(f"expected one cp::{name} {kind} AST")
        trees.append(normalized(ast))
    encoded = json.dumps(trees, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    metadata = tomllib.loads((ROOT / "library/associative_array.toml").read_text())
    if metadata.get("reviewed_ast_sha256") != AST_SHA256:
        raise RuntimeError("metadata and reviewed AST hash differ")
    if hashlib.sha256(SOURCE.read_bytes()).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("C++ source changed; review the source-to-Lean mapping")
    digest = digest_ast()
    if digest != AST_SHA256:
        raise RuntimeError(f"C++ AST changed: {digest}; review the mapping")
    expected = TEMPLATE.read_text()
    if args.write:
        OUTPUT.write_text(expected)
    elif OUTPUT.read_text() != expected:
        raise RuntimeError("generated Lean model differs from the reviewed mapping")
    print(f"reviewed C++ AST and Lean model match: {digest}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
