"""Check the reviewed C++ AST and emit its trusted Lean translation."""

import argparse
import hashlib
import json
import subprocess
import sys
import tomllib

from clang_ast import ROOT, check_source_contract, filtered_ast, normalized


SOURCE = ROOT / "library/associative_array.hpp"
TEMPLATE = ROOT / "verifier/associative_array_model.lean.in"
OUTPUT = ROOT / "Proofs/Generated/AssociativeArray.lean"
AST_SHA256 = "a13e8ae708ff997e87742af9420139d82cad9c6302db25c9cefa8b9b4cec349a"
EXPECTED_SOURCE_SHA256 = "05f51f13e2fa37efab5b23d1aac020ee63e0ac3dd474ef98b8121b29e96a9712"
REVIEWED_DECLARATIONS = [
    ("AssociativeArray", "TypeAliasDecl"),
    ("associative_array_set", "FunctionDecl"),
    ("associative_array_get", "FunctionDecl"),
]


def digest_ast() -> str:
    trees = []
    for name, kind in REVIEWED_DECLARATIONS:
        ast = filtered_ast(SOURCE, name)
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
    if metadata.get("source_sha256") != EXPECTED_SOURCE_SHA256:
        raise RuntimeError("metadata and reviewed source digest differ")
    if sorted(metadata["public_declarations"]) != sorted(
        f"{kind}:{name}" for name, kind in REVIEWED_DECLARATIONS
    ):
        raise RuntimeError("public declarations require a source-to-Lean mapping review")
    if metadata.get("reviewed_ast_sha256") != AST_SHA256:
        raise RuntimeError("metadata and reviewed AST hash differ")
    check_source_contract(SOURCE, metadata)
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
