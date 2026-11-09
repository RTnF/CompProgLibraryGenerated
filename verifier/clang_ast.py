"""Shared, pinned Clang AST checks for public C++ components."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parent.parent
CLANG_VERSION = "clang version 22.1.4"
GCC_VERSION = "13.3.0"
VOLATILE_KEYS = {"id", "loc", "range", "mangledName"}
PUBLIC_KINDS = {"FunctionDecl", "TypeAliasDecl", "TypeAliasTemplateDecl", "CXXRecordDecl", "EnumDecl", "VarDecl", "ClassTemplateDecl", "FunctionTemplateDecl",
                "ClassTemplateSpecializationDecl"}


def normalized(value):
    if isinstance(value, dict):
        return {
            key: normalized(item)
            for key, item in value.items()
            if key not in VOLATILE_KEYS and not key.endswith("Id")
        }
    if isinstance(value, list):
        return [normalized(item) for item in value]
    if isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]+", value):
        return "<ast-id>"
    return value


def elan_binary():
    local = ROOT / ".tools/elan/bin/elan"
    if local.is_file():
        os.environ["ELAN_HOME"] = str(ROOT / ".tools/elan")
        return str(local)
    found = shutil.which("elan")
    if found is None:
        raise RuntimeError("elan is required to find the pinned Clang toolchain")
    return found


def gcc_include_dirs():
    version = subprocess.check_output(["g++", "-dumpfullversion"], text=True).strip()
    if version != GCC_VERSION:
        raise RuntimeError(f"expected GCC {GCC_VERSION}, found {version}")
    result = subprocess.run(
        ["g++", "-E", "-x", "c++", "-", "-v"],
        input="", text=True, capture_output=True, check=True,
    )
    lines = result.stderr.splitlines()
    start = lines.index("#include <...> search starts here:") + 1
    end = lines.index("End of search list.")
    return [line.strip() for line in lines[start:end]]


def clang_command():
    lean = subprocess.check_output([elan_binary(), "which", "lean"], text=True).strip()
    clang = str(Path(lean).with_name("clang"))
    version = subprocess.check_output([clang, "--version"], text=True).splitlines()[0]
    if not version.startswith(CLANG_VERSION):
        raise RuntimeError(f"expected {CLANG_VERSION}, found {version}")
    command = [clang, "-x", "c++", "-std=c++17", "-fsyntax-only"]
    for include_dir in gcc_include_dirs():
        command += ["-isystem", include_dir]
    return command


def filtered_ast(source: Path, name: str):
    command = clang_command() + [
        "-Xclang", "-ast-dump=json", "-Xclang", f"-ast-dump-filter=cp::{name}",
        str(source),
    ]
    return json.loads(subprocess.check_output(command, text=True, cwd=ROOT))


def public_declarations(source: Path):
    command = clang_command() + [
        "-Xclang", "-ast-dump=json", "-Xclang", "-ast-dump-filter=cp::",
        str(source),
    ]
    output = subprocess.check_output(command, text=True, cwd=ROOT)
    decoder = json.JSONDecoder()
    position = 0
    declarations = []
    while position < len(output):
        ast, position = decoder.raw_decode(output, position)
        kind, name = ast.get("kind"), ast.get("name")
        if kind not in PUBLIC_KINDS or not name:
            raise RuntimeError(f"unsupported public declaration: {kind} {name}")
        if kind == "ClassTemplateDecl" and not any(c.get("kind") == "CXXRecordDecl" and c.get("completeDefinition")
                                                   for c in ast.get("inner", [])):
            # A forward declaration of a class template is not a second public declaration.
            while position < len(output) and output[position].isspace():
                position += 1
            continue
        if kind == "FunctionTemplateDecl" and not any(
                c.get("kind") == "FunctionDecl" and any(x.get("kind") == "CompoundStmt" for x in c.get("inner", []))
                for c in ast.get("inner", [])):
            while position < len(output) and output[position].isspace():
                position += 1
            continue
        if kind == "ClassTemplateSpecializationDecl":
            arguments = [str(c.get("value", c.get("type", {}).get("qualType", ""))) for c in ast.get("inner", [])
                         if c.get("kind") == "TemplateArgument"]
            name = f"{name}<{','.join(arguments)}>"
        if kind == "FunctionTemplateDecl":
            # Overloaded function templates are told apart by the class template of the first parameter
            # (`op<MonoidMul>`); a template without parameters keeps its plain name.
            functions = [c for c in ast.get("inner", []) if c.get("kind") == "FunctionDecl"]
            parameters = [c for c in functions[0].get("inner", []) if c.get("kind") == "ParmVarDecl"] if functions else []
            if parameters:
                spelling = re.sub(r"\bconst\b|&|\*|<.*>", "", parameters[0]["type"]["qualType"]).strip()
                spelling = re.sub(r"^.*::", "", spelling)
                name = f"{name}<{spelling}>"
        if kind in ("ClassTemplateDecl", "FunctionTemplateDecl") and f"{kind}:{name}" in declarations:
            # a redeclaration of a template (forward declaration before the definition)
            while position < len(output) and output[position].isspace():
                position += 1
            continue
        declarations.append(f"{kind}:{name}")
        while position < len(output) and output[position].isspace():
            position += 1
    if len(declarations) != len(set(declarations)):
        raise RuntimeError(f"duplicate or overloaded public declarations: {declarations}")
    return sorted(declarations)


def check_source_contract(source: Path, metadata: dict):
    actual_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    if actual_hash != metadata["source_sha256"]:
        raise RuntimeError(f"C++ source changed: {source}; review the entire header")
    actual_declarations = public_declarations(source)
    if actual_declarations != sorted(metadata["public_declarations"]):
        raise RuntimeError(
            f"public declarations changed in {source}: {actual_declarations}; "
            f"registered: {metadata['public_declarations']}"
        )
