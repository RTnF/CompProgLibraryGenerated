"""Inventory both imported C++ trees without modifying or executing their drivers.

This is a discovery/compile check, not a public verification gate. In particular,
including a template does not establish that all its members are instantiated.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from offline import disable_network
from check_public import FLAGS, check_compiler

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
from clang_ast import clang_command  # noqa: E402

TREES = (ROOT / "experiments/library/cpp", ROOT / "experiments/library3/cpp")
OUTPUT = ROOT / "docs/verification_inventory.json"
INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.MULTILINE)
NODE = re.compile(r"^([ |`-]*)(\w+) (?:0x[0-9a-f]+)(.*)$")
LOCATION = re.compile(r"(?:(/[^<> ,]+|[^<> ,]+\.(?:hpp|cpp|h)):(\d+):(\d+)|line:(\d+):(\d+))")
KINDS = {"FunctionDecl", "FunctionTemplateDecl", "CXXMethodDecl",
         "CXXConstructorDecl", "CXXDestructorDecl", "CXXConversionDecl",
         "CXXRecordDecl", "ClassTemplateDecl", "ClassTemplateSpecializationDecl",
         "TypeAliasDecl", "TypeAliasTemplateDecl", "TypedefDecl", "EnumDecl",
         "EnumConstantDecl", "VarDecl", "FieldDecl"}
FUNCTIONS = {"FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl",
             "CXXDestructorDecl", "CXXConversionDecl"}


def pending_status():
    return {"review": "pending", "bug": "unknown", "cpp_tested": False,
            "common_translator": False, "lean_proved": False,
            "include_verified": False, "published": False}


def relative(path):
    return path.relative_to(ROOT).as_posix()


def discover():
    return sorted(p for tree in TREES for p in tree.rglob("*")
                  if p.suffix in {".hpp", ".cpp"})


def series_root(path):
    return next(tree for tree in TREES if path.is_relative_to(tree))


def dependencies(path):
    result = []
    tree = series_root(path)
    for name in INCLUDE.findall(path.read_text()):
        candidates = [path.parent / name, tree / name]
        resolved = next((p.resolve() for p in candidates if p.is_file()), None)
        if resolved is None or not resolved.is_relative_to(ROOT):
            result.append({"include": name, "path": None})
        else:
            result.append({"include": name, "path": relative(resolved)})
    return result


def declarations(lines, source):
    """Read named source declarations from pinned Clang's text AST.

    Keep the complete declaration tail (including its type); overloads and
    private helpers remain separate. Implicit compiler declarations are omitted.
    Macro locations and template coverage still require manual review.
    """
    current_file = None
    current_line = None
    ancestors = []
    result = []
    for line in lines:
        match = NODE.match(line)
        if not match:
            continue
        prefix, kind, tail = match.groups()
        depth = len(prefix) // 2
        while ancestors and ancestors[-1][0] >= depth:
            ancestors.pop()
        # Only parse the location prefix, not strings/types in expressions.
        end = tail.find(">")
        location_text = tail[:end + 1] if end >= 0 else ""
        locations = list(LOCATION.finditer(location_text))
        owner, start_line = current_file, current_line
        for index, loc in enumerate(locations):
            filename, full_line, _, short_line, _ = loc.groups()
            if filename:
                current_file = (ROOT / filename).resolve()
            current_line = int(full_line or short_line)
            if index == 0:
                owner, start_line = current_file, current_line
        signature = tail[end + 1:].strip() if end >= 0 else tail.strip()
        # Clang prints the declaration's own location AFTER its range. It
        # resets the relative-location printer (the range end may be later).
        own_location = re.match(r"line:(\d+):\d+\s+", signature)
        if own_location:
            current_line = int(own_location.group(1))
            start_line = current_line
        signature = re.sub(r"^(?:(?:line:\d+:\d+|col:\d+)\s+)+", "", signature)
        signature = re.sub(r"0x[0-9a-f]+", "<ast-id>", signature)
        inside_function = any(k in FUNCTIONS for _, k in ancestors)
        if (owner == source and kind in KINDS
                and not re.search(r"\bimplicit\b(?!-inline)", signature)
                and not (kind == "VarDecl" and inside_function)):
            result.append({"kind": kind, "line": start_line,
                           "declaration": signature,
                           "template_instantiation_review": "pending",
                           "verification_target": None, "status": pending_status()})
        ancestors.append((depth, kind))
    return result


def run_capture(command, scratch):
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    diagnostics = completed.stderr.replace(str(ROOT) + "/", "")
    diagnostics = diagnostics.replace(str(scratch), "<scratch>")
    return {"status": "passed" if completed.returncode == 0 else "failed",
            "exit_code": completed.returncode, "diagnostics": diagnostics}


def preserve_reviews(data, previous):
    old_rows = {r["source"]: r for r in previous.get("files", [])}
    for row in data["files"]:
        old = old_rows.get(row["source"])
        if not old or old["source_sha256"] != row["source_sha256"]:
            continue
        for key in ("status", "verification_target", "evidence", "review_notes"):
            if key in old:
                row[key] = old[key]
        old_decls = {(d["kind"], d["line"], d["declaration"]): d
                     for d in old["declarations"]}
        for decl in row["declarations"]:
            prior = old_decls.get((decl["kind"], decl["line"], decl["declaration"]))
            if prior:
                for key in ("status", "verification_target", "evidence", "template_instantiation_review", "review_notes"):
                    if key in prior:
                        decl[key] = prior[key]


def validate_inventory(data):
    expected = {relative(p): p for p in discover()}
    rows = data["files"]
    actual = {r["source"] for r in rows}
    if len(actual) != len(rows) or actual != set(expected):
        raise RuntimeError(f"inventory coverage mismatch: {actual ^ set(expected)}")
    for row in rows:
        path = expected[row["source"]]
        if row["source_sha256"] != hashlib.sha256(path.read_bytes()).hexdigest():
            raise RuntimeError(f"stale inventory: {path}")
        if row["dependencies"] != dependencies(path):
            raise RuntimeError(f"stale dependencies: {path}")
        for item in [row, *row.get("declarations", [])]:
            for reference in [item.get("verification_target"), *item.get("evidence", [])]:
                if reference is None:
                    continue
                target = (ROOT / reference).resolve()
                if not target.is_relative_to(ROOT) or not target.is_file():
                    raise RuntimeError(f"missing inventory reference: {reference}")


def declaration_names(row):
    names = set()
    for decl in row["declarations"]:
        kind, signature = decl["kind"], decl["declaration"]
        if kind == "CXXRecordDecl":
            match = re.search(r"\b(?:struct|class|union)\s+(\S+)", signature)
            if match:
                names.add(match.group(1))
        elif kind in {"FunctionDecl", "FunctionTemplateDecl", "ClassTemplateDecl",
                      "TypeAliasDecl", "EnumDecl"}:
            before_type = signature.split(" '", 1)[0].split()
            if before_type:
                names.add(before_type[-1])
    return names


def update_duplicate_candidates(rows):
    names = {r["source"]: declaration_names(r) for r in rows}
    for row in rows:
        row["duplicate_candidates"] = [other["source"] for other in rows
                                       if other["source"] != row["source"]
                                       and names[row["source"]] & names[other["source"]]]
        row["byte_identical_sources"] = [other["source"] for other in rows
                                          if other["source"] != row["source"]
                                          and row.get("source_sha256") is not None
                                          and row["source_sha256"] == other.get("source_sha256")]


def build_inventory():
    check_compiler()
    clang = clang_command()
    paths = discover()
    rows = []
    with tempfile.TemporaryDirectory(prefix="import-inventory-") as directory:
        scratch = Path(directory)
        for index, path in enumerate(paths):
            tree = series_root(path)
            is_header = path.suffix == ".hpp"
            is_template = path.parent.name.lower() == "template"
            source = path
            if is_header:
                source = scratch / "include.cpp"
                template = tree / ("template/small_template.hpp" if tree == TREES[0]
                                   else "Template/SmallTemplate.hpp")
                includes = [template] if path == template else [template, path]
                source.write_text("".join(f'#include "{p}"\n' for p in includes))
            compile_result = run_capture(
                ["g++", *FLAGS, "-I", str(tree), "-fsyntax-only", str(source)], scratch)
            compile_result["mode"] = "syntax-only"
            declared = []
            ast_result = None
            if is_header or is_template:
                with (scratch / "ast.txt").open("w+") as dump:
                    process = subprocess.run(
                        clang + ["-I", str(tree), "-Xclang", "-ast-dump", str(path)],
                        cwd=ROOT, stdout=dump, stderr=subprocess.PIPE, text=True)
                    dump.seek(0)
                    declared = declarations(dump, path)
                ast_result = {"status": "passed" if process.returncode == 0 else "partial",
                              "diagnostics": process.stderr.replace(str(ROOT) + "/", "")}
            text = path.read_text()
            brief = re.search(r"@brief\s+([^\n]+)", text)
            row = {
                "source": relative(path),
                "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "series": relative(tree.parent),
                "kind": "template" if is_template else "header" if is_header else "driver",
                "purpose_hint": brief.group(1).strip() if brief else None,
                "dependencies": dependencies(path),
                "declarations": declared,
                "declaration_scan": ast_result,
                "compile": compile_result,
                "problem_url": (re.search(r'#define\s+PROBLEM\s+"([^"]+)"', text).group(1)
                                if re.search(r'#define\s+PROBLEM\s+"([^"]+)"', text) else None),
                "ignored_driver": bool(re.search(r"^\s*#define\s+IGNORE\b", text, re.MULTILINE)),
                "verification_target": None,
                "status": pending_status(),
            }
            rows.append(row)
            print(f"[{index + 1}/{len(paths)}] {row['source']}: {compile_result['status']}", flush=True)
    by_source = {r["source"]: r for r in rows}

    def reachable(name, visited=None):
        visited = set() if visited is None else visited
        if name in visited or name not in by_source:
            return visited
        visited.add(name)
        for dep in by_source[name]["dependencies"]:
            if dep["path"]:
                reachable(dep["path"], visited)
        return visited

    for row in rows:
        row["including_drivers"] = [d["source"] for d in rows if d["kind"] == "driver"
                                    and row["source"] in reachable(d["source"])]
    # Candidate only: same spelling never establishes semantic equivalence.
    update_duplicate_candidates(rows)
    return {"schema_version": 1, "scope": [relative(t) for t in TREES],
            "compiler": "GCC 13.3.0 / C++17", "ast": "Clang 22.1.4 text AST",
            "compile_flags": FLAGS,
            "network_policy": "Linux seccomp socket/connect/send denial inherited by subprocesses",
            "limitations": ["Syntax compilation does not prove runtime correctness or instantiate every template member.",
                            "Declaration extraction, macro ownership, API/purpose and duplicate candidates require manual review.",
                            "No imported driver is executed and no problem site is contacted."],
            "files": rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true",
                        help="check inventory file coverage, hashes and dependency references without compiling")
    parser.add_argument("--compile-drivers", action="store_true",
                        help="compile and link inventoried drivers/templates without executing them")
    parser.add_argument("--rescan-declarations", action="store_true",
                        help="refresh header/template declaration scans without recompiling drivers")
    parser.add_argument("--report", type=Path,
                        help="write results to this path instead of overwriting the repository inventory")
    args = parser.parse_args()
    report_path = args.report or OUTPUT
    disable_network()
    if args.check or args.compile_drivers or args.rescan_declarations:
        data = json.loads(OUTPUT.read_text())
        validate_inventory(data)
        rows = data["files"]
        if args.rescan_declarations:
            clang = clang_command()
            with tempfile.TemporaryDirectory(prefix="import-declarations-") as directory:
                scratch = Path(directory)
                for row in rows:
                    if row["kind"] == "driver":
                        continue
                    path = ROOT / row["source"]
                    previous = {"files": [json.loads(json.dumps(row))]}
                    with (scratch / "ast.txt").open("w+") as dump:
                        process = subprocess.run(
                            clang + ["-I", str(series_root(path)), "-Xclang", "-ast-dump", str(path)],
                            cwd=ROOT, stdout=dump, stderr=subprocess.PIPE, text=True)
                        dump.seek(0)
                        row["declarations"] = declarations(dump, path)
                    row["declaration_scan"] = {
                        "status": "passed" if process.returncode == 0 else "partial",
                        "diagnostics": process.stderr.replace(str(ROOT) + "/", "")}
                    preserve_reviews({"files": [row]}, previous)
                    print(f"{row['source']}: {len(row['declarations'])} declarations", flush=True)
            update_duplicate_candidates(rows)
            report_path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
        elif args.compile_drivers:
            check_compiler()
            with tempfile.TemporaryDirectory(prefix="import-link-") as directory:
                scratch = Path(directory)
                for row in rows:
                    path = ROOT / row["source"]
                    if path.suffix != ".cpp":
                        continue
                    row["compile"] = run_capture(
                        ["g++", *FLAGS, "-I", str(series_root(path)), str(path),
                         "-o", str(scratch / "driver")], scratch)
                    row["compile"]["mode"] = "compile-and-link"
                    print(f"{row['source']}: {row['compile']['status']}", flush=True)
            report_path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
        else:
            print(f"inventory coverage and source hashes passed: {len(rows)} files")
    else:
        data = build_inventory()
        if OUTPUT.exists():
            preserve_reviews(data, json.loads(OUTPUT.read_text()))
        report_path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
