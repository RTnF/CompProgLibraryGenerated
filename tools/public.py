"""Validate public component metadata and generate ordered include checks."""

import argparse
from pathlib import Path
import re
import tomllib


ROOT = Path(__file__).resolve().parent.parent
PUBLIC = ROOT / "library"
TEMPLATE = "experiments/library/cpp/template/small_template.hpp"


def repo_file(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT) or not path.is_file():
        raise ValueError(f"missing or invalid repository file: {relative}")
    return path


def registry() -> dict[str, dict]:
    entries = {}
    for metadata in sorted(PUBLIC.glob("*.toml")):
        data = tomllib.loads(metadata.read_text())
        name = data.get("name")
        if not isinstance(name, str) or metadata.stem != name or name in entries:
            raise ValueError(f"invalid component name in {metadata}")
        if data.get("source") != f"{name}.hpp":
            raise ValueError(f"invalid source name for {name}")
        if data.get("standard") != "c++17":
            raise ValueError(f"unsupported C++ standard for {name}")
        if not isinstance(data.get("max_n"), int) or data["max_n"] < 0:
            raise ValueError(f"invalid maximum input length for {name}")
        digest = data.get("reviewed_ast_sha256")
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise ValueError(f"invalid reviewed AST digest for {name}")
        for field in ("proof", "model", "bridge", "benchmark"):
            if not isinstance(data.get(field), str):
                raise ValueError(f"missing {field} for {name}")
            repo_file(data[field])
        if not isinstance(data.get("tests"), list) or not data["tests"] or not all(
            isinstance(item, str) and item.endswith(".cpp") for item in data["tests"]
        ):
            raise ValueError(f"missing or invalid C++ tests for {name}")
        for test in data["tests"]:
            repo_file(test)
        if not isinstance(data.get("io_cases", []), list):
            raise ValueError(f"invalid I/O cases for {name}")
        for case in data.get("io_cases", []):
            if not isinstance(case, dict) or set(case) != {"source", "input", "expected"}:
                raise ValueError(f"invalid I/O case for {name}")
            for field in ("source", "input", "expected"):
                if not isinstance(case[field], str):
                    raise ValueError(f"invalid I/O {field} for {name}")
                repo_file(case[field])
            for field, directory in (("input", "in"), ("expected", "out")):
                path = Path(case[field])
                if path.parent != Path("tests/data") / directory or path.suffix != ".txt":
                    raise ValueError(f"I/O {field} must be tests/data/{directory}/*.txt for {name}")
            if not case["source"].endswith(".cpp"):
                raise ValueError(f"invalid I/O source for {name}")
        source_digest = data.get("source_sha256")
        if not isinstance(source_digest, str) or re.fullmatch(r"[0-9a-f]{64}", source_digest) is None:
            raise ValueError(f"invalid C++ source digest for {name}")
        declarations = data.get("public_declarations")
        if not isinstance(declarations, list) or not declarations or not all(
            isinstance(item, str) and re.fullmatch(r"[A-Za-z]+Decl:[A-Za-z_][A-Za-z_0-9]*", item)
            for item in declarations
        ) or len(declarations) != len(set(declarations)):
            raise ValueError(f"invalid public declarations for {name}")
        repo_file(f"library/{data['source']}")
        if not isinstance(data.get("dependencies"), list) or not all(
            isinstance(item, str) for item in data["dependencies"]
        ):
            raise ValueError(f"invalid dependencies for {name}")
        entries[name] = data

    allowed = {PUBLIC / "README.md"}
    for name in entries:
        allowed.add(PUBLIC / f"{name}.toml")
        allowed.add(PUBLIC / f"{name}.hpp")
    unexpected = sorted(path for path in PUBLIC.rglob("*") if path.is_file() and path not in allowed)
    if unexpected:
        raise ValueError(f"unregistered public files: {[str(path.relative_to(ROOT)) for path in unexpected]}")
    for name in entries:
        dependency_order(name, entries)
    expected_proofs = {data["proof"] for data in entries.values()}
    expected_models = {data["model"] for data in entries.values()}
    expected_bridges = {data["bridge"] for data in entries.values()}
    if len(expected_proofs) != len(entries) or len(expected_models) != len(entries):
        raise ValueError("proof and model paths must be unique per component")
    if len(expected_bridges) != len(entries):
        raise ValueError("bridge paths must be unique per component")
    actual_proofs = {f"Proofs/{path.name}" for path in (ROOT / "Proofs").glob("*.lean")}
    actual_models = {f"Proofs/Generated/{path.name}" for path in (ROOT / "Proofs/Generated").glob("*.lean")}
    if actual_proofs != expected_proofs or actual_models != expected_models:
        raise ValueError("Lean proof/model files and public registry differ")
    actual_bridges = {f"verifier/{path.name}" for path in (ROOT / "verifier").glob("*_bridge.py")}
    if actual_bridges != expected_bridges:
        raise ValueError("bridge files and public registry differ")
    expected_tests = {
        path for data in entries.values() for path in data["tests"]
    } | {
        case["source"] for data in entries.values() for case in data.get("io_cases", [])
    }
    actual_tests = {f"tests/{path.name}" for path in (ROOT / "tests").glob("*.cpp")}
    if actual_tests != expected_tests:
        raise ValueError("C++ test files and public registry differ")
    expected_cases = {
        case[field] for data in entries.values() for case in data.get("io_cases", [])
        for field in ("input", "expected")
    }
    actual_cases = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "tests/data").rglob("*") if path.is_file()
    }
    if actual_cases != expected_cases:
        raise ValueError("I/O case files and public registry differ")
    expected_imports = {
        "import " + data["proof"].removesuffix(".lean").replace("/", ".")
        for data in entries.values()
    }
    actual_imports = {
        line.strip() for line in repo_file("Proofs.lean").read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("--")
    }
    if actual_imports != expected_imports:
        raise ValueError("Proofs.lean imports and public registry differ")
    return entries


def dependency_order(name: str, entries: dict[str, dict]) -> list[str]:
    ordered = []
    active = set()
    visited = set()

    def visit(current: str) -> None:
        if current in active:
            raise ValueError(f"cyclic dependency at {current}")
        if current in visited:
            return
        if current not in entries:
            raise ValueError(f"unknown dependency: {current}")
        active.add(current)
        for dependency in entries[current]["dependencies"]:
            visit(dependency)
        active.remove(current)
        visited.add(current)
        ordered.append(current)

    visit(name)
    return ordered


def include_check(names: list[str], entries: dict[str, dict]) -> str:
    paths = [TEMPLATE]
    for name in names:
        for item in dependency_order(name, entries):
            source = f"library/{entries[item]['source']}"
            if source not in paths:
                paths.append(source)
    for path in paths:
        repo_file(path)
    return "\n".join(f'#include "{path}"' for path in paths) + "\nint main() {}\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--include-check", metavar="COMPONENT")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    entries = registry()
    if args.include_check:
        if args.output is None:
            parser.error("--include-check requires --output")
        args.output.write_text(include_check([args.include_check], entries))
        print(f"generated include check for {args.include_check}")
    else:
        print(f"validated {len(entries)} public component(s)")


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        raise SystemExit(str(error)) from error
