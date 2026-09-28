"""Validate public component metadata and assemble paste-ready source."""

import argparse
from pathlib import Path
import re
import tomllib


ROOT = Path(__file__).resolve().parent.parent
PUBLIC = ROOT / "library"
MARKER = "// Paste public library components here, after their dependencies."


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
        for field in ("proof", "model", "bridge", "test", "benchmark"):
            if not isinstance(data.get(field), str):
                raise ValueError(f"missing {field} for {name}")
            repo_file(data[field])
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


def assemble(name: str, entries: dict[str, dict]) -> str:
    template = repo_file("a.cpp").read_text()
    if template.count(MARKER) != 1:
        raise ValueError("a.cpp must contain exactly one paste marker")
    parts = [repo_file(f"library/{entries[item]['source']}").read_text() for item in dependency_order(name, entries)]
    return template.replace(MARKER, "\n".join(parts))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--assemble", metavar="COMPONENT")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    entries = registry()
    if args.assemble:
        if args.output is None:
            parser.error("--assemble requires --output")
        args.output.write_text(assemble(args.assemble, entries))
        print(f"assembled {args.assemble} with {len(dependency_order(args.assemble, entries))} component(s)")
    else:
        print(f"validated {len(entries)} public component(s)")


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        raise SystemExit(str(error)) from error
