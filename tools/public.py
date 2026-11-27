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


def support_registry() -> dict[str, list[str]]:
    data = tomllib.loads(repo_file("verifier/support.toml").read_text())
    suffixes = {"lean_modules": ".lean", "python_modules": ".py",
                "checks": ".py", "documents": ".md"}
    if set(data) != set(suffixes):
        raise ValueError("invalid verifier support manifest fields")
    for field, suffix in suffixes.items():
        paths = data[field]
        if (not isinstance(paths, list)
                or not all(isinstance(path, str) and path.endswith(suffix) for path in paths)
                or len(paths) != len(set(paths))):
            raise ValueError(f"invalid verifier support {field}")
        for path in paths:
            resolved = repo_file(path)
            if field == "lean_modules" and not any(
                    resolved.is_relative_to(ROOT / root) for root in ("Proofs/Math", "Proofs/Cpp")):
                raise ValueError("shared Lean support must be in Proofs/Math/ or Proofs/Cpp/")
    return data


def load_component(metadata: Path) -> dict:
    """Validate one component's metadata alone (no scan of the other components or of the directories)."""
    data = tomllib.loads(metadata.read_text())
    name = data.get("name")
    if not isinstance(name, str) or metadata.stem != name:
        raise ValueError(f"invalid component name in {metadata}")
    if data.get("source") != metadata.resolve().relative_to(PUBLIC.resolve()).with_suffix(".hpp").as_posix():
        raise ValueError(f"invalid source name for {name}")
    if data.get("standard") not in ("c++17", "c++20"):
        raise ValueError(f"unsupported C++ standard for {name}")
    translation = data.get("translation")
    if translation != "lean_model":
        raise ValueError(f"unsupported translation for {name}")
    namespace = data.get("lean_namespace")
    if (not isinstance(namespace, str) or not re.fullmatch(
            r"Proofs(?:\.[A-Za-z_][A-Za-z_0-9]*)+", namespace)
            or data.get("bridge") != "verifier/model_bridge.py"):
        raise ValueError(f"invalid common state generator configuration for {name}")
    check_lean_model(name, data)
    if "reviewed_ast_sha256" in data:
        raise ValueError(f"common translation must not select a reviewed AST fingerprint for {name}")
    if not isinstance(data.get("spec"), str) or not data["spec"].endswith(".md"):
        raise ValueError(f"missing common component specification for {name}")
    repo_file(data["spec"])
    for field in ("proof", "model", "bridge"):
        if not isinstance(data.get(field), str):
            raise ValueError(f"missing {field} for {name}")
        repo_file(data[field])
    if "benchmark" in data:
        if not isinstance(data.get("benchmark"), str):
            raise ValueError(f"missing benchmark for {name}")
        repo_file(data["benchmark"])
    if not isinstance(data.get("tests"), list) or not data["tests"] or not all(
        isinstance(item, str) and item.endswith(".cpp") for item in data["tests"]
    ):
        raise ValueError(f"missing or invalid C++ tests for {name}")
    for test in data["tests"]:
        repo_file(test)
    if not isinstance(data.get("sanitizers", False), bool):
        raise ValueError(f"invalid sanitizer configuration for {name}")
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
        isinstance(item, str) and (
            re.fullmatch(r"[A-Za-z]+Decl:(?:[A-Za-z_][A-Za-z_0-9]*|operator[-+*/%<>=!&|^~]+)(?:<[0-9A-Za-z_, <>:]+>)?", item)
            or (re.fullmatch(r"(?:FunctionDecl|TypeAliasDecl|TypeAliasTemplateDecl|VarDecl):[A-Za-z_][A-Za-z_0-9]*::[A-Za-z_][A-Za-z_0-9]*", item))
        )
        for item in declarations
    ) or len(declarations) != len(set(declarations)):
        raise ValueError(f"invalid public declarations for {name}")
    if "qualified_class" in data:
        raise ValueError(f"qualified_class is not a lean_model field: {name}")
    repo_file(f"library/{data['source']}")
    if not isinstance(data.get("dependencies"), list) or not all(
        isinstance(item, str) for item in data["dependencies"]
    ):
        raise ValueError(f"invalid dependencies for {name}")
    return data


def check_lean_model(name: str, data: dict) -> None:
    """The fields of a component translated by verifier/lean_translate.py (docs/translation.md)."""
    stem = "".join(part.capitalize() for part in name.split("_"))
    if data.get("lean_namespace") != f"Proofs.Cpp.{stem}":
        raise ValueError(f"lean_model components use the namespace Proofs.Cpp.{stem}: {name}")
    if data.get("model") != f"Proofs/Cpp/Gen/{stem}.lean" or data.get("proof") != f"Proofs/Cpp/{stem}.lean":
        raise ValueError(f"lean_model components use Proofs/Cpp/Gen/{stem}.lean and Proofs/Cpp/{stem}.lean: {name}")
    diff = data.get("diff")
    if not isinstance(diff, dict) or set(diff) - {"instances", "cases", "calls", "bindings", "packs", "lean_imports"} \
            or not {"instances", "cases"} <= set(diff):
        raise ValueError(f"missing differential test (diff.instances, diff.cases) for {name}")
    if "calls" in diff and (not isinstance(diff["calls"], list) or not diff["calls"]
            or not all(isinstance(call, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", call)
                       for call in diff["calls"]) or len(diff["calls"]) != len(set(diff["calls"]))):
        raise ValueError(f"invalid differential call selection for {name}")
    if "bindings" in diff and (not isinstance(diff["bindings"], list) or not diff["bindings"] or not all(
            isinstance(b, str) and re.fullmatch(r"[a-z_][a-z_0-9]*", b) for b in diff["bindings"])):
        raise ValueError(f"invalid differential bindings for {name}")
    # packs: a type parameter pack -> the C++ argument type lists of its differential commands
    if "packs" in diff and (not isinstance(diff["packs"], dict) or not diff["packs"] or not all(
            isinstance(k, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", k) and isinstance(v, list) and v
            and all(isinstance(t, list) and all(isinstance(x, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9: <>,]*", x)
                                                for x in t) for t in v)
            for k, v in diff["packs"].items())):
        raise ValueError(f"invalid differential packs for {name}")
    # lean_imports: hand-written Lean modules with the instances of the bound classes
    if "lean_imports" in diff and (not isinstance(diff["lean_imports"], list) or not diff["lean_imports"] or not all(
            isinstance(m, str) and re.fullmatch(r"Proofs(?:\.[A-Z][A-Za-z0-9]*)+", m)
            and repo_file(m.replace(".", "/") + ".lean").is_file() for m in diff["lean_imports"])):
        raise ValueError(f"invalid differential Lean imports for {name}")
    instances = diff["instances"]
    if not isinstance(instances, list) or not instances or not all(
            isinstance(item, dict) and all(isinstance(k, str) and isinstance(v, str) for k, v in item.items())
            for item in instances):
        raise ValueError(f"invalid differential test instances for {name}")
    cases = diff["cases"]
    if not isinstance(cases, str) or Path(cases).parent != Path("tests/diff") or not cases.endswith(".py"):
        raise ValueError(f"differential test cases must be a generator tests/diff/*.py for {name}")
    repo_file(cases)


def component(name: str) -> dict:
    if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name) is None:
        raise ValueError(f"invalid component name: {name}")
    matches = list(PUBLIC.rglob(f"{name}.toml"))
    if len(matches) != 1:
        raise ValueError(f"expected one metadata file for {name}, found {len(matches)}")
    return load_component(matches[0])


def registry() -> dict[str, dict]:
    support = support_registry()
    entries = {}
    for metadata in sorted(PUBLIC.rglob("*.toml")):
        data = load_component(metadata)
        if data["name"] in entries:
            raise ValueError(f"invalid component name in {metadata}")
        entries[data["name"]] = data

    allowed = {PUBLIC / "README.md"}
    for name in entries:
        allowed.add(PUBLIC / Path(entries[name]["source"]).with_suffix(".toml"))
        allowed.add(PUBLIC / entries[name]["source"])
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
    shared_proofs = set(support["lean_modules"])
    if shared_proofs & (expected_proofs | expected_models):
        raise ValueError("shared infrastructure must not be registered as a component proof/model")
    lean_files = {path.relative_to(ROOT).as_posix() for path in (ROOT / "Proofs").rglob("*.lean")}
    model_dirs = (Path("Proofs/Cpp/Gen"),)
    actual_models = {path for path in lean_files if Path(path).parent in model_dirs}
    actual_proofs = lean_files - actual_models
    shared_models = {path for path in shared_proofs if Path(path).parent in model_dirs}
    if actual_proofs != expected_proofs | (shared_proofs - shared_models) or actual_models != expected_models | shared_models:
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
    } | {"import " + path.removesuffix(".lean").replace("/", ".") for path in shared_proofs}
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
            if entries[current].get("standard", "c++17") == "c++17" and \
                    entries[dependency].get("standard", "c++17") == "c++20":
                raise ValueError(f"C++17 component {current} depends on C++20 component {dependency}")
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
