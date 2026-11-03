"""Proof policy, raw dependency checks, and statement/definition integrity.

The checked-in policy and contract are review boundaries, not automatically
rewritten when a proof changes. Cache entries are local successful observations.
"""

from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def definition_digest(row):
    return digest({key: row[key] for key in ("kind", "module", "type", "levels", "unsafe")})


def load_policy(path):
    data = json.loads(path.read_text())
    if set(data) != {"schema_version", "axioms"} or data["schema_version"] != 1:
        raise ValueError("invalid axiom policy schema")
    entries = data["axioms"]
    if not isinstance(entries, list) or not entries:
        raise ValueError("axiom policy must be a nonempty list")
    names = set()
    for entry in entries:
        if (set(entry) != {"name", "definition_sha256", "reason"}
                or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", entry["name"])
                or not re.fullmatch(r"[a-f0-9]{64}", entry["definition_sha256"])
                or not isinstance(entry["reason"], str) or not entry["reason"].strip()
                or entry["name"] in names):
            raise ValueError("invalid or duplicate axiom policy entry")
        names.add(entry["name"])
    return entries


def load_contracts(path):
    """Reviewed contracts of the C++ standard library: axioms of a separate category (see docs/trust_policy.md)."""
    data = json.loads(path.read_text())
    if set(data) != {"schema_version", "contracts"} or data["schema_version"] != 1:
        raise ValueError("invalid STL contract schema")
    names = set()
    entries = []
    for entry in data["contracts"]:
        if (set(entry) != {"name", "definition_sha256", "clause", "reason"}
                or not re.fullmatch(r"Proofs(?:\.[A-Za-z_][A-Za-z_0-9]*)+", entry["name"])
                or not re.fullmatch(r"[a-f0-9]{64}", entry["definition_sha256"])
                or not all(isinstance(entry[key], str) and entry[key].strip() for key in ("clause", "reason"))
                or entry["name"] in names):
            raise ValueError("invalid or duplicate STL contract entry")
        names.add(entry["name"])
        entries.append(entry)
    return entries


def contract_dependents(contracts, rows):
    """The theorems of the project that depend on an STL contract: they are proved only under that contract."""
    names = {entry["name"] for entry in contracts}
    memo = {}

    def depends(name, active=()):
        if name in memo:
            return memo[name]
        if name in names:
            return True
        row = rows.get(name)
        result = False
        if row is not None and name not in active:
            result = any(depends(dep, active + (name,)) for dep in row["dependencies"])
        memo[name] = result
        return result

    import sys
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100000))
    return sorted(name for name, row in rows.items()
                  if row["kind"] == "theorem" and row["module"].startswith("Proofs") and name not in names
                  and depends(name))


def audit_axiom_definitions(entries, rows):
    for entry in entries:
        row = rows.get(entry["name"])
        if row is None or row["kind"] != "axiom" or definition_digest(row) != entry["definition_sha256"]:
            raise ValueError(f"allowed axiom definition differs from review: {entry['name']}")


def changed_axiom_entries(entries, rows, cached):
    """Select only changed policy entries or actual axiom definitions."""
    keys = {entry["name"]: digest({"policy": entry,
        "definition": definition_digest(rows[entry["name"]])
        if entry["name"] in rows else None}) for entry in entries}
    cached_keys = cached.get("keys", {}) if isinstance(cached, dict) else {}
    if not isinstance(cached_keys, dict):
        cached_keys = {}
    changed = [entry for entry in entries
               if cached_keys.get(entry["name"]) != keys[entry["name"]]]
    return changed, keys


def audit_dependencies(entries, rows):
    allowed = {entry["name"] for entry in entries}
    roots = [name for name, row in rows.items() if row["module"].startswith("Proofs")]
    pending = list(roots)
    visited = set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        if name not in rows:
            raise ValueError(f"missing dependency declaration: {name}")
        row = rows[name]
        if row.get("unsafe", False):
            raise ValueError(f"unsafe proof dependency: {name}")
        if row["kind"] == "axiom" and name not in allowed:
            raise ValueError(f"unpermitted axiom dependency: {name}")
        pending.extend(row["dependencies"])
    return len(visited)


def statement_contract(rows, roots):
    pending = list(roots)
    visited = {}
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        if name not in rows:
            raise ValueError(f"missing statement declaration: {name}")
        row = rows[name]
        # Proof bodies may change. The proposition and every computational
        # definition used to express it must match the reviewed contract.
        record = {key: row[key] for key in ("kind", "module", "type", "levels", "body", "unsafe")}
        visited[name] = digest(record)
        pending.extend(row["type_dependencies"] if row["kind"] == "theorem" else row["dependencies"])
    return {"schema_version": 1, "roots": sorted(roots), "declarations": dict(sorted(visited.items()))}


def audit_contract(contract, rows):
    if contract != statement_contract(rows, contract["roots"]):
        raise ValueError("reviewed theorem statement or its definition closure changed")


def lean_code(text):
    """Remove nested comments and strings before conservatively screening tokens."""
    output = []
    index = 0
    depth = 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1; index += 2
            elif text.startswith("-/", index):
                depth -= 1; index += 2
            else:
                index += 1
            continue
        if text.startswith("/-", index):
            depth = 1; index += 2; output.append(" "); continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end == -1 else end
            output.append(" "); continue
        if text[index] == '"':
            index += 1
            while index < len(text) and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            if index == len(text):
                raise ValueError("unterminated Lean string")
            index += 1; output.append(" "); continue
        output.append(text[index]); index += 1
    if depth:
        raise ValueError("unterminated Lean comment")
    return "".join(output)


def audit_source(path):
    code = lean_code(path.read_text())
    forbidden = {"sorry", "sorryAx", "native_decide", "axiom", "unsafe", "extern",
                 "implemented_by", "partial", "initialize", "builtin_initialize",
                 "run_elab", "run_tac", "run_meta", "run_cmd", "elab", "elab_rules",
                 "macro", "macro_rules", "syntax", "prelude"}
    if Path(path).resolve() == (ROOT / "Proofs/StlContracts.lean").resolve():
        # The only file that may declare axioms: each must be a registered STL contract (verification/stl_contracts.json).
        registered = {entry["name"] for entry in load_contracts(ROOT / "verification/stl_contracts.json")}
        declared = {"Proofs.StlContracts." + name for name in re.findall(r"\baxiom\s+([A-Za-z_][A-Za-z_0-9]*)", code)}
        if declared != registered:
            raise ValueError(f"axioms of {path} and registered STL contracts differ: {sorted(declared ^ registered)}")
        forbidden = forbidden - {"axiom"}
    found = forbidden & set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", code))
    if found or "skipKernelTC" in code or "#" in code:
        raise ValueError(f"forbidden proof source construct in {path}: {sorted(found)}")
    for line in code.splitlines():
        if re.match(r"\s*(?:public\s+|private\s+)?import\b", line):
            modules = re.sub(r"^\s*(?:public\s+|private\s+)?import\s+", "", line).split()
            for module in modules:
                if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", module):
                    raise ValueError(f"unsupported proof import syntax: {module}")
                if module != "Init" and not module.startswith(("Proofs.", "Init.", "Std.", "Mathlib.")):
                    raise ValueError(f"unreviewed proof import: {module}")


MATHLIB_FAMILY = ('Mathlib', 'Batteries', 'Aesop', 'Qq', 'Plausible', 'ProofWidgets', 'ImportGraph',
                  'LeanSearchClient', 'Cli')


def audit_mathlib_coverage(modules):
    """Mathlib is trusted after one audit per pinned version (tools/audit_mathlib.py).

    Every module of Mathlib and its packages that the proofs import (transitively) must be covered by a log
    entry for the pinned Mathlib revision and Lean toolchain; otherwise the audit has to be repeated first.
    """
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    used = sorted(m for m in modules if m.split(".")[0] in MATHLIB_FAMILY)
    if not used:
        return 0
    log_path = ROOT / "verification/mathlib_audit_log.json"
    entries = json.loads(log_path.read_text())["entries"] if log_path.is_file() else []
    for entry in reversed(entries):
        if (entry["mathlib_rev"] == mathlib["rev"] and entry["lean_toolchain"] == toolchain
                and entry["leanchecker"] == "passed" and entry["nanoda"] == "passed"):
            missing = sorted(set(used) - set(entry["covered_modules"]))
            if not missing:
                return len(used)
    raise ValueError("Mathlib at the pinned revision has not been audited for all imported modules; run "
                     f"tools/audit_mathlib.py (first uncovered modules: {sorted(set(used))[:5]})")
