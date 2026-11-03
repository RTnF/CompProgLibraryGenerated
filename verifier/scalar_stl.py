"""Checked contracts for scalar standard-library operations.

Compiler pointer-identity probes reject user-defined namesakes. Instantiation
patterns must belong to the pinned libstdc++ header, not user specializations.
"""

from pathlib import Path
from functools import lru_cache
import json
import subprocess
import tempfile

from clang_ast import clang_command, gcc_include_dirs, normalized, ROOT
from scalar_ir import source_ast, scalar_type


def walk(node):
    yield node
    for child in node.get("inner", []):
        yield from walk(child)


def direct_callee(node):
    children = node.get("inner", [])
    if node.get("kind") != "CallExpr" or len(children) != 3:
        return None
    callee = children[0]
    if callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "FunctionToPointerDecay":
        inner = callee.get("inner", [])
        if len(inner) == 1:
            callee = inner[0]
    if callee.get("kind") == "DeclRefExpr" and callee.get("referencedDecl", {}).get("kind") == "FunctionDecl":
        return callee
    return None


def standard_patterns(roots):
    headers = {(Path(directory)/"bits/move.h").resolve() for directory in gcc_include_dirs()}
    patterns = {}
    for root in roots:
        if root.get("name") != "swap" or root.get("kind") != "FunctionTemplateDecl":
            continue
        origin = root.get("loc",{}).get("file")
        if origin is None or Path(origin).resolve() not in headers:
            continue
        for child in root.get("inner",[]):
            if child.get("kind") != "FunctionDecl" or any(c.get("kind") == "TemplateArgument" for c in child.get("inner",[])):
                continue
            bodies = [c for c in child.get("inner",[]) if c.get("kind") == "CompoundStmt"]
            if len(bodies) == 1:
                patterns[child["id"]] = normalized(bodies[0])
    return patterns


@lru_cache(maxsize=1)
def pristine_bodies():
    with tempfile.TemporaryDirectory(prefix="scalar-swap-standard-") as directory:
        source = Path(directory)/"standard.cpp"
        source.write_text("#include <utility>\n")
        return list(standard_patterns(source_ast(source,"std::swap")).values())


def verify_scalar_swaps(source, nodes, include_dirs):
    source = Path(source).resolve()
    calls = []
    origins = {}
    for root in nodes:
        selected = [(node,direct_callee(node)) for node in walk(root)]
        selected = [(node,callee) for node,callee in selected
                    if callee is not None and callee["referencedDecl"].get("name") == "swap"]
        if selected:
            origin = root.get("loc",{}).get("file")
            if origin is None or not Path(origin).is_file():
                raise ValueError("scalar swap definitions require an explicit source file")
            for node, _ in selected:
                origins[id(node)] = Path(origin).resolve()
        calls.extend(selected)
    if not calls:
        return
    replacements, types = {}, set()
    for node, callee in calls:
        origin = origins[id(node)]
        text = origin.read_bytes()
        args = node["inner"][1:]
        ty = scalar_type(args[0])
        if scalar_type(args[1]) != ty:
            raise ValueError("scalar std::swap requires identical argument types")
        spelling = args[0]["type"].get("desugaredQualType", args[0]["type"]["qualType"])
        # Canonical builtin spelling, independently checked by scalar_type.
        if "const" in spelling.split():
            raise ValueError("scalar std::swap requires mutable arguments")
        types.add(spelling)
        begin, end = node["range"]["begin"], node["range"]["end"]
        cb, ce = callee["range"]["begin"], callee["range"]["end"]
        if any("offset" not in loc or "spellingLoc" in loc or "expansionLoc" in loc
               for loc in (begin,end,cb,ce)):
            raise ValueError("macro or indirect-source swap call locations are unsupported")
        if any("file" in loc and Path(loc["file"]).resolve() != origin for loc in (begin,end,cb,ce)):
            raise ValueError("scalar swap calls must belong to their definition's source file")
        start, stop = begin["offset"], end["offset"] + end["tokLen"]
        while stop < len(text) and text[stop:stop+1].isspace():
            stop += 1
        if stop >= len(text) or text[stop:stop+1] != b";":
            raise ValueError("std::swap must be a discarded standalone statement in the input source")
        name = text[cb["offset"]:ce["offset"]+ce["tokLen"]].decode()
        original = text[start:stop].decode()
        pointer = f"void (*)({spelling} &, {spelling} &)"
        assertion = (f"static_assert(static_cast<{pointer}>(&{name}) == "
                     f"static_cast<{pointer}>(&std::swap<{spelling}>), "
                     '"scalar swap must resolve to std::swap");')
        replacements.setdefault(origin, []).append((start,stop+1,("{"+assertion+original+";}").encode()))
    with tempfile.TemporaryDirectory(prefix="scalar-swap-probe-") as directory:
        mappings = []
        for index, (origin, edits) in enumerate(replacements.items()):
            probe = origin.read_bytes()
            previous = len(probe) + 1
            for start, stop, replacement in sorted(set(edits), reverse=True):
                if stop > previous:
                    raise ValueError("overlapping swap source locations")
                probe = probe[:start] + replacement + probe[stop:]
                previous = start
            path = Path(directory)/f"probe-{index}.hpp"
            path.write_bytes(probe)
            mappings.append({"type": "file", "name": str(origin), "external-contents": str(path)})
        overlay = Path(directory)/"overlay.json"
        # Compile the actual translation unit with only the selected call sites
        # instrumented. Virtual paths preserve relative includes, macros and
        # specializations from the caller, including calls in dependency headers.
        overlay.write_text(json.dumps({"version": 0, "use-external-names": False, "roots": mappings}))
        command = clang_command() + ["-ivfsoverlay", str(overlay)]
        for directory in include_dirs:
            command += ["-I",str(Path(directory).resolve())]
        result = subprocess.run(command+[str(source)],cwd=ROOT,capture_output=True,text=True)
        if result.returncode:
            raise ValueError("scalar swap callee identity probe failed: " + result.stderr)
    roots = source_ast(source,"std::swap",include_dirs)
    patterns = standard_patterns(roots)
    baseline = pristine_bodies()
    if not baseline or any(body not in baseline for body in patterns.values()):
        raise ValueError("scalar std::swap template body differs from the pristine pinned library")
    all_nodes = [node for root in roots for node in walk(root)]
    for spelling in types:
        instances = [n for n in all_nodes if n.get("kind") == "FunctionDecl" and n.get("name") == "swap"
                     and [c.get("type",{}).get("qualType") for c in n.get("inner",[])
                          if c.get("kind") == "TemplateArgument"] == [spelling]]
        if not instances or any(n.get("TemplateInstantiationPattern") not in patterns for n in instances):
            raise ValueError("scalar std::swap must use the pinned library template, not a user specialization")
    for node, _ in calls:
        node["verifiedScalarSwap"] = True
