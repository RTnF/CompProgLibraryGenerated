"""Recognize the pinned system assert expansion and its terminating failure call."""

from functools import lru_cache
from pathlib import Path
import tempfile

from scalar_ir import source_ast
from scalar_stl import walk


def direct_callee(node):
    children = node.get("inner", [])
    if node.get("kind") != "CallExpr" or not children:
        return None
    callee = children[0]
    if callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "FunctionToPointerDecay":
        inner = callee.get("inner", [])
        if len(inner) == 1:
            callee = inner[0]
    return callee if callee.get("kind") == "DeclRefExpr" else None


def signature(node):
    return (node.get("type"), node.get("storageClass"), node.get("mangledName"),
            [c.get("type") for c in node.get("inner", []) if c.get("kind") == "ParmVarDecl"])


@lru_cache(maxsize=1)
def standard_assert():
    with tempfile.TemporaryDirectory(prefix="scalar-assert-standard-") as directory:
        source = Path(directory) / "standard.cpp"
        source.write_text("#include <cassert>\n")
        nodes = source_ast(source, "__assert_fail")
    if len(nodes) != 1 or nodes[0].get("kind") != "FunctionDecl":
        raise ValueError("unsupported system assertion declaration")
    return Path(nodes[0]["loc"]["file"]).resolve(), signature(nodes[0])


def macro_origin(node, header):
    return all(Path(node.get("range", {}).get(end, {}).get("spellingLoc", {}).get("file", "")).resolve() == header
               for end in ("begin", "end"))


def verify_scalar_asserts(source, nodes, include_dirs=()):
    candidates = [node for root in nodes for node in walk(root)
                  if node.get("kind") == "ConditionalOperator" and len(node.get("inner", [])) == 3
                  and node["inner"][2].get("kind") == "CallExpr"
                  and (callee := direct_callee(node["inner"][2])) is not None
                  and callee.get("referencedDecl", {}).get("name") == "__assert_fail"]
    if not candidates:
        return
    header, expected = standard_assert()
    declarations = source_ast(source, "__assert_fail", include_dirs)
    if not declarations or any(n.get("kind") != "FunctionDecl"
            or Path(n.get("loc", {}).get("file", "")).resolve() != header
            or signature(n) != expected or any(c.get("kind") == "CompoundStmt" for c in n.get("inner", []))
            for n in declarations):
        raise ValueError("assert failure callee must be the pristine system declaration; redefinitions and shadows rejected")
    for node in candidates:
        condition, success, failure = node["inner"]
        callee = direct_callee(failure)
        value = success.get("inner", [])
        if (not macro_origin(node, header) or not macro_origin(callee, header)
                or success.get("kind") != "CXXFunctionalCastExpr" or success.get("castKind") != "ToVoid"
                or len(value) != 1 or value[0].get("kind") != "IntegerLiteral" or value[0].get("value") != "0"
                or condition.get("type", {}).get("qualType") != "bool"
                or len(failure.get("inner", [])) != 5
                or callee["referencedDecl"].get("type") != expected[0]):
            raise ValueError("unsupported or nonstandard assert macro expansion")
        node["verifiedScalarAssert"] = True
