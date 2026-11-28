"""Translate the restricted C++ subset of a public header into Lean functions in `Cpp.M`.

The rules are documented in docs/translation.md. The translation reads Clang's JSON AST of the
template definitions (not of their instantiations), so a class or function template over `T` becomes
a Lean definition over a type variable `T` whose required operations are instance arguments.

Anything outside the subset raises `Unsupported`; the translator never guesses.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import clang_ast  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


class Unsupported(Exception):
    pass


class RangeMutation(Unsupported):
    pass


# --------------------------------------------------------------------------------------------- types

@dataclass(frozen=True)
class Ty:
    kind: str                 # int, u32, u64, bool, tparam, vec, pair, cls, void
    name: str = ""            # tparam/cls name
    args: tuple = ()          # vec: (elem,), pair: (a, b), cls: template arguments
    width: int = field(default=64, compare=False)   # int: the C++ width (32, 64, 128); not part of the Lean type
    # vec of a fixed-size C array member `T a[N]`: the length N (a vparam/vlit Ty); not part of the Lean type
    length: object = field(default=None, compare=False)

    def __str__(self):
        return lean_type(self)


INT = Ty("int")
INT32 = Ty("int", width=32)
U32 = Ty("u32")
U64 = Ty("u64")
BOOL = Ty("bool")
ORDERING = Ty("ordering")
ISTREAM = Ty("istream")
OSTREAM = Ty("ostream")
VOID = Ty("void")

# Signed integers are mathematical integers (Int) under the stated precondition; the width only decides the
# usual arithmetic conversions with unsigned operands. Unsigned 32/64 bit integers wrap around (UInt32/UInt64).
SIGNED_WIDTHS = {
    "int": 32, "short": 32, "signed char": 32, "char": 32, "short int": 32, "std::int32_t": 32, "int32_t": 32,
    "long": 64, "long long": 64, "long int": 64, "long long int": 64, "difference_type": 64, "std::int64_t": 64,
    "int64_t": 64, "ll": 64, "size_type": 64, "wchar_t": 32, "__int128": 128, "__int128_t": 128,
    # Unsigned 128-bit values use mathematical integers without intermediate
    # wrapping. The fused mixed-remainder contract accepts their full range.
    "unsigned __int128": 128, "__uint128_t": 128,
}
INTEGER_NAMES = set(SIGNED_WIDTHS)
UNSIGNED_NAMES = {
    "unsigned": U32, "unsigned int": U32, "std::uint32_t": U32, "uint32_t": U32,
    "char32_t": U32,
    "unsigned long": U64, "unsigned long long": U64, "long unsigned int": U64, "long long unsigned int": U64,
    "size_t": U64, "std::size_t": U64, "std::uint64_t": U64, "uint64_t": U64, "ull": U64,
}


def split_args(text: str) -> list[str]:
    parts, depth, current = [], 0, ""
    for ch in text:
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current.strip())
    return parts


def product_value_element(ty: Ty) -> bool:
    if ty.kind == "vec" and ty.length is None:
        ty = ty.args[0]
    return ty.kind in ("int", "u32", "u64", "bool", "tparam")


def parse_type(text: str, tparams: set[str], classes, value_params=None, aliases=None) -> Ty:
    value_params = value_params or {}
    s = text.strip()
    s = re.sub(r"\bconst\b|\bvolatile\b|\btypename\b|\bstruct\b|\bclass\b", " ", s)
    s = s.replace("&", " ").strip()
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"^cp::", "", s)
    if s not in tparams and aliases and s in aliases:
        return aliases[s]
    if s in SIGNED_WIDTHS:
        return Ty("int", width=SIGNED_WIDTHS[s])
    if s in UNSIGNED_NAMES:
        return UNSIGNED_NAMES[s]
    if s in ("unsigned char", "unsigned short", "unsigned short int"):
        raise Unsupported(f"type {text!r}")
    if s == "bool":
        return BOOL
    if s in ("std::strong_ordering", "strong_ordering"):
        return ORDERING
    if s == "void":
        return VOID
    if s in ("std::string", "std::basic_string<char>", "std::__cxx11::basic_string<char>"):
        return Ty("string", args=(INT32,))
    if s in ("std::istream", "istream"):
        return ISTREAM
    if s in ("std::ostream", "ostream"):
        return OSTREAM
    if s in tparams:
        return Ty("tparam", s)
    m = re.fullmatch(r"std::deque<(.*)>", s)
    if m:
        args = split_args(m.group(1))
        if len(args) != 1:
            raise Unsupported("deque requires the default allocator")
        return Ty("deque", args=(parse_type(args[0], tparams, classes, value_params, aliases),))
    m = re.fullmatch(r"std::optional<(.*)>", s)
    if m:
        args = split_args(text[text.index("<") + 1:text.rindex(">")])
        if len(args) != 1 or "&" in args[0]:
            raise Unsupported("optional requires one value type")
        item = parse_type(args[0], tparams, classes, value_params, aliases)
        if item.kind not in ("int", "u32", "u64", "bool", "tparam"):
            raise Unsupported("optional requires a scalar value type")
        return Ty("optional", args=(item,))
    m = re.fullmatch(r"std::set<(.*)>", s)
    if m:
        args = split_args(m.group(1))
        if len(args) != 1:
            raise Unsupported("set requires the default comparator and allocator")
        elem = parse_type(args[0], tparams, classes, value_params, aliases)
        if elem.kind not in ("int", "u32", "u64", "tparam"):
            raise Unsupported("set requires ordered scalar elements")
        return Ty("ordered_set", "less", (elem,))
    m = re.fullmatch(r"std::(priority_queue|stack|queue)<(.*)>", s)
    if m:
        args = split_args(m.group(2))
        elem = parse_type(args[0], tparams, classes, value_params, aliases)
        if m.group(1) in ("stack", "queue"):
            if len(args) != 1:
                raise Unsupported(f"type {text!r}")
            if m.group(1) == "queue" and elem.kind not in ("int", "u32", "u64", "bool", "tparam"):
                raise Unsupported("queue requires scalar elements")
            return Ty(m.group(1), args=(elem,))
        order = "less"
        if len(args) >= 2 and re.sub(r"\s", "", args[1]) not in (f"std::vector<{re.sub(r'[ ]', '', args[0])}>",):
            if parse_type(args[1], tparams, classes, value_params, aliases) != Ty("vec", args=(elem,)):
                raise Unsupported("priority_queue container other than std::vector")
        if len(args) == 3:
            cmp = re.fullmatch(r"std::(greater|less)<(.*)>", re.sub(r"\s+", " ", args[2]).strip())
            if not cmp or parse_type(cmp.group(2), tparams, classes, value_params, aliases) != elem:
                raise Unsupported("priority_queue comparison other than std::less / std::greater")
            order = cmp.group(1)
        elif len(args) > 3:
            raise Unsupported(f"type {text!r}")
        return Ty("pq", order, (elem,))
    m = re.fullmatch(r"std::unordered_map<(.*)>", s)
    if m:
        args = split_args(m.group(1))
        if len(args) != 2:
            raise Unsupported(f"type {text!r}")
        key = parse_type(args[0], tparams, classes, value_params, aliases)
        if key.kind != "int":
            raise Unsupported("unordered_map key other than a signed integer")
        return Ty("umap", args=(key, parse_type(args[1], tparams, classes, value_params, aliases)))
    # `T (&)[n]` (a reference to an array, e.g. the row returned by operator[]): the array value.
    s = re.sub(r"\s*\(\s*\)\s*(?=\[)", "", s)
    m = re.fullmatch(r"([^\[\]]+?)\s*((?:\[[^\[\]]+\])+)", s)
    if m:
        # A fixed-size C array `T[a][b]` (a member of a class): nested Arrays of the given lengths.
        ty = parse_type(m.group(1), tparams, classes, value_params, aliases)
        for dim in reversed(re.findall(r"\[([^\[\]]+)\]", m.group(2))):
            dim = dim.strip()
            length = (Ty("vparam", dim, (value_params[dim],)) if dim in value_params
                      else parse_value_arg(dim, INT, value_params))
            ty = Ty("vec", args=(ty,), length=length)
        return ty
    m = re.fullmatch(r"(?:std::)?vector<(.*)>", s)
    if m:
        args = split_args(m.group(1))
        return Ty("vec", args=(parse_type(args[0], tparams, classes, value_params, aliases),))
    m = re.fullmatch(r"(?:std::)?pair<(.*)>", s)
    if m:
        a, b = split_args(m.group(1))
        return Ty("pair", args=(parse_type(a, tparams, classes, value_params, aliases), parse_type(b, tparams, classes, value_params, aliases)))
    m = re.fullmatch(r"std::tuple<(.*)>", s)
    if m:
        args = split_args(text[text.index("<") + 1:text.rindex(">")])
        if len(args) < 2 or any("&" in arg for arg in args):
            raise Unsupported("tuple requires at least two value elements")
        items = tuple(parse_type(arg, tparams, classes, value_params, aliases) for arg in args)
        if not all(product_value_element(item) for item in items):
            raise Unsupported("tuple requires scalar or scalar-vector elements")
        return Ty("tuple", args=items)
    m = re.fullmatch(r"([A-Za-z_][A-Za-z_0-9]*)(?:<(.*)>)?", s)
    if m and m.group(1) in classes:
        raw_args = split_args(m.group(2)) if m.group(2) else []
        info = classes.get(m.group(1)) if isinstance(classes, dict) else None
        if info is not None:
            extra = raw_args[len(info.tparams):]
            if (len(raw_args) < len(info.tparams) or len(extra) > len(info.constraints)
                    or any(a not in ("nullptr", f"value-parameter-0-{len(info.tparams) + i}")
                           for i, a in enumerate(extra))):
                raise Unsupported(f"template argument count or constraint argument of {s}")
            raw_args = raw_args[:len(info.tparams)]
        args = []
        for i, arg in enumerate(raw_args):
            expected = info.value_params.get(info.tparams[i]) if info is not None else None
            if expected is None:
                args.append(parse_type(arg, tparams, classes, value_params, aliases))
            else:
                args.append(parse_value_arg(arg, expected, value_params))
        return Ty("cls", m.group(1), tuple(args))
    raise Unsupported(f"type {text!r}")


def parse_value_arg(text, expected, values):
    if text in values:
        if values[text] != expected or values[text].width != expected.width:
            raise Unsupported(f"non-type template argument conversion {text}")
        return Ty("vparam", text, (expected,))
    if expected.kind == "bool" and text in ("true", "false", "0", "1"):
        return Ty("vlit", "true" if text in ("true", "1") else "false", (BOOL,))
    match = re.fullmatch(r"(-?\d+)([uUlL]*)", text)
    if match and expected.kind in ("int", "u32", "u64"):
        n = int(match.group(1))
        width = 32 if expected.kind == "u32" else 64 if expected.kind == "u64" else expected.width
        lower, upper = (0, 2**width) if expected.kind != "int" else (-2**(width-1), 2**(width-1))
        if lower <= n < upper:
            return Ty("vlit", str(n), (expected,))
    raise Unsupported(f"non-type template argument {text!r}")


def known_type_traits(cpp):
    canonical = " ".join(re.sub(r"\bconst\b|\bvolatile\b", "", cpp).split())
    if canonical in ("__int128", "__int128_t"):
        return False, True
    if canonical in ("unsigned __int128", "__uint128_t"):
        return False, False
    if canonical in ("bool", "unsigned char", "unsigned short", "unsigned short int", "char16_t") or canonical in UNSIGNED_NAMES:
        return False, False
    if canonical in SIGNED_WIDTHS:
        return True, False
    raise Unsupported(f"type traits require a known integral C++ type: {cpp}")


def constraint_binder(requirement):
    return "cppConstraint_" + hashlib.sha256(requirement.encode()).hexdigest()[:16]


def mod_to_uint32_binding(cpp, tag):
    canonical = " ".join(re.sub(r"\bconst\b|\bvolatile\b", "", cpp).split())
    known_type_traits(canonical)
    if canonical in ("unsigned char", "unsigned short", "unsigned short int", "char16_t"):
        return f'(Cpp.intModToUInt32 "{tag}" true)'
    ty = parse_type(canonical, set(), set())
    if ty.kind in ("bool", "u32", "u64"):
        return f'(inferInstance : Cpp.ModToUInt32 "{tag}" {lean_type(ty)})'
    if ty.kind == "int":
        return f'(Cpp.intModToUInt32 "{tag}" {str(ty.width <= 32).lower()})'
    raise Unsupported(f"integral remainder binding {cpp}")


SOURCE_STREAM_TYPES = {
    'int': ('int', INT32), 'long': ('long', INT), 'long int': ('long', INT),
    'long long': ('long_long', INT), 'long long int': ('long_long', INT),
    'unsigned int': ('unsigned_int', U32), 'unsigned': ('unsigned_int', U32),
    'unsigned long': ('unsigned_long', U64), 'long unsigned int': ('unsigned_long', U64),
    'unsigned long long': ('unsigned_long_long', U64),
    'long long unsigned int': ('unsigned_long_long', U64),
}


def source_stream_type(node):
    source = strip(node).get('type', {})
    spelling = source.get('desugaredQualType', source.get('qualType', ''))
    spelling = ' '.join(re.sub(r'\bconst\b|\bvolatile\b', '', spelling).split())
    if spelling not in SOURCE_STREAM_TYPES:
        raise Unsupported(f'concrete stream source-type contract: {spelling}')
    return SOURCE_STREAM_TYPES[spelling]


def return_type_text(fn_type: str) -> str:
    """The return type in a function type `R (params)`. `T (&(int))[n]` (a function returning a reference to an array
    `T[n]`) gives `T[n]`."""
    array_ret = re.fullmatch(r"(.*?)\(\s*&\s*\(.*\)\s*(?:const)?\s*\)\s*((?:\[[^\[\]]+\])+)", fn_type)
    if array_ret:
        return array_ret.group(1).strip() + array_ret.group(2)
    return fn_type.split("(")[0].strip()


def container_text(text: str, containers) -> str:
    """`T::value_type` → `T_value_type` and `T` → `std::vector<T_value_type>` for a container parameter `T`."""
    for t in containers:
        text = re.sub(rf"(?:typename\s+)?\b{t}::value_type\b", f"{t}_value_type", text)
        text = re.sub(rf"\b{t}\b(?!_value_type)", f"std::vector<{t}_value_type>", text)
    return text


def lean_type(ty: Ty) -> str:
    if ty.kind == "int":
        return "Int"
    if ty.kind == "u32":
        return "UInt32"
    if ty.kind == "u64":
        return "UInt64"
    if ty.kind == "bool":
        return "Bool"
    if ty.kind == "ordering":
        return "Ordering"
    if ty.kind == "void":
        return "Unit"
    if ty.kind == "istream":
        return "Cpp.IStream"
    if ty.kind == "ostream":
        return "Cpp.OStream"
    if ty.kind == "tparam":
        return ty.name
    if ty.kind == "field_value":
        return f'(Cpp.ReadField.Value (member := "{ty.name}") (Record := {lean_type(ty.args[0])}))'
    if ty.kind in ("add_result", "mul_result", "conditional_result"):
        cls = {"add_result": "AddResult", "mul_result": "MulResult",
               "conditional_result": "ConditionalResult"}[ty.kind]
        left, right = (lean_type(a) for a in ty.args)
        return f"(Cpp.{cls}.Value (Left := {left}) (Right := {right}))"
    if ty.kind == "vparam":
        return lean_name(ty.name)
    if ty.kind == "vlit":
        return f"({ty.name} : {lean_type(ty.args[0])})"
    if ty.kind in ("vec", "deque", "string", "constant_array"):
        return f"(Array {lean_type(ty.args[0])})"
    if ty.kind == "pair":
        return f"({lean_type(ty.args[0])} × {lean_type(ty.args[1])})"
    if ty.kind == "tuple":
        return "(" + " × ".join(lean_type(arg) for arg in ty.args) + ")"
    if ty.kind == "cstate":
        return f"(Cpp.ConstructState.State {lean_type(ty.args[0])})"
    if ty.kind == "pq":
        return f"(Cpp.PQ {lean_type(ty.args[0])})"
    if ty.kind == "stack":
        return f"(Cpp.Stack {lean_type(ty.args[0])})"
    if ty.kind == "queue":
        return f"(Cpp.Queue {lean_type(ty.args[0])})"
    if ty.kind == "optional":
        return f"(Option {lean_type(ty.args[0])})"
    if ty.kind == "ordered_set":
        return f"(Cpp.OrderedSet {lean_type(ty.args[0])})"
    if ty.kind == "umap":
        return f"(Cpp.UMap {lean_type(ty.args[0])} {lean_type(ty.args[1])})"
    if ty.kind == "cls":
        if ty.args:
            return "(" + " ".join(["cp." + ty.name] + [lean_type(a) for a in ty.args]) + ")"
        return "cp." + ty.name
    raise Unsupported(f"type {ty}")


def tparams_of(ty: Ty) -> set[str]:
    if ty.kind in ("tparam", "vparam"):
        return {ty.name}
    out = set()
    for a in ty.args:
        out |= tparams_of(a)
    return out


LEAN_KEYWORDS = {
    "end", "fun", "at", "from", "have", "show", "by", "do", "then", "else", "if", "match", "with", "let", "in",
    "open", "def", "theorem", "where", "structure", "class", "instance", "for", "return", "mut", "break",
    "continue", "unless", "namespace", "section", "variable", "universe", "example", "abbrev", "inductive",
    "deriving", "calc", "λ", "Type", "Prop", "Sort", "self", "default", "pure", "tick", "size", "get", "set",
    "range", "failure", "true", "false", "not", "and", "or", "max", "min", "id", "this", "prefix", "suffix",
    "to", "import", "export", "local", "private", "protected", "noncomputable", "mutual", "notation", "attribute",
    "try", "catch", "finally", "nomatch", "nofun", "termination_by", "decreasing_by", "omit", "include", "opaque",
    "set_option", "fuel", "check", "forever",
    # identifiers that the proof source screening (tools/proof_security.py) rejects
    "sorry", "sorryAx", "native_decide", "axiom", "unsafe", "extern", "implemented_by", "partial", "initialize",
    "builtin_initialize", "run_elab", "run_tac", "run_meta", "run_cmd", "elab", "elab_rules", "macro", "macro_rules",
    "syntax", "prelude",
}


OPERATOR_NAMES = {"++": "op_inc", "--": "op_dec", "==": "op_eq", "!=": "op_ne", "<": "op_lt", ">": "op_gt", "<=": "op_le", ">=": "op_ge",
                  "+": "op_add", "-": "op_sub", "*": "op_mul", "/": "op_div", "%": "op_mod", "+=": "op_add_assign",
                  "-=": "op_sub_assign", "*=": "op_mul_assign", "/=": "op_div_assign", "()": "op_call", "[]": "op_index",
                  "<=>": "op_cmp", "<<": "op_shl", ">>": "op_shr", "&": "op_and", "|": "op_or", "^": "op_xor",
                  "!": "op_not", "~": "op_compl", "=": "op_assign"}


def lean_name(name: str) -> str:
    if name.startswith("operator"):
        op = name.removeprefix("operator").strip()
        if op not in OPERATOR_NAMES:
            raise Unsupported(f"operator {op}")
        return OPERATOR_NAMES[op]
    return name + "_" if name in LEAN_KEYWORDS else name


# ---------------------------------------------------------------------------------------------- AST

def inner(node):
    return [c for c in node.get("inner", []) if isinstance(c, dict)]


def unsigned_type(node) -> bool:
    qual = node.get("type", {}).get("qualType", "")
    qual = re.sub(r"\bconst\b", "", qual).strip()
    return qual in UNSIGNED_NAMES


def scoped_lean_name(name: str) -> str:
    return ".".join(lean_name(part) for part in name.split("::"))


def strip(node):
    """Skip nodes that do not change the value in the integer/bool/vector model."""
    while True:
        kind = node.get("kind")
        if kind in ("ImplicitCastExpr", "ParenExpr", "ExprWithCleanups", "MaterializeTemporaryExpr",
                    "CXXBindTemporaryExpr", "ConstantExpr") and len(inner(node)) == 1:
            if kind == "ImplicitCastExpr" and node.get("castKind") in (
                    "IntegralToBoolean", "FloatingToIntegral", "IntegralToFloating", "FloatingCast"):
                return node
            node = inner(node)[0]
            continue
        return node


def peel(node):
    """`strip` and also one-argument constructions (iterator to const_iterator conversions)."""
    while True:
        node = strip(node)
        if node.get("kind") == "CXXConstructExpr" and len(inner(node)) == 1:
            node = inner(node)[0]
            continue
        return node


def strip_casts(node):
    """`strip` and also explicit casts (for lvalues and syntactic patterns)."""
    while True:
        node = strip(node)
        if node.get("kind") in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXFunctionalCastExpr") \
                and len(inner(node)) == 1 and node.get("castKind") in ("NoOp", "LValueToRValue"):
            node = inner(node)[0]
            continue
        return node


def type_of_decl(node) -> str:
    return node["type"]["qualType"]


@dataclass(frozen=True)
class OrderedSetKeyAdapter:
    record: str
    member: str
    parameter: str


def key_argument_reference(node, declaration):
    node = strip(node)
    return node.get('kind') == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') == declaration['id']


def key_argument_member(node, declaration, field):
    node = strip(node)
    kind = node.get('kind')
    if kind == 'MemberExpr':
        matches = node.get('referencedMemberDecl') == field['id']
    elif kind == 'CXXDependentScopeMemberExpr':
        matches = node.get('member') == field['name'] and not node.get('hasExplicitTemplateArgs')
    else:
        return False
    return matches and not node.get('isArrow') and len(inner(node)) == 1 and key_argument_reference(inner(node)[0], declaration)


def ordered_set_key_constructor(node, wrapper, field):
    nodes = inner(node)
    if [part.get('kind') for part in nodes] != ['ParmVarDecl', 'CXXCtorInitializer', 'CompoundStmt']:
        return None
    param, initializer, body = nodes
    if (inner(param) or inner(body) or initializer.get('anyInit', {}).get('id') != field['id']
            or len(inner(initializer)) != 1):
        return None
    construct = inner(initializer)[0]
    if construct.get('kind') != 'ParenListExpr' or len(inner(construct)) != 1:
        return None
    value = inner(construct)[0]
    param_type = type_of_decl(param)
    if param_type == f"{type_of_decl(field)} &" and key_argument_reference(value, param):
        return 'payload'
    if param_type == f"const {wrapper} &" and key_argument_member(value, param, field):
        return 'copy'
    return None


def ordered_set_key_comparison(node, wrapper, field):
    if node.get('kind') != 'FriendDecl' or len(inner(node)) != 1:
        return False
    function = inner(node)[0]
    if (function.get('kind') != 'FunctionDecl' or function.get('name') != 'operator<'
            or type_of_decl(function) != f"bool (const {wrapper} &, const {wrapper} &)"):
        return False
    parts = inner(function)
    if [part.get('kind') for part in parts] != ['ParmVarDecl', 'ParmVarDecl', 'CompoundStmt']:
        return False
    left, right, body = parts
    if len(inner(body)) != 1 or inner(body)[0].get('kind') != 'ReturnStmt':
        return False
    expression = inner(inner(body)[0])
    if len(expression) != 1:
        return False
    comparison = strip(expression[0])
    return (comparison.get('kind') == 'BinaryOperator' and comparison.get('opcode') == '<'
            and len(inner(comparison)) == 2
            and key_argument_member(inner(comparison)[0], left, field) and key_argument_member(inner(comparison)[1], right, field))


def ordered_set_key_adapter(record, template_parameters):
    if record.get('tagUsed') != 'struct' or record.get('bases'):
        return None
    declarations = [node for node in inner(record) if not node.get('isImplicit') and node.get('kind') != 'FullComment']
    kinds = [node.get('kind') for node in declarations]
    if kinds != ['FieldDecl', 'CXXConstructorDecl', 'CXXConstructorDecl', 'FriendDecl']:
        return None
    field, initialize, copy, friend = declarations
    wrapper = record['name']
    parameter = type_of_decl(field)
    if parameter not in template_parameters or not field.get('mutable') or inner(field):
        return None
    constructors = {ordered_set_key_constructor(c, wrapper, field) for c in (initialize, copy)}
    if constructors != {'payload', 'copy'} or not ordered_set_key_comparison(friend, wrapper, field):
        return None
    return OrderedSetKeyAdapter(wrapper, field['name'], parameter)


def normalize_owned_deque(record, field, deque_type, source):
    """Project a nullable private deque owner to its elements (null has zero elements)."""
    field_id = field["id"]

    def receiver(node):
        node = strip(node)
        if node.get("kind") != "MemberExpr" or node.get("referencedMemberDecl") != field_id:
            return None
        base = strip(inner(node)[0])
        if base.get("kind") == "CXXThisExpr":
            return "this"
        if base.get("kind") == "DeclRefExpr":
            ref = base.get("referencedDecl", {})
            if ref.get("kind") == "ParmVarDecl":
                return ref["id"]
        raise Unsupported("owned deque requires a direct member receiver")

    def deque_member(node):
        node = strip(node)
        qualified = node.get("type", {}).get("qualType", "")
        return {**node, "type": {"qualType": ("const " if qualified.startswith("const ") else "") + deque_type}}

    def dereference(node):
        node = strip(node)
        if node.get("kind") == "UnaryOperator" and node.get("opcode") == "*":
            base = strip(inner(node)[0])
            if receiver(base) is not None:
                return base
        return None

    def call_member(node, name, arity=0):
        node = strip(node)
        parts = inner(node)
        if node.get("kind") != "CallExpr" or len(parts) != arity + 1:
            return None
        function = strip(parts[0])
        if (function.get("kind") != "CXXDependentScopeMemberExpr" or function.get("member") != name
                or function.get("isArrow") or function.get("hasExplicitTemplateArgs")
                or len(inner(function)) != 1):
            return None
        return node, function, inner(function)[0], parts[1:]

    def null_test(node):
        node = strip(node)
        if node.get("kind") != "BinaryOperator" or node.get("opcode") != "==":
            return None
        left, right = map(strip, inner(node))
        access = call_member(left, "get")
        if access is None or right.get("kind") != "CXXNullPtrLiteralExpr":
            return None
        return receiver(access[2])

    def with_receiver(call, base, args):
        node, function, _, _ = call
        return {**node, "inner": [{**function, "inner": [deque_member(base)]}, *args]}

    def empty_allocation(node):
        node = strip(node)
        if node.get("kind") != "CallExpr" or len(inner(node)) != 1:
            return False
        function = strip(inner(node)[0])
        parameters = inner(function)
        if (function.get("kind") != "UnresolvedLookupExpr" or function.get("name") != "make_unique"
                or len(parameters) != 1 or parameters[0].get("kind") != "TemplateArgument"
                or re.sub(r"\s+", "", type_of_decl(parameters[0])) != re.sub(r"\s+", "", deque_type)):
            return False
        begin = function["range"]["begin"].get("offset")
        end = function["range"]["end"].get("offset")
        return (begin is not None and end is not None and
                re.match(rb"(?:\s*::)?\s*std\s*::\s*make_unique\s*<", source[begin:end]) is not None)

    def allocated_for_append(branch, following):
        if branch.get("kind") != "IfStmt" or len(inner(branch)) != 2:
            return None
        condition, body = inner(branch)
        owner = null_test(condition)
        if owner is None:
            return None
        if body.get("kind") == "CompoundStmt" and len(inner(body)) == 1:
            body = inner(body)[0]
        if body.get("kind") != "BinaryOperator" or body.get("opcode") != "=":
            return None
        target, value = inner(body)
        if receiver(target) != owner or not empty_allocation(value):
            return None
        append = call_member(following, "emplace_back")
        base = dereference(append[2]) if append is not None else None
        if base is not None and receiver(base) == owner:
            return with_receiver(append, base, [])
        return None

    def rewrite_block(kids):
        results = []
        index = 0
        while index < len(kids):
            child = kids[index]
            action = allocated_for_append(child, kids[index + 1]) if index + 1 < len(kids) else None
            if action is not None:
                results.append(action)
                index += 2
            else:
                results.append(rewrite(child))
                index += 1
        return results

    def rewrite(node):
        kind = node.get("kind")
        kids = inner(node)
        if kind == "FieldDecl" and node.get("id") == field_id:
            if kids:
                raise Unsupported("owned deque only supports empty field initialization")
            return deque_member(node)
        if kind == "CXXCtorInitializer" and node.get("anyInit", {}).get("id") == field_id:
            if len(kids) != 1 or kids[0].get("kind") != "ParenListExpr" or inner(kids[0]):
                raise Unsupported("owned deque needs an empty member initializer")
            return {**node, "anyInit": deque_member(node["anyInit"])}
        if kind == "CompoundStmt":
            return {**node, "inner": rewrite_block(kids)}
        if kind == "ConditionalOperator" and len(kids) == 3:
            test, zero, present = kids
            owner = null_test(test)
            size = call_member(present, "size")
            base = dereference(size[2]) if size is not None else None
            zero = strip(zero)
            if (owner is not None and base is not None and receiver(base) == owner
                    and zero.get("kind") == "IntegerLiteral" and zero.get("value") == "0"):
                return with_receiver(size, base, [])
        if kind == "ArraySubscriptExpr" and len(kids) == 2:
            base = dereference(kids[0])
            if base is not None:
                return {**node, "inner": [deque_member(base), rewrite(kids[1])]}
        swap = call_member(node, "swap", arity=1)
        if swap is not None and receiver(swap[2]) is not None:
            if receiver(swap[3][0]) is None:
                raise Unsupported("owned deque swap requires two direct owners")
            return with_receiver(swap, swap[2], [deque_member(swap[3][0])])
        if kind == "MemberExpr" and node.get("referencedMemberDecl") == field_id:
            raise Unsupported("unsupported use of a private deque owner")
        return {**node, "inner": [rewrite(child) for child in kids]} if kids else node

    return rewrite(record)


def expose_nested_deque_records(decls, source):
    """Qualify private passive record elements of a std::deque in the model."""
    def translate(declaration):
        if declaration.get("kind") != "ClassTemplateDecl":
            return [declaration]
        parameters = [item for item in inner(declaration) if item.get("kind") == "TemplateTypeParmDecl"]
        if (not parameters or any(not item.get("name") or item.get("isParameterPack") for item in parameters)
                or any(item.get("kind") in ("NonTypeTemplateParmDecl", "TemplateTemplateParmDecl")
                       for item in inner(declaration))):
            return [declaration]
        record = next((item for item in inner(declaration)
                       if item.get("kind") == "CXXRecordDecl" and item.get("completeDefinition")), None)
        if record is None or record.get("tagUsed") != "class" or record.get("bases"):
            return [declaration]
        nested = [item for item in inner(record)
                  if item.get("kind") == "CXXRecordDecl" and item.get("completeDefinition")]
        if len(nested) != 1:
            return [declaration]
        nested = nested[0]
        nested_name = nested["name"]
        before = inner(record)[:inner(record).index(nested)]
        if any(item.get("kind") == "AccessSpecDecl" for item in before):
            return [declaration]
        if nested.get("tagUsed") != "struct" or nested.get("bases"):
            return [declaration]
        fields = [field for field in inner(nested) if field.get("kind") == "FieldDecl"]
        if not fields or any(field.get("isBitfield") or inner(field) for field in fields):
            return [declaration]
        if any(item.get("kind") not in ("FieldDecl", "FullComment") and not item.get("isImplicit")
               for item in inner(nested)):
            return [declaration]
        spelling = rf"std::deque\s*<\s*{re.escape(nested_name)}\s*>"
        owner_spelling = rf"std::unique_ptr\s*<\s*({spelling})\s*>"
        slots = [item for item in inner(record) if item.get("kind") == "FieldDecl"
                 and (re.fullmatch(spelling, type_of_decl(item)) or re.fullmatch(owner_spelling, type_of_decl(item)))]
        if len(slots) != 1:
            return [declaration]
        token = re.compile(rf"\b{re.escape(nested_name)}\b")
        types = {item["name"] for item in parameters}
        for field in fields:
            field_type = parse_type(type_of_decl(field), types, {})
            scalar = {"tparam", "int", "u32", "u64", "bool"}
            if field_type.kind not in scalar and not (
                    field_type.kind == "optional" and field_type.args[0].kind in scalar):
                raise Unsupported("private deque elements need passive scalar or optional fields")
        private = True
        for member in inner(record):
            if member.get("kind") == "AccessSpecDecl":
                private = member["access"] != "public"
                continue
            if member.get("kind") == "FriendDecl":
                raise Unsupported("a private deque element cannot escape through a friend")
            if not private and (token.search(member.get("type", {}).get("qualType", ""))
                                or any(token.search(type_of_decl(arg)) for arg in inner(member)
                                       if arg.get("kind") == "ParmVarDecl")):
                raise Unsupported("a private deque element cannot occur in the public API")
        model_name = record["name"] + "_" + nested_name
        if any(item.get("name") == model_name for item in decls):
            raise Unsupported("nested storage record model name conflicts with another declaration")
        names = [p["name"] for p in parameters]
        type_spelling = re.compile(rf"(?<![A-Za-z0-9_:]){re.escape(nested_name)}\b")
        qualified = model_name + "<" + ", ".join(names) + ">"

        def rewrite(value):
            if isinstance(value, list):
                return [rewrite(item) for item in value]
            if not isinstance(value, dict):
                return value
            if value.get("kind") in ("TypeAliasDecl", "TypedefDecl", "TemplateTypeParmDecl", "EnumDecl"):
                if value.get("name") == nested_name:
                    raise Unsupported("shadowing a private storage record")
            return {key: type_spelling.sub(qualified, item)
                    if key in ("qualType", "desugaredQualType") and isinstance(item, str)
                    else rewrite(item) for key, item in value.items()}

        model = {**rewrite(nested), "name": model_name, "lean_model_only": True}
        auxiliary = {"kind": "ClassTemplateDecl", "name": model_name,
                     "inner": [*parameters, model]}
        receiver = {**record, "inner": [x for x in inner(record) if x is not nested]}
        owner = re.fullmatch(owner_spelling, type_of_decl(slots[0]))
        if owner is not None:
            receiver = normalize_owned_deque(receiver, slots[0], owner[1], source)
        receiver = rewrite(receiver)
        declaration = {**declaration, "inner": [receiver if item is record else item for item in inner(declaration)]}
        return [auxiliary, declaration]

    return [part for declaration in decls for part in translate(declaration)]


def normalize_ordered_set_key_adapters(decls):
    def simple_set_access(call, container_id, names):
        if call.get('kind') != 'CallExpr' or not inner(call):
            return None
        function = strip(inner(call)[0])
        if (function.get('kind') != 'CXXDependentScopeMemberExpr' or function.get('member') not in names
                or function.get('isArrow') or function.get('hasExplicitTemplateArgs') or len(inner(function)) != 1):
            return None
        base = strip(inner(function)[0])
        if (base.get('kind') != 'MemberExpr' or base.get('referencedMemberDecl') != container_id
                or len(inner(base)) != 1 or strip(inner(base)[0]).get('kind') != 'CXXThisExpr'):
            return None
        return function

    def normalize_class(record, nested, adapter, container):
        name, field, parameter = adapter.record, adapter.member, adapter.parameter
        token = re.compile(rf'\b{re.escape(name)}\b')
        old_type = type_of_decl(container)
        new_type = f'std::set<{parameter}>'

        def key_value(node):
            ref = strip(node)
            if (ref.get('kind') != 'DeclRefExpr' or type_of_decl(ref) != parameter
                    or ref.get('valueCategory') != 'lvalue'):
                raise Unsupported('ordered set wrapper requires a direct key lvalue')
            return ref

        def walk(node, allow_receiver=False):
            kind = node.get('kind')
            kids = inner(node)
            if kind in ('TypeAliasDecl', 'TypedefDecl', 'TemplateTypeParmDecl') and node.get('name') == name:
                raise Unsupported('shadowing an ordered set key wrapper')
            def rewrite_method(method):
                return {**method, 'inner': [walk(inner(method)[0], allow_receiver=True)]}

            if kind == 'CallExpr':
                method = simple_set_access(node, container['id'], {'size'})
                if method is not None and len(kids) == 1:
                    return {**node, 'inner': [rewrite_method(method)]}
                method = simple_set_access(node, container['id'], {'emplace', 'erase', 'count'})
                if method is not None:
                    if len(kids) != 2:
                        raise Unsupported('ordered set wrapper call arity')
                    if method['member'] == 'emplace':
                        key = key_value(kids[1])
                        method = {**method, 'member': 'insert'}
                    else:
                        construction = strip(kids[1])
                        if (construction.get('kind') != 'CXXUnresolvedConstructExpr'
                                or type_of_decl(construction) != name or len(inner(construction)) != 1):
                            raise Unsupported('ordered set lookup requires its checked key wrapper')
                        key = key_value(inner(construction)[0])
                    return {**node, 'inner': [rewrite_method(method), walk(key)]}
            if (kind == 'CXXDependentScopeMemberExpr' and node.get('member') == field
                    and node.get('isArrow') and len(kids) == 1):
                child = strip(kids[0])
                method = simple_set_access(child, container['id'], {'begin', 'rbegin'})
                if method is not None:
                    if len(inner(child)) != 1 or node.get('hasExplicitTemplateArgs'):
                        raise Unsupported('unsupported ordered set iterator read')
                    call = {**child, 'inner': [rewrite_method(method)]}
                    return {'kind': 'UnaryOperator', 'opcode': '*', 'range': node['range'],
                            'type': {'qualType': parameter}, 'valueCategory': 'lvalue', 'inner': [call]}
            if kind in ('FieldDecl', 'MemberExpr') and container['id'] in (
                    node.get('id'), node.get('referencedMemberDecl')):
                if kind == 'MemberExpr' and not allow_receiver:
                    raise Unsupported('ordered set wrapper escapes a supported container operation')
                if type_of_decl(node) != old_type:
                    raise Unsupported('ordered set receiver type changed')
                node = {**node, 'type': {'qualType': new_type}}
            for spelling in node.get('type', {}).values():
                if isinstance(spelling, str) and token.search(spelling):
                    raise Unsupported('unmodeled use of ordered set key wrapper')
            rewritten = {**node, 'inner': [walk(child) for child in kids]} if kids else node
            if isinstance(node.get('anyInit'), dict):
                rewritten = {**rewritten, 'anyInit': walk(node['anyInit'])}
            return rewritten

        return {**record, 'inner':[walk(node) for node in inner(record) if node is not nested]}

    result = []
    for declaration in decls:
        if declaration.get('kind') != 'ClassTemplateDecl':
            result.append(declaration)
            continue
        params = {x['name'] for x in inner(declaration) if x.get('kind') == 'TemplateTypeParmDecl' and x.get('name')}
        record = next((x for x in inner(declaration)
                       if x.get('kind') == 'CXXRecordDecl' and x.get('completeDefinition')), None)
        if not record or record.get('bases') or record.get('tagUsed') != 'class':
            result.append(declaration)
            continue
        private = True
        nested = None
        adapter = None
        for part in inner(record):
            if part.get('kind') == 'AccessSpecDecl':
                private = part['access'] == 'private'
            if private and part.get('kind') == 'CXXRecordDecl' and part.get('completeDefinition'):
                if candidate := ordered_set_key_adapter(part, params):
                    if adapter is not None:
                        raise Unsupported('multiple ordered set key wrappers')
                    nested, adapter = part, candidate
        if adapter is None:
            result.append(declaration)
            continue
        spelling = rf'std::set\s*<\s*{re.escape(adapter.record)}\s*>'
        containers = [x for x in inner(record)
                      if x.get('kind') == 'FieldDecl' and re.fullmatch(spelling, type_of_decl(x))]
        if len(containers) != 1:
            raise Unsupported('ordered set wrapper needs one default std::set field')
        normalized = normalize_class(record, nested, adapter, containers[0])
        result.append({**declaration, 'inner':[normalized if x is record else x for x in inner(declaration)]})
    return result


def always_returns(node) -> bool:
    """A syntactically total return, without inferring facts about conditions."""
    kind = node.get("kind")
    children = inner(node)
    if kind == "ReturnStmt":
        return True
    if kind == "CompoundStmt":
        return bool(children) and always_returns(children[-1])
    if kind == "IfStmt" and node.get("hasElse") and not node.get("hasInit") and not node.get("hasVar"):
        return len(children) == 3 and always_returns(children[1]) and always_returns(children[2])
    return False


# ------------------------------------------------------------------------------------------ context

# The parameter of a method that constructs values of a class type parameter (docs/translation.md).
CONSTRUCT_STATE = "cppConstructState"


@dataclass
class Sig:
    """A translated C++ function: how a call is written and what it returns."""
    cpp_name: str
    lean_name: str
    params: list            # [(name, Ty, is_mut_ref)]
    ret: Ty
    owner: str | None = None      # class name for methods/constructors
    is_const: bool = True         # const method (does not change *this)
    is_static: bool = False
    is_ctor: bool = False
    node: dict | None = None
    tparams: list = field(default_factory=list)
    public: bool = True
    containers: list = field(default_factory=list)
    policies: dict = field(default_factory=dict)   # tparam -> [static member names] (policy classes)
    value_params: dict = field(default_factory=dict)
    constraints: list[str] = field(default_factory=list)
    uses_globals: bool = False
    initializes_globals: bool = False
    preserves_receiver: bool = False

    @property
    def mut_refs(self):
        return [p for p in self.params if p[2]]

    def outputs(self):
        out = []
        if self.is_ctor:
            if not self.mut_refs and not self.uses_globals:
                return out
            out = ["ret", *[p[0] for p in self.mut_refs]]
            if self.uses_globals:
                out.append("@globals")
            return out
        if self.ret.kind != "void":
            out.append("ret")
        out += [p[0] for p in self.mut_refs]
        if self.owner and not self.is_const and not self.is_static and not self.preserves_receiver:
            out.append("self")
        if self.uses_globals:
            out.append("@globals")
        return out


@dataclass
class ClassInfo:
    name: str
    tparams: list
    fields: list              # [(name, Ty, init_node or None)]
    methods: list             # [Sig]
    public_fields: set[str] = field(default_factory=set)
    value_params: dict = field(default_factory=dict)
    constraints: list[str] = field(default_factory=list)
    model_only: bool = False


def class_ty(info):
    args = tuple(Ty("vparam", t, (info.value_params[t],)) if t in info.value_params
                 else Ty("tparam", t) for t in info.tparams)
    return Ty("cls", info.name, args)


def substitute_constraint(condition, bindings):
    return re.sub(r'\b[A-Za-z_][A-Za-z_0-9]*\b',
                  lambda m: lean_type(bindings[m[0]]) if m[0] in bindings else m[0], condition)


def class_requirements(ty, classes):
    requirements = []
    if ty.kind == "cls":
        info = classes[ty.name]
        bindings = dict(zip(info.tparams, ty.args))
        requirements.extend("Cpp.TemplateConstraint " + substitute_constraint(c, bindings) for c in info.constraints)
    for arg in ty.args:
        requirements.extend(class_requirements(arg, classes))
    return requirements


class Requirements:
    def __init__(self):
        self.items: list[str] = []

    def add(self, item: str):
        if item not in self.items:
            self.items.append(item)


ORDER = ["Cpp.Streams", "Cpp.TypeTraits", "Cpp.ConstructState", "Cpp.Construct", "Cpp.ReadField", "Cpp.MulResult", "Cpp.AddResult", "Cpp.ConditionalResult", "Inhabited", "Zero", "One", "NatCast", "IntCast", "Add", "Sub", "Mul", "Neg", "Div", "Mod", "LT", "LE",
         "DecidableLT", "DecidableLE", "DecidableEq", "Min", "Max"]


def binders(tparams, reqs: list[str], value_params=None) -> str:
    value_params = value_params or {}
    out = []
    for t in tparams:
        out.append(f"{{{lean_name(t) if t in value_params else t} : {lean_type(value_params[t]) if t in value_params else 'Type'}}}")
    def key(r):
        cls = r.split()[0]
        return (ORDER.index(cls) if cls in ORDER else len(ORDER), r)
    for r in sorted(reqs, key=key):
        if r.startswith('Cpp.TypeTraits "'):
            parameter = re.fullmatch(r'Cpp.TypeTraits "(\w+)" \w+', r)
            if parameter is None:
                raise Unsupported(f"non-generic type trait requirement {r}")
            out.append(f"[cppTypeTraits_{parameter[1]} : {r}]")
        elif r.startswith('Cpp.ModToUInt32 "'):
            parameter = re.fullmatch(r'Cpp.ModToUInt32 "(\w+)" \w+', r)
            if parameter is None:
                raise Unsupported(f"remainder contract binder {r}")
            out.append(f"[cppModToUInt32_{parameter[1]} : {r}]")
        elif r.startswith("Cpp.TemplateConstraint ") and "Cpp.TypeTraits." in r:
            out.append(f"[{constraint_binder(r)} : {r}]")
        else:
            out.append(f"[{r}]")
    return " ".join(out)


class Fn:
    """Translation state of one function body."""

    def __init__(self, tr: "Translator", sig: Sig, cls: ClassInfo | None):
        self.tr = tr
        self.sig = sig
        self.cls = cls
        self.scopes: list[dict] = [{}]
        self.local_aliases: dict[str, Ty] = {}   # `using P = ...;` inside the body
        self.lines: list[str] = []
        self.indent = 1
        self.tmp = 0
        self.reqs = Requirements()
        self.field_names = {}
        self.continue_prefix: list[list[str]] = []
        self.callees: list[Sig] = []
        self.member_call_bindings: dict[int, list[tuple[dict, set]]] = {}
        self.type_trait_bindings: set[tuple[str, bool, bool]] = set()
        self.used_names: set[str] = set()
        self.floating_constexpr_types: set[str] = set()
        occupied = local_names(sig.node) | {p[0] for p in sig.params} | set(sig.tparams)
        self.global_names = {}
        for key, (name, _, _) in tr.globals.items():
            candidate = "cppGlobal_" + name
            while candidate in occupied:
                candidate += "_"
            occupied.add(candidate)
            self.global_names[key] = candidate
        self.global_input = "cppGlobals"
        while self.global_input in occupied:
            self.global_input += "_"

    def global_value(self):
        return "({ " + ", ".join(f"{lean_name(name)} := {self.global_names[key]}"
                                   for key, (name, _, _) in self.tr.globals.items()) + f" }} : {self.tr.global_state_type()})"

    # scopes
    def declare(self, name, ty):
        """Declare a C++ variable; a name already used in the function gets a fresh Lean name, since Lean's
        `do` notation does not let a mutable variable be shadowed (even by a later sibling block)."""
        for requirement in class_requirements(ty, self.tr.classes):
            self.reqs.add(requirement)
        visible = self.lookup(name) is not None
        lean = lean_name(name)
        if visible or lean in self.used_names or lean in self.visible_lean_names():
            k = 1
            while f"{name}_{k}" in self.used_names or f"{name}_{k}" in self.visible_lean_names():
                k += 1
            lean = f"{name}_{k}"
        self.used_names.add(lean)
        scope = self.scopes[-1]
        scope[name] = ty
        scope.setdefault("__names__", {})[name] = lean

    def visible_lean_names(self):
        out = set(self.field_names.values())
        for scope in self.scopes:
            out |= set(scope.get("__names__", {}).values())
        return out

    def lookup(self, name):
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        return None

    def emit(self, text):
        self.lines.append("  " * self.indent + text)

    def fresh(self):
        self.tmp += 1
        return f"t{self.tmp}"

    def need(self, cls, ty: Ty):
        if ty.kind == "tparam":
            self.reqs.add(f"{cls} {ty.name}")
        elif ty.kind in ("vec", "pair", "cls"):
            if cls == "Inhabited":
                for a in ty.args:
                    if a.kind != "vec":
                        self.need("Inhabited", a)

    # ------------------------------------------------------------------ expressions
    def expr(self, node, pre: list[str], expected: Ty | None = None):
        """Translate an rvalue; calls are hoisted into `pre` as `let t ← ...` lines. Returns (text, Ty)."""
        if self.sig.uses_globals:
            references, effectful_calls = set(), 0
            def scan(n):
                nonlocal effectful_calls
                reference = n.get("referencedDecl", {})
                if reference.get("id") in self.tr.globals:
                    references.add(reference["id"])
                callable_kinds = ("FunctionDecl", "CXXMethodDecl") if self.tr.static_members else ("FunctionDecl",)
                name = self.tr.qualified_functions.get(reference.get("id"), reference.get("name"))
                if (n.get("kind") == "DeclRefExpr" and reference.get("kind") in callable_kinds
                        and name in self.tr.global_functions):
                    effectful_calls += 1
                if n.get("kind") == "UnresolvedLookupExpr" and n.get("name") in self.tr.global_functions:
                    name = n["name"]
                    if not self.tr.static_members or not name.startswith("operator"):
                        effectful_calls += 1
                    else:
                        ids = {candidate.get("id") for candidate in n.get("lookups", [])}
                        if any(sig.uses_globals and sig.node.get("id") in ids
                               for sig in self.tr.functions.get(name, [])):
                            effectful_calls += 1
                if self.tr.static_members:
                    if self.tr.constructor_name(n) in self.tr.global_constructors:
                        effectful_calls += 1
                    if n.get("kind") in ("MemberExpr", "CXXDependentScopeMemberExpr", "UnresolvedMemberExpr"):
                        member = n.get("name") or n.get("member")
                        if member is None and n.get("kind") == "UnresolvedMemberExpr":
                            member = self.tr.member_token(n)
                        if member in self.tr.global_methods:
                            effectful_calls += 1
                for child in inner(n):
                    scan(child)
            scan(node)
            if effectful_calls > 1 or references and effectful_calls:
                raise Unsupported(f"global reads and stateful calls require separate full expressions in {self.sig.lean_name}")
        if expected is not None and expected.kind == "cls":
            raw = strip(node)
            if raw.get("kind") not in ("CXXConstructExpr", "CXXTemporaryObjectExpr", "CXXUnresolvedConstructExpr"):
                try:
                    actual = self.tr.ty(raw.get("type", {}).get("qualType", ""), self)
                except Unsupported:
                    actual = None
                if actual is not None and actual != expected:
                    info = self.tr.classes[expected.name]
                    conversions = [sig for sig in info.methods if sig.is_ctor and len(sig.params) == 1
                                   and not re.search(r"\bexplicit\b", self.tr.span(sig.node))]
                    eligible = [sig for sig in conversions if self.trait_eligibility(sig, [node]) is True]
                    if eligible:
                        competing = [sig for sig in conversions if self.trait_eligibility(sig, [node]) is not False]
                        if len(competing) != 1:
                            raise Unsupported("cannot rank competing implicit conversion constructors")
                        return self.call_sig(eligible[0], None, [node], pre, expected)
                    candidates = [sig for sig in info.methods if sig.is_ctor and len(sig.params) == 1
                                  and subst(sig.params[0][1], info.tparams, expected.args) == actual
                                  and not re.search(r"\bexplicit\b", self.tr.span(sig.node))]
                    if len(candidates) == 1:
                        # Recurse with the scalar constructor's parameter type so the
                        # argument is evaluated only once, including any nested call.
                        return self.call_sig(candidates[0], None, [node], pre, expected)
        raw = strip(node)
        if expected == U32 and ((raw.get("kind") == "BinaryOperator" and raw.get("opcode") == "%")
                or (raw.get("kind") == "CXXOperatorCallExpr" and self.operator_name(raw) == "%")):
            operands = inner(raw) if raw.get("kind") == "BinaryOperator" else inner(raw)[1:]
            if len(operands) == 2:
                left, right = operands
                try:
                    aty = self.tr.ty(strip(left)["type"]["qualType"], self)
                    bty = self.tr.ty(strip(right)["type"]["qualType"], self)
                except Unsupported:
                    aty = bty = None
                if aty is not None and bty is not None and aty.kind == "tparam" and bty.kind == "u32":
                    at, _ = self.expr(left, pre)
                    bt, _ = self.expr(right, pre)
                    self.reqs.add(f'Cpp.ModToUInt32 "{aty.name}" {aty.name}')
                    return f'(Cpp.ModToUInt32.apply (tag := "{aty.name}") {at} {bt})', U32
        text, ty = self._expr(node, pre, expected)
        if expected is not None and expected.kind == "cls" and ty != expected:
            info = self.tr.classes[expected.name]
            candidates = [sig for sig in info.methods if sig.is_ctor and len(sig.params) == 1
                          and not sig.params[0][2]
                          and not re.search(r"\bexplicit\b", self.tr.span(sig.node))]
            matching = [sig for sig in candidates
                        if subst(sig.params[0][1], info.tparams, expected.args) == ty]
            if not matching and ty.kind == "int" and strip(node).get("kind") == "IntegerLiteral":
                matching = [sig for sig in candidates
                            if subst(sig.params[0][1], info.tparams, expected.args).kind == "tparam"]
            if len(matching) == 1:
                sig = matching[0]
                pty = subst(sig.params[0][1], info.tparams, expected.args)
                value, _ = self.convert(text, ty, pty, node)
                self.callees.append(sig)
                tmp = self.fresh()
                pre.append(f"let {tmp} ← {sig.lean_name} {value}")
                return tmp, expected
        if expected is not None:
            text, ty = self.convert(text, ty, expected, node)
        return text, ty

    def convert(self, text, ty, expected, node=None):
        if expected is None or ty == expected:
            return text, (expected if expected is not None and ty.kind == expected.kind == "int" else ty)
        if ty.kind in ("add_result", "mul_result", "conditional_result") and expected.kind == "tparam":
            self.reqs.add(f"Cpp.Conv {lean_type(ty)} {expected.name}")
            return f"(Cpp.Conv.conv {text} : {expected.name})", expected
        if ty.kind == "tparam" and expected.kind == "tparam":
            # the implicit conversion of a template parameter T to another one S (whatever C++ does for the instance)
            self.reqs.add(f"Cpp.Conv {ty.name} {expected.name}")
            return f"(Cpp.Conv.conv {text} : {expected.name})", expected
        lit = strip(node) if node is not None else None
        is_lit = lit is not None and lit.get("kind") == "IntegerLiteral"
        if expected.kind in ("u32", "u64"):
            lt = lean_type(expected)
            if is_lit:
                return f"({lit['value']} : {lt})", expected
            if ty.kind == "int":
                return f"({lt}.ofInt {text})", expected
            if ty.kind in ("u32", "u64"):
                return f"({text}.to{lt})", expected
            if ty.kind == "bool":
                return f"(if {text} then (1 : {lt}) else 0)", expected
        if ty.kind in ("u32", "u64"):
            if expected.kind == "int":
                src = 32 if ty.kind == "u32" else 64
                if expected.width > src:
                    return f"({text}.toNat : Int)", expected
                # unsigned to a signed type of the same or smaller width: two's complement (C++23 [conv.integral])
                return f"(Cpp.toSigned {expected.width} {text}.toNat)", expected
            if expected.kind == "bool":
                return f"(decide ({text} ≠ 0))", BOOL
            if expected.kind == "tparam":
                self.need("NatCast", expected)
                return f"(Nat.cast {text}.toNat : {expected.name})", expected
        if ty.kind == "int" and expected.kind == "tparam":
            n = lit
            if n is not None and n.get("kind") == "IntegerLiteral" and n["value"] in ("0", "1"):
                self.need("Zero" if n["value"] == "0" else "One", expected)
                return f"({n['value']} : {expected.name})", expected
            self.need("IntCast", expected)
            return f"(Int.cast {text} : {expected.name})", expected
        if ty.kind == "int" and expected.kind == "bool":
            return f"(decide ({text} ≠ 0))", BOOL
        if ty.kind == "bool" and expected.kind == "int":
            return f"(if {text} then (1 : Int) else 0)", INT
        if ty.kind == "bool" and expected.kind == "tparam":
            # bool to an arithmetic T: false is 0 and true is 1.
            self.need("IntCast", expected)
            return f"(Int.cast (if {text} then (1 : Int) else 0) : {expected.name})", expected
        if ty.kind == "unknown":
            return text, expected
        if ty.kind == "tparam" and expected.kind in ("int", "u32", "u64"):
            # the implicit conversion of a template parameter to an integer type (Cpp.Conv)
            lt = lean_type(expected)
            self.reqs.add(f"Cpp.Conv {ty.name} {lt}")
            return f"(Cpp.Conv.conv {text} : {lt})", expected
        if ty.kind == "vec" and expected.kind == "vec":
            if ty.args[0].kind == "unknown" or ty.args[0] == expected.args[0]:
                return text, expected
        raise Unsupported(f"conversion from {ty} to {expected}")

    def range_base(self, arg, which):
        """The vector `v` of an iterator argument `v.begin()` / `v.end()`, or None."""
        call = peel(arg)
        callee = strip(inner(call)[0]) if inner(call) else {}
        member = callee.get("name") or callee.get("member")
        if call.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or member != which or not inner(callee):
            return None
        return inner(callee)[0]

    def lower_bound_index(self, n, pre):
        """`std::lower_bound(v.begin(), v.end(), x) - v.begin()`: the index of the first element not less than `x`
        (https://en.cppreference.com/w/cpp/algorithm/lower_bound; the range must be partitioned by `e < x`),
        at most log2(n) + 1 comparisons. Returns (text, Ty) or None."""
        if n.get("kind") == "BinaryOperator" and n.get("opcode") == "-":
            left, right = inner(n)
        elif n.get("kind") == "CXXOperatorCallExpr" and self.operator_name(n) == "-" and len(inner(n)) == 3:
            left, right = inner(n)[1:]
        else:
            return None
        call = peel(left)
        if call.get("kind") != "CallExpr" or len(inner(call)) != 4:
            return None
        callee = strip(inner(call)[0])
        name = callee.get("referencedDecl", {}).get("name") if callee.get("kind") == "DeclRefExpr" \
            else callee.get("name")
        if name != "lower_bound" or not re.sub(r"\s+", "", self.tr.span(callee)).startswith("std::lower_bound"):
            return None
        bases = [self.range_base(inner(call)[1], "begin"), self.range_base(inner(call)[2], "end"),
                 self.range_base(right, "begin")]
        if any(b is None for b in bases):
            raise Unsupported("std::lower_bound over a range other than v.begin(), v.end()")
        target = self.lvalue(bases[0])
        if self.lvalue(bases[1])[:2] != target[:2] or self.lvalue(bases[2])[:2] != target[:2]:
            raise Unsupported("std::lower_bound over different vectors")
        if target[3].kind != "vec" or target[3].args[0].kind not in ("tparam", "int", "u32", "u64"):
            raise Unsupported("std::lower_bound of a non-vector")
        elem = target[3].args[0]
        cur = self.read_lvalue(target)
        x, _ = self.expr(inner(call)[3], pre, elem)
        self.need("LT", elem)
        self.need("DecidableLT", elem)
        pre.append(f"Cpp.tickN (Nat.log2 {cur}.size + 1)")
        return f"(Cpp.lowerBound {cur} {x})", INT

    def _expr(self, node, pre, expected):
        n = strip(node)
        kind = n.get("kind")
        found = self.lower_bound_index(n, pre)
        if found is not None:
            return found
        if kind in ("UnresolvedLookupExpr", "DependentScopeDeclRefExpr"):
            text = re.sub(r"\s+", "", self.tr.span(n))
            m = re.fullmatch(r"std::is_floating_point_v<(\w+)>", text)
            if m:
                return self.numeric_trait(m.group(1), "isFloatingPoint", BOOL)
            m = re.fullmatch(r"std::numeric_limits<(\w+)>::has_infinity", text)
            if m:
                return self.numeric_trait(m.group(1), "hasInfinity", BOOL)
        if kind == "IntegerLiteral":
            lty = self.tr.ty(n["type"]["qualType"], self)
            if lty.kind in ("u32", "u64"):
                return f"({n['value']} : {lean_type(lty)})", lty
            return n["value"], lty
        if kind == "CXXBoolLiteralExpr":
            return ("true" if n["value"] else "false"), BOOL
        if kind == "CharacterLiteral":
            return str(n["value"]), INT
        if kind in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXFunctionalCastExpr", "ImplicitCastExpr"):
            cast = n.get("castKind")
            subs = inner(n)
            if len(subs) != 1:
                raise Unsupported(f"cast {cast} with {len(subs)} operands")
            sub = subs[0]
            if cast == "IntegralToBoolean":
                t, ty = self.expr(sub, pre)
                return self.convert(t, ty, BOOL, sub)
            if cast in ("FloatingToIntegral", "IntegralToFloating", "FloatingCast"):
                raise Unsupported(f"floating point cast {cast}")
            target = self.tr.ty(n["type"]["qualType"], self)
            t, ty = self.expr(sub, pre)
            return self.convert(t, ty, target, sub)
        if kind == "DeclRefExpr":
            name = n["referencedDecl"]["name"]
            key = n["referencedDecl"].get("id")
            if key in self.tr.globals:
                return self.global_names[key], self.tr.globals[key][1]
            constant = self.tr.constants.get(n["referencedDecl"].get("id"))
            if constant is not None:
                return f"cp.{scoped_lean_name(constant[0])}", constant[1]
            if key in self.tr.static_constant_methods:
                methods = [] if self.cls is None else [s for s in self.cls.methods if s.node.get("id") == key]
                if len(methods) != 1:
                    raise Unsupported(f"static constant {name} outside its class")
                return self.call_sig(methods[0], None, [], pre)
            ty = self.lookup(name)
            if ty is None:
                raise Unsupported(f"unknown variable {name}")
            return self.var_name(name), ty
        if kind == "DependentScopeDeclRefExpr" and self.cls is not None:
            # `C<A>::NAME` of a static constant of the enclosing class template C given with fewer arguments (the
            # others are the defaults, e.g. `ListGraph<Cost>::UNREACHABLE` inside ListGraph<Cost, E>). The
            # initializer of the constant uses only the given parameters, so its value is that of this class.
            text = re.sub(r"\s+", "", self.tr.span(n))
            m = re.fullmatch(rf"{re.escape(self.cls.name)}<([^<>]*)>::(\w+)", text)
            methods = [s for s in self.cls.methods if m and s.node.get("lean_static_constant") and s.cpp_name == m.group(2)]
            if m and len(methods) == 1:
                given = m.group(1).split(",")
                used = set(re.findall(r"\b\w+\b", json.dumps(methods[0].node)))
                if given != self.cls.tparams[:len(given)] or \
                        any(t in used for t in self.cls.tparams[len(given):]):
                    raise Unsupported("static constant of another specialization")
                return self.call_sig(methods[0], None, [], pre)
            raise Unsupported("dependent scope reference")
        if kind == "MemberExpr":
            base = strip(inner(n)[0])
            if base.get("kind") == "CXXThisExpr":
                return self.field_ref(n["name"])
            t, bty = self.expr(base, pre)
            if bty.kind == "pair" and n["name"] in ("first", "second"):
                return f"{t}.{1 if n['name'] == 'first' else 2}", bty.args[0 if n["name"] == "first" else 1]
            if bty.kind == "cls":
                info = self.tr.classes[bty.name]
                for fname, fty, _ in info.fields:
                    if fname == n["name"]:
                        return f"{t}.{lean_name(fname)}", subst(fty, info.tparams, bty.args)
            raise Unsupported(f"member {n['name']}")
        if kind == "CXXDependentScopeMemberExpr":
            member = n.get("member")
            if inner(n):
                t, bty = self.expr(inner(n)[0], pre)
                if bty.kind == "pair" and member in ("first", "second"):
                    i = 0 if member == "first" else 1
                    return f"{t}.{i + 1}", bty.args[i]
                if bty.kind == "cls":
                    info = self.tr.classes[bty.name]
                    for fname, fty, _ in info.fields:
                        if fname == member:
                            return f"{t}.{lean_name(fname)}", subst(fty, info.tparams, bty.args)
                typed = self.default_field_type(bty, member) if not n.get("isArrow") else None
                if typed is not None:
                    self.reqs.add(f'Cpp.Field "{member}" {lean_type(bty)} {lean_type(typed)}')
                    return f'(Cpp.Field.get (member := "{member}") {t})', typed
                if (bty.kind == "tparam" and bty.name in self.sig.tparams and member
                        and not n.get("isArrow") and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", member)):
                    self.reqs.add(f'Cpp.ReadField "{member}" {lean_type(bty)}')
                    return f'(Cpp.ReadField.read (member := "{member}") {t})', Ty("field_value", member, (bty,))
            raise Unsupported("member access without call")
        if kind == "ArraySubscriptExpr" or (kind == "CXXOperatorCallExpr" and self.operator_name(n) == "[]"):
            base, index = self.subscript_parts(n)
            bt, bty = self.expr(base, pre)
            it, _ = self.expr(index, pre, INT)
            if bty.kind == "umap":
                # std::unordered_map::operator[]: the mapped value, inserting a value-initialized one for a new key
                # (Cpp.umapIndex). The map is an lvalue that is updated.
                target = self.lvalue(base)
                if target[1]:
                    raise Unsupported("subscript of an unordered_map inside another object")
                self.umap_value_ok(bty.args[1])
                tmp = self.fresh()
                pre.append(f"let {tmp} ← Cpp.umapIndex {bt} {it}")
                pre.extend(self.assign_lines(target, f"{tmp}.2"))
                return f"{tmp}.1", bty.args[1]
            if bty.kind not in ("vec", "deque", "string", "constant_array"):
                raise Unsupported(f"subscript of {bty}")
            elem = bty.args[0]
            self.need("Inhabited", elem)
            return f"(Cpp.get {bt} {it})", elem
        if kind == "UnaryOperator":
            op = n["opcode"]
            sub = inner(n)[0]
            text = re.sub(r"\s+", "", self.tr.span(n))
            neg_inf = re.fullmatch(r"-std::numeric_limits<(\w+)>::infinity\(\)", text)
            if op == "-" and neg_inf and neg_inf.group(1) in self.floating_constexpr_types:
                t = neg_inf.group(1)
                return self.numeric_trait(t, "negativeInfinity", Ty("tparam", t))
            if op == "*" and strip(sub).get("kind") == "CXXThisExpr":
                return self.self_value(), class_ty(self.cls)
            if op == "*":
                take = self.ordered_set_deref(sub, pre)
                if take is not None:
                    return take
            if op in ("++", "--"):
                # `i++` / `--i` of a local integer inside a larger expression. `stmt` rejects a full expression that
                # also reads or changes `i` elsewhere (their order would be unsequenced or unspecified).
                base = strip(sub)
                element = self.subscript_root(base)
                if element is not None:
                    # `--v[i]` of an element of a local vector: the index has no side effects, and `stmt` rejects
                    # another use of `v` in the same full expression.
                    if self.has_side_effects(self.subscript_parts(base)[1]):
                        raise Unsupported("increment of an element with a side-effecting index")
                elif base.get("kind") != "DeclRefExpr" or \
                        base.get("referencedDecl", {}).get("kind") not in ("VarDecl", "ParmVarDecl"):
                    raise Unsupported("increment inside an expression")
                target = self.lvalue(sub)
                if target[3].kind not in ("int", "u32", "u64"):
                    raise Unsupported("increment of a non-integer")
                current = self.read_lvalue(target)
                sym = "+" if op == "++" else "-"
                result = current
                if n.get("isPostfix"):
                    result = self.fresh()
                    pre.append(f"let {result} := {current}")
                pre.extend(self.assign_lines(target, f"({current} {sym} 1)"))
                return (result if n.get("isPostfix") else self.read_lvalue(target)), target[3]
            t, ty = self.expr(sub, pre)
            if op == "-":
                if ty.kind == "tparam":
                    self.need("Neg", ty)
                if ty.kind in ("u32", "u64"):
                    return f"(0 - {t})", ty
                if ty.kind == "bool":
                    t, ty = self.convert(t, ty, INT32, sub)
                return f"(-{t})", ty
            if op == "+":
                return t, ty
            if op == "!":
                t, ty = self.convert(t, ty, BOOL, sub)
                return f"(!{t})", BOOL
            if op == "~":
                if ty.kind in ("u32", "u64"):
                    return f"(~~~{t})", ty
                return f"(-{t} - 1)", ty
            raise Unsupported(f"unary {op}")
        if kind == "CompoundAssignOperator":
            lhs, rhs = inner(n)
            if self.tr.functions.get("operator" + n["opcode"]):
                raise Unsupported("unresolved compound operator has free overload candidates")
            return self.method_call(lhs, "operator" + n["opcode"], [rhs], pre)
        if kind == "BinaryOperator":
            return self.binary(n, pre)
        if kind == "CXXOperatorCallExpr":
            op = self.operator_name(n)
            args = inner(n)[1:]
            if op == "*" and len(args) == 1:
                take = self.ordered_set_deref(args[0], pre)
                if take is not None:
                    return take
            if op in ("+=", "-=", "*=", "/=", "%=") and len(args) == 2:
                callee = strip(inner(n)[0])
                if callee.get("referencedDecl", {}).get("kind") != "CXXMethodDecl":
                    raise Unsupported("compound operator other than a resolved member")
                return self.method_call(args[0], "operator" + op, args[1:], pre)
            if op in ("++", "--") and args:
                base = strip(args[0])
                if base.get("kind") == "UnaryOperator" and base.get("opcode") == "*" and \
                        strip(inner(base)[0]).get("kind") == "CXXThisExpr":
                    return self.self_call("operator" + op, args[1:], pre)
                return self.method_call(args[0], "operator" + op, args[1:], pre)
            if op in ("+", "-", "*", "/", "%", "<", ">", "<=", ">=", "==", "!=", "<=>", "<<", ">>", "&&", "||") and len(args) == 2:
                return self.binary_parts(op, args[0], args[1], pre, callee=strip(inner(n)[0]))
            if op in ("+", "-", "!", "~") and len(args) == 1:
                t, ty = self.expr(args[0], pre)
                if ty.kind == "cls":
                    reference = strip(inner(n)[0]).get("referencedDecl")
                    if reference is None:
                        raise Unsupported("unresolved class unary operator")
                    sig = self.tr.resolve_function(reference["id"])
                    if sig.cpp_name != "operator" + op or sig.mut_refs:
                        raise Unsupported("unary operator declaration or mutable operand")
                    if "&" in type_of_decl(sig.node).split("(")[0]:
                        raise Unsupported("unary operator returning a reference")
                    info = self.tr.classes[ty.name]
                    if (set(info.tparams) - info.value_params.keys()
                            or set(sig.tparams) - sig.value_params.keys()):
                        raise Unsupported("class unary operator with type template parameters")
                    if sig.owner:
                        if sig.owner != ty.name or not sig.is_const or sig.params:
                            raise Unsupported("unary member operator needs a const receiver")
                        return self.call_sig(sig, t, [], pre, owner_ty=ty)
                    return self.call_sig(sig, None, args, pre, evaluated_args=[(t, ty)])
                if op != "-":
                    raise Unsupported("non-class overloaded unary operator")
                if ty.kind == "tparam":
                    self.need("Neg", ty)
                return f"(-{t})", ty
            raise Unsupported(f"operator {op}")
        if kind == "ConditionalOperator":
            c, t, e = inner(n)
            sub_pre_t, sub_pre_e = [], []
            ct, _ = self.expr(c, pre, BOOL)
            tt, tty = self.expr(t, sub_pre_t)
            if not sub_pre_t and expected is not None and expected.kind == "tparam" and tty.kind == "tparam":
                e_ast = strip(e)
                type_text = e_ast.get("type", {}).get("qualType", "")
                right_type = type_text if type_text in self.sig.tparams or (
                    self.cls is not None and type_text in self.cls.tparams) else None
                if right_type and right_type != tty.name:
                    et, ety = self.expr(e, sub_pre_e)
                    if sub_pre_e:
                        raise Unsupported("a call inside a conditional operator branch")
                    left, right = lean_type(tty), lean_type(ety)
                    self.reqs.add(f"Cpp.ConditionalResult {left} {right}")
                    return (f"(if {ct} then Cpp.ConditionalResult.left (Right := {right}) {tt} "
                            f"else Cpp.ConditionalResult.right (Left := {left}) {et})",
                            Ty("conditional_result", args=(tty, ety)))
            if sub_pre_t and tty.kind == "tparam" and strip(e).get("type", {}).get("qualType") == "int":
                et, ety = self.expr(e, sub_pre_e)
                left, right = lean_type(tty), lean_type(ety)
                self.reqs.add(f"Cpp.ConditionalResult {left} {right}")
                tt = f"(Cpp.ConditionalResult.left (Right := {right}) {tt})"
                et = f"(Cpp.ConditionalResult.right (Left := {left}) {et})"
                tty = Ty("conditional_result", args=(tty, ety))
            else:
                et, ety = self.expr(e, sub_pre_e, tty if tty.kind != "int" else None)
                if tty != ety:
                    tt, tty = self.convert(tt, tty, ety, t)
            if sub_pre_t or sub_pre_e:
                def optional_branch(steps, value):
                    if any(not re.match(r"let \w+ ← Cpp\.optionalValue ", step) for step in steps):
                        raise Unsupported("effectful conditional operator branch")
                    return "(do " + "; ".join([*steps, f"pure {value}"]) + ")"

                result = self.fresh()
                pre.append(f"let {result} ← if {ct} then {optional_branch(sub_pre_t, tt)} "
                           f"else {optional_branch(sub_pre_e, et)}")
                return result, tty
            return f"(if {ct} then {tt} else {et})", tty
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            return self.call(n, pre, expected)
        if kind in ("CXXConstructExpr", "ParenListExpr", "CXXTemporaryObjectExpr", "InitListExpr",
                    "CXXUnresolvedConstructExpr", "CXXScalarValueInitExpr"):
            if expected is None:
                if kind == "CXXUnresolvedConstructExpr" or kind == "CXXTemporaryObjectExpr":
                    expected = self.tr.ty(n["type"]["qualType"], self)
                elif kind == "CXXConstructExpr":
                    expected = self.tr.ty(n["type"]["qualType"], self)
                else:
                    raise Unsupported(f"{kind} without a known type")
            return self.construct(expected, n, pre), expected
        raise Unsupported(f"expression {kind}")

    def operator_name(self, n):
        callee = strip(inner(n)[0])
        name = callee.get("referencedDecl", {}).get("name", "")
        if not name and callee.get("kind") == "UnresolvedLookupExpr":
            name = callee.get("name", "")
        return name.removeprefix("operator")

    def pq_order(self, bty):
        """The comparison `comp a b` of a priority_queue (its top has no `b` with `comp top b`)."""
        elem = bty.args[0]
        def lt(t):
            if t.kind == "pair":
                return f"(Cpp.pairLt {lt(t.args[0])} {lt(t.args[1])})"
            if t.kind not in ("int", "u32", "u64", "tparam"):
                raise Unsupported(f"priority_queue element {t}")
            self.need("LT", t)
            self.need("DecidableLT", t)
            return f"(fun a b : {lean_type(t)} => decide (a < b))"
        base = lt(elem)
        return base if bty.name == "less" else f"(fun a b => {base} b a)"

    def ordered_set_deref(self, node, pre):
        call = strip(node)
        if call.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or len(inner(call)) != 1:
            return None
        callee = strip(inner(call)[0])
        if callee.get("kind") not in ("MemberExpr", "CXXDependentScopeMemberExpr") or not inner(callee):
            return None
        name = callee.get("name") or callee.get("member")
        if name not in ("begin", "rbegin"):
            return None
        before = []
        base, ty = self.expr(inner(callee)[0], before)
        if ty.kind != "ordered_set":
            return None
        pre.extend(before)
        fn = "orderedSetFirst" if name == "begin" else "orderedSetLast"
        tmp = self.fresh()
        pre.append(f"let {tmp} ← Cpp.{fn} {base}")
        return tmp, ty.args[0]

    def construct_call(self, elem, texts, tys, pre):
        """`Cpp.Construct.make` of the class type parameter `elem` on the tuple `texts`; updates the state."""
        tuple_text = "(" + ", ".join(texts) + ")" if len(texts) > 1 else texts[0]
        tuple_ty = " × ".join(tys)
        self.reqs.add(f"Cpp.ConstructState {lean_type(elem)}")
        self.reqs.add(f"Cpp.Construct {lean_type(elem)} ({tuple_ty})")
        state = self.var_name(CONSTRUCT_STATE)
        tmp = self.fresh()
        pre.append(f"let {tmp} ← Cpp.Construct.make (E := {lean_type(elem)}) (Args := {tuple_ty}) {tuple_text} {state}")
        pre.append(f"{state} := {tmp}.2")
        return f"{tmp}.1"

    def umap_value_ok(self, vty):
        # The model inserts `default`, which is the C++ value-initialization only for these types.
        if not (vty.kind == "int" or (vty.kind == "vec" and vty.length is None)):
            raise Unsupported("unordered_map value other than a signed integer or a vector")
        self.need("Inhabited", vty)

    def moved_local(self, rhs, statement):
        """`std::move(x)` of a local variable that the function does not use again: its value."""
        r = strip(rhs)
        if r.get("kind") != "CallExpr" or len(inner(r)) != 2:
            return None
        callee = strip(inner(r)[0])
        name = callee.get("name") or callee.get("referencedDecl", {}).get("name")
        if name != "move" or not re.match(r"std::move\b", re.sub(r"\s+", "", self.tr.span(r))):
            return None
        arg = strip(inner(r)[1])
        key = arg.get("referencedDecl", {}).get("id")
        if arg.get("kind") != "DeclRefExpr" or key is None:
            raise Unsupported("std::move of something other than a local variable")
        end = statement.get("range", {}).get("end", {}).get("offset")
        def later(x):
            if not isinstance(x, dict):
                return False
            if (x.get("kind") == "DeclRefExpr" and x.get("referencedDecl", {}).get("id") == key
                    and x.get("range", {}).get("begin", {}).get("offset", -1) > end):
                return True
            return any(later(c) for c in inner(x))
        if end is None or later(self.sig.node):
            raise Unsupported("a moved-from variable is used again")
        return arg

    def umap_store(self, statement, lhs, rhs, pre):
        """`m[k] = e` for an unordered_map lvalue `m` (Cpp.umapSet). Returns False for other targets."""
        lh = strip(lhs)
        if not (lh.get("kind") == "ArraySubscriptExpr"
                or (lh.get("kind") == "CXXOperatorCallExpr" and self.operator_name(lh) == "[]")):
            return False
        base, index = self.subscript_parts(lh)
        probe = []
        try:
            _, bty = self.expr(base, probe)
        except Unsupported:
            return False
        if bty.kind != "umap":
            return False
        target = self.lvalue(base)
        if target[1]:
            raise Unsupported("subscript of an unordered_map inside another object")
        self.umap_value_ok(bty.args[1])
        it, _ = self.expr(index, pre, INT)
        moved = self.moved_local(rhs, statement)
        value, vty = self.expr(moved if moved is not None else rhs, pre, bty.args[1])
        if vty.kind == "vec" and moved is None and self.is_lvalue_vector(rhs):
            pre.append(f"Cpp.tickN {value}.size")
        tmp = self.fresh()
        pre.append(f"let {tmp} ← Cpp.umapSet {self.read_lvalue(target)} {it} {value}")
        self.flush(pre)
        for line in self.assign_lines(target, tmp):
            self.emit(line)
        return True

    def default_field_type(self, bty, member, *, for_write=False):
        """The type of `x.member` for a value of a class type parameter whose default argument is a dependency class
        template (`class E = Edge<Cost>`): the member's type in that class with the default's arguments."""
        if bty.kind != "tparam" or not self.tr.tparam_defaults.get(bty.name):
            return None
        m = re.fullmatch(r"(?:cp::)?(\w+)\s*(?:<(.*)>)?", self.tr.tparam_defaults[bty.name].strip())
        if not m or m.group(1) not in self.tr.dep_layouts:
            return None
        dtps, fields = self.tr.dep_layouts[m.group(1)]
        if member not in fields:
            return None
        if for_write and re.search(r"\b(const|volatile)\b|&", fields[member]):
            raise Unsupported("dependent assignment needs a writable value member")
        args = split_args(m.group(2)) if m.group(2) else []
        if len(args) != len(dtps):
            raise Unsupported("default class argument needs every template argument")
        tps = set(self.sig.tparams) | set(self.cls.tparams if self.cls else [])
        arg_tys = [parse_type(a, tps, self.tr.classes, aliases=self.tr.aliases) for a in args]
        fty = parse_type(fields[member], set(dtps), self.tr.classes, aliases=self.tr.aliases)
        return subst(fty, dtps, arg_tys)

    def subscript_parts(self, n):
        if n.get("kind") == "ArraySubscriptExpr":
            a, b = inner(n)
            return a, b
        return inner(n)[1], inner(n)[2]

    def binary(self, n, pre):
        op = n["opcode"]
        a, b = inner(n)
        if op in ("=", ",") or op.endswith("=") and op not in ("==", "!=", "<=", ">="):
            raise Unsupported(f"assignment {op} inside an expression")
        return self.binary_parts(op, a, b, pre)

    def binary_parts(self, op, a, b, pre, callee=None):
        if op in ("&&", "||"):
            at, _ = self.expr(a, pre, BOOL)
            rpre = []
            bt, _ = self.expr(b, rpre, BOOL)
            if rpre:
                raise Unsupported("a call on the right of && or ||")
            return f"({at} {op} {bt})", BOOL
        at, aty = self.expr(a, pre)
        if aty.kind in ("istream", "ostream"):
            return self.stream_shift(op, a, at, aty, b, pre)
        bt, bty = self.expr(b, pre)
        if op == "*" and {aty.kind, bty.kind} == {"int", "tparam"}:
            count = a if aty.kind == "int" else b
            if strip(count).get("kind") == "CXXDependentScopeMemberExpr":
                self.reqs.add(f"Cpp.MulResult {lean_type(aty)} {lean_type(bty)}")
                return f"(Cpp.MulResult.mul {at} {bt})", Ty("mul_result", args=(aty, bty))
        if op == "+" and ((aty.kind == "field_value" and bty.kind == "tparam")
                          or (aty.kind == "tparam" and bty.kind == "mul_result")):
            self.reqs.add(f"Cpp.AddResult {lean_type(aty)} {lean_type(bty)}")
            return f"(Cpp.AddResult.add {at} {bt})", Ty("add_result", args=(aty, bty))
        if aty.kind == "cls" or bty.kind == "cls":
            return self.class_binary(op, a, at, aty, b, bt, bty, pre, callee)
        return self.arith(op, at, aty, a, bt, bty, b)

    def class_binary(self, op, a, at, aty, b, bt, bty, pre, callee):
        name = "operator" + op
        reference = callee.get("referencedDecl") if callee else None
        if reference is not None:
            sig = self.tr.resolve_function(reference["id"])
            if sig.cpp_name != name:
                raise Unsupported("binary operator declaration mismatch")
        else:
            # With only value parameters, the associated types cannot introduce
            # an unknown namespace through a type template argument. Still reject
            # every competing member/free declaration rather than rank it here.
            if aty.kind != "cls" or bty.kind != "cls" or aty.name != bty.name:
                raise Unsupported("unresolved binary operator needs the same class operands")
            info = self.tr.classes[aty.name]
            # With type parameters, argument-dependent lookup also searches their namespaces, but the hidden friend
            # below is a non-template exact match: a competing exact match there would make the call ambiguous (a
            # compile error), and templates lose to it, so the selection cannot change silently.
            if any(s.cpp_name == name for s in info.methods):
                raise Unsupported("unresolved binary operator has member candidates")
            candidates = self.tr.functions.get(name, [])
            if len(candidates) != 1:
                raise Unsupported("unresolved binary operator has competing free candidates")
            sig = candidates[0]
            if (not sig.node.get("lean_hidden_friend") or len(sig.params) != 2
                    or any(t.kind != "cls" or t.name != aty.name for _, t, _ in sig.params)):
                raise Unsupported("unresolved binary operator is not the class hidden friend")
        if set(sig.tparams) - sig.value_params.keys() and not (
                sig.node.get("lean_hidden_friend") and aty.kind == "cls" and aty == bty
                and set(sig.tparams) <= set(self.sig.tparams) | set(self.cls.tparams if self.cls else [])
                and all(a == Ty("tparam", p) or p in sig.value_params
                        for p, a in zip(self.tr.classes[aty.name].tparams, aty.args))):
            raise Unsupported("binary operator with type template parameters")
        if sig.mut_refs:
            raise Unsupported("binary operator with mutable reference operands")
        if sig.owner:
            if aty.kind != "cls" or sig.owner != aty.name or not sig.is_const:
                raise Unsupported("binary member operator needs a const receiver")
            owner = self.tr.classes[sig.owner]
            if set(owner.tparams) - owner.value_params.keys():
                raise Unsupported("binary member operator with type template parameters")
            return self.call_sig(sig, at, [b], pre, owner_ty=aty, evaluated_args=[(bt, bty)])
        return self.call_sig(sig, None, [a, b], pre, evaluated_args=[(at, aty), (bt, bty)])

    def stream_base(self, node):
        n = strip(node)
        if n.get("kind") == "BinaryOperator" and n.get("opcode") in ("<<", ">>"):
            return self.stream_base(inner(n)[0])
        if n.get("kind") == "CXXOperatorCallExpr" and self.operator_name(n) in ("<<", ">>"):
            return self.stream_base(inner(n)[1])
        return n

    def stream_shift(self, op, left, stream, sty, right, pre):
        self.reqs.add("Cpp.Streams")
        receiver = self.lvalue(self.stream_base(left))
        if sty.kind == "istream" and op == ">>":
            target = self.lvalue(right)
            ty = target[3]
            operation = "Cpp.StreamRead.read"
            source_arg = ""
            if ty.kind == "tparam":
                self.reqs.add(f"Cpp.StreamRead {lean_type(ty)}")
            else:
                source, carrier = source_stream_type(right)
                if carrier != ty:
                    raise Unsupported("stream source type and carrier disagree")
                self.reqs.add(f'Cpp.SourceStreamRead "{source}" {lean_type(ty)}')
                operation = "Cpp.SourceStreamRead.read"
                source_arg = f' (source := "{source}")'
            tmp = self.fresh()
            pre.append(f"let {tmp} ← {operation}{source_arg} {stream} {self.read_lvalue(target)}")
            pre.extend(self.assign_lines(target, f"{tmp}.1"))
            pre.extend(self.assign_lines(receiver, f"{tmp}.2"))
        elif sty.kind == "ostream" and op == "<<":
            before_value = len(pre)
            value, ty = self.expr(right, pre)
            operation = "Cpp.StreamWrite.write"
            source_arg = ""
            if strip(right).get("kind") == "CharacterLiteral" and \
                    strip(right).get("type", {}).get("qualType") == "char":
                value = f"(⟨{value}⟩ : Cpp.StreamChar)"
                self.reqs.add("Cpp.StreamWrite Cpp.StreamChar")
            else:
                optional_read = (len(pre) == before_value + 1
                                 and re.fullmatch(r"let \w+ ← Cpp\.optionalValue .+", pre[-1]))
                if (strip(right).get("kind") not in
                    ("DeclRefExpr", "MemberExpr", "CXXDependentScopeMemberExpr", "ArraySubscriptExpr")
                        and not optional_read):
                    raise Unsupported("stream insertion needs a typed template value or a character literal")
                if ty.kind == "tparam":
                    self.reqs.add(f"Cpp.StreamWrite {lean_type(ty)}")
                else:
                    source, carrier = source_stream_type(right)
                    if carrier != ty:
                        raise Unsupported("stream source type and carrier disagree")
                    self.reqs.add(f'Cpp.SourceStreamWrite "{source}" {lean_type(ty)}')
                    operation = "Cpp.SourceStreamWrite.write"
                    source_arg = f' (source := "{source}")'
            tmp = self.fresh()
            pre.append(f"let {tmp} ← {operation}{source_arg} {stream} {value}")
            pre.extend(self.assign_lines(receiver, tmp))
        else:
            raise Unsupported(f"stream operation {op} on {sty}")
        return self.read_lvalue(receiver), sty

    def common_type(self, aty, bty):
        """C++'s usual arithmetic conversions on the modelled types."""
        if aty.kind == "tparam" or bty.kind == "tparam":
            if aty.kind == "tparam" and bty.kind == "tparam" and aty != bty:
                raise Unsupported(f"operands {aty} and {bty}")
            return aty if aty.kind == "tparam" else bty
        def promote(t):
            return INT32 if t.kind == "bool" else t
        aty, bty = promote(aty), promote(bty)
        for t in (aty, bty):
            if t.kind not in ("int", "u32", "u64"):
                raise Unsupported(f"arithmetic on {t}")
        if aty.kind == bty.kind == "int":
            return Ty("int", width=max(aty.width, bty.width))
        if "u64" in (aty.kind, bty.kind):
            other = bty if aty.kind == "u64" else aty
            return Ty("int", width=128) if other.kind == "int" and other.width > 64 else U64
        other = bty if aty.kind == "u32" else aty
        if other.kind == "int" and other.width > 32:
            return other
        return U32

    def arith(self, op, at, aty, a, bt, bty, b):
        if op in ("<<", ">>"):
            ty = INT32 if aty.kind == "bool" else aty
            if ty.kind in ("u32", "u64"):
                bt, _ = self.convert(bt, bty, ty, b)
                return f"({at} {'<<<' if op == '<<' else '>>>'} {bt})", ty
            if ty.kind == "tparam":
                bt, _ = self.convert(bt, bty, INT, b)
                self.reqs.add(f"Cpp.ShiftInt {lean_type(ty)}")
                return f"(Cpp.ShiftInt.{'shl' if op == '<<' else 'shr'} {at} {bt})", ty
            if ty.kind != "int":
                raise Unsupported(f"shift of {ty}")
            bt, _ = self.convert(bt, bty, INT, b)
            return f"(Cpp.{'shl' if op == '<<' else 'shr'} {at} {bt})", ty
        if aty.kind == bty.kind == "tparam" and aty != bty and op in ("<", ">"):
            # `a < b` on two template parameters S, T: the operator of the instance (Cpp.HLt S T)
            x, y, xt, yt = (at, bt, aty, bty) if op == "<" else (bt, at, bty, aty)
            self.reqs.add(f"Cpp.HLt {xt.name} {yt.name}")
            return f"(Cpp.HLt.hlt {x} {y})", BOOL
        if aty.kind == bty.kind == "bool" and op in ("==", "!="):
            ty = BOOL
        else:
            ty = self.common_type(aty, bty)
        at, _ = self.convert(at, aty, ty, a)
        bt, _ = self.convert(bt, bty, ty, b)
        if op == "<=>":
            self.need("LT", ty)
            self.need("DecidableLT", ty)
            return f"(if {at} < {bt} then Ordering.lt else if {bt} < {at} then Ordering.gt else Ordering.eq)", ORDERING
        arith = {"+": "Add", "-": "Sub", "*": "Mul"}
        if op in arith:
            if ty.kind == "tparam":
                self.need(arith[op], ty)
            return f"({at} {op} {bt})", ty
        if op in ("/", "%"):
            if ty.kind == "int":
                return f"(Cpp.{'div' if op == '/' else 'mod'} {at} {bt})", ty
            if ty.kind == "tparam":
                self.need("Div" if op == "/" else "Mod", ty)
            return f"({at} {op} {bt})", ty
        if op in ("&", "|", "^"):
            if ty.kind in ("u32", "u64"):
                return f"({at} {dict(zip('&|^', ['&&&', '|||', '^^^']))[op]} {bt})", ty
            if ty.kind != "int":
                raise Unsupported(f"bit operation on {ty}")
            fn = {"&": "land", "|": "lor", "^": "lxor"}[op]
            return f"(Cpp.{fn} {at} {bt})", ty
        if op in ("<", ">", "<=", ">="):
            if ty.kind == "tparam":
                self.need("LT" if op in ("<", ">") else "LE", ty)
                self.need("DecidableLT" if op in ("<", ">") else "DecidableLE", ty)
            sym = {"<": "<", ">": ">", "<=": "≤", ">=": "≥"}[op]
            return f"(decide ({at} {sym} {bt}))", BOOL
        if op in ("==", "!="):
            if ty.kind in ("tparam",):
                self.need("DecidableEq", ty)
            sym = "=" if op == "==" else "≠"
            return f"(decide ({at} {sym} {bt}))", BOOL
        raise Unsupported(f"binary {op}")

    # ------------------------------------------------------------------ variables and fields
    def var_name(self, name):
        depth = self.scope_of(name)
        if self.cls is not None and name in self.field_names and depth == 0 and \
                name not in {p[0] for p in self.sig.params}:
            return self.field_names[name]
        if depth is not None:
            return self.scopes[depth].get("__names__", {}).get(name, lean_name(name))
        return lean_name(name)

    def scope_of(self, name):
        for depth in range(len(self.scopes) - 1, -1, -1):
            if name in self.scopes[depth]:
                return depth
        return None

    def field_ref(self, name):
        if self.cls is None:
            raise Unsupported("this outside a class")
        for fname, fty, _ in self.cls.fields:
            if fname == name:
                return self.field_names[fname], fty
        raise Unsupported(f"unknown field {name}")

    def self_value(self):
        if not self.cls.fields:
            return "({} : " + self.cls_type() + ")"
        return "(⟨" + ", ".join(self.field_names[f] for f, _, _ in self.cls.fields) + "⟩ : " + self.cls_type() + ")"

    def cls_type(self):
        return lean_type(class_ty(self.cls))

    # ------------------------------------------------------------------ construction
    def tuple_value(self, ty: Ty, args, pre) -> str:
        values = []
        for arg, item_ty in zip(args, ty.args, strict=True):
            before_arg = len(pre)
            moved = self.moved_local(arg, arg)
            value, _ = self.expr(moved or arg, pre, item_ty)
            if any(not re.match(r"let \w+ ← Cpp\.optionalValue ", step) for step in pre[before_arg:]):
                raise Unsupported("effects in tuple constructor arguments")
            if item_ty.kind == "vec" and self.is_lvalue_vector(arg):
                tmp = self.fresh()
                pre.append(f"let {tmp} := {value}")
                pre.append(f"Cpp.tickN {tmp}.size")
                value = tmp
            values.append(value)
        return "(" + ", ".join(values) + ")"

    def construct(self, ty: Ty, n, pre):
        kind = n.get("kind")
        args = [a for a in inner(n) if strip(a).get("kind") not in ("CXXDefaultArgExpr",)]
        if ty.kind in ("pq", "stack", "queue", "umap", "ordered_set") and not args and kind in ("CXXConstructExpr", "InitListExpr"):
            return self.default_value(ty)   # an empty container
        if ty.kind == "optional":
            if kind not in ("InitListExpr", "CXXConstructExpr", "ParenListExpr",
                            "CXXTemporaryObjectExpr", "CXXUnresolvedConstructExpr"):
                raise Unsupported("optional construction")
            if not args:
                return self.default_value(ty)
            if len(args) == 1:
                value, actual = self.expr(args[0], pre)
                if actual == ty:
                    return value
                value, _ = self.convert(value, actual, ty.args[0], args[0])
                return f"(some {value})"
            raise Unsupported("optional constructor arity")
        if ty.kind == "deque":
            if not args and kind in ("InitListExpr", "CXXConstructExpr", "ParenListExpr", "CXXUnresolvedConstructExpr"):
                return self.default_value(ty)
            raise Unsupported("deque construction")
        if ty.kind == "ordered_set" and not args and kind == "ParenListExpr":
            return self.default_value(ty)
        if ty.kind == "tuple":
            if kind not in ("InitListExpr", "CXXConstructExpr", "ParenListExpr") or len(args) != len(ty.args):
                raise Unsupported("tuple construction requires one argument per value element")
            return self.tuple_value(ty, args, pre)
        if kind == "InitListExpr" and ty.kind == "cls":
            sigs = [s for s in self.tr.classes[ty.name].methods if s.is_ctor]
            sig = self.pick(sigs, args, f"list constructor of {ty.name}")
            if re.search(r"\bexplicit\b", self.tr.span(sig.node)):
                raise Unsupported("explicit constructor in record list conversion")
            return self.call_sig(sig, None, args, pre, ty)[0]
        if kind == "InitListExpr":
            if ty.kind == "vec":
                items = [self.expr(a, pre, ty.args[0])[0] for a in args]
                return "([" + ", ".join(items) + f"] : List {lean_type(ty.args[0])}).toArray"
            if ty.kind == "pair" and len(args) == 2:
                a = self.expr(args[0], pre, ty.args[0])[0]
                b = self.expr(args[1], pre, ty.args[1])[0]
                return f"({a}, {b})"
            if ty.kind == "tparam" and self.lookup(CONSTRUCT_STATE) is not None:
                # `E{a, b}` of a class type parameter: E's constructor on (a, b, ()) (the argument tuple always ends
                # with the forwarded pack, empty here), through Cpp.Construct.
                texts, tys = [], []
                for a in args:
                    at, aty = self.expr(a, pre)
                    texts.append(at)
                    tys.append(lean_type(aty))
                return self.construct_call(ty, texts + ["()"], tys + ["Unit"], pre)
            raise Unsupported(f"initializer list for {ty}")
        if kind == "CXXScalarValueInitExpr":
            return self.default_value(ty)
        if len(args) == 1 and kind in ("ParenListExpr",) and strip(args[0]).get("kind") == "ParenListExpr":
            args = inner(strip(args[0]))
        if ty.kind == "vec":
            if not args:
                return f"([] : List {lean_type(ty.args[0])}).toArray"
            if len(args) == 1:
                at, aty = self.expr(args[0], pre)
                if aty.kind == "vec":
                    tmp = self.fresh()
                    pre.append(f"let {tmp} := {at}")
                    pre.append(f"Cpp.tickN {tmp}.size")
                    return tmp
                at, _ = self.convert(at, aty, INT, args[0])
                tmp = self.fresh()
                pre.append(f"let {tmp} := {at}")
                pre.append(f"Cpp.tickN {tmp}.toNat")
                return f"(Cpp.replicate {tmp} {self.default_value(ty.args[0])})"
            if len(args) == 2:
                at, _ = self.expr(args[0], pre, INT)
                vt, _ = self.expr(args[1], pre, ty.args[0])
                tmp = self.fresh()
                pre.append(f"let {tmp} := {at}")
                if ty.args[0].kind == "vec":
                    # n copies of a vector value: n * (its length) element copies
                    val = self.fresh()
                    pre.append(f"let {val} := {vt}")
                    pre.append(f"Cpp.tickN ({tmp}.toNat * ({val}.size + 1))")
                    return f"(Cpp.replicate {tmp} {val})"
                pre.append(f"Cpp.tickN {tmp}.toNat")
                return f"(Cpp.replicate {tmp} {vt})"
            raise Unsupported("vector constructor")
        if ty.kind in ("int", "u32", "u64", "bool", "tparam"):
            if not args:
                return self.default_value(ty)
            if len(args) == 1:
                return self.expr(args[0], pre, ty)[0]
        if ty.kind == "pair":
            if not args:
                return self.default_value(ty)
            if len(args) == 2:
                a = self.expr(args[0], pre, ty.args[0])[0]
                b = self.expr(args[1], pre, ty.args[1])[0]
                return f"({a}, {b})"
        if ty.kind == "cls":
            if len(args) == 1:
                type_info = strip(args[0]).get("type", {})
                spelling = type_info.get("qualType", "")
                canonical = type_info.get("desugaredQualType")
                if spelling in ("value_type", "const value_type") and canonical:
                    # Clang spells a std::vector element as value_type at
                    # the copy site. The canonical type must match exactly.
                    if self.tr.ty(canonical, self) != ty:
                        raise Unsupported("record copy has a different canonical type")
                    argty = ty
                else:
                    argty = None if spelling in ("<dependent type>", "NULL TYPE") else self.tr.ty(spelling, self)
                if argty == ty:
                    if any(s.is_ctor and s.tparams
                           and any(p.get("kind") == "ParmVarDecl" and "&" in type_of_decl(p)
                                   for p in inner(s.node))
                           for s in self.tr.classes[ty.name].methods):
                        # A forwarding/non-const reference template can beat the
                        # implicit copy constructor. Do not erase that selection.
                        raise Unsupported("record copy competing with a reference template constructor")
                    copies = [s for s in self.tr.classes[ty.name].methods if s.is_ctor and len(s.params) == 1
                              and s.params[0][1] == ty]
                    if copies:
                        if len(copies) != 1:
                            raise Unsupported("ambiguous record copy")
                        raise Unsupported("user-defined record copy constructor")
                    def carray_cells(fty):
                        # The number of scalar cells of a fixed-size C array member, or None.
                        if fty.kind in ("int", "u32", "u64", "bool", "tparam"):
                            return []
                        if fty.kind == "vec" and fty.length is not None:
                            inner_cells = carray_cells(fty.args[0])
                            if inner_cells is None:
                                return None
                            n = lean_name(fty.length.name) if fty.length.kind == "vparam" else fty.length.name
                            return [f"({n} : Int).toNat"] + inner_cells
                        return None
                    cells = []
                    for _, fty, _ in self.tr.classes[ty.name].fields:
                        c = carray_cells(subst(fty, list(self.tr.classes[ty.name].tparams), list(ty.args)))
                        if c is None:
                            raise Unsupported("implicit record copy with non-scalar fields")
                        if c:
                            cells.append(" * ".join(c))
                    # Implicit record copy (scalars and C arrays, element by element), not a converting constructor.
                    value = self.expr(args[0], pre, ty)[0]
                    if cells:
                        pre.append(f"Cpp.tickN ({' + '.join(cells)})")
                    return value
            sigs = [s for s in self.tr.classes[ty.name].methods if s.is_ctor]
            return self.call_sig(self.pick(sigs, args, f"constructor of {ty.name}"), None, args, pre, ty)[0]
        raise Unsupported(f"construct {ty}")

    def default_value(self, ty: Ty):
        if ty.kind == "int":
            return "(0 : Int)"
        if ty.kind in ("u32", "u64"):
            return f"(0 : {lean_type(ty)})"
        if ty.kind == "bool":
            return "false"
        if ty.kind == "tparam":
            self.need("Inhabited", ty)
            return f"(default : {ty.name})"
        if ty.kind == "vec" and ty.length is not None:
            # A C array member: its elements are default-initialized (the model starts from the default value;
            # the C++ value of a scalar is indeterminate, so a component must write an element before reading it).
            n = lean_name(ty.length.name) if ty.length.kind == "vparam" else ty.length.name
            return f"(Cpp.replicate ({n} : Int) {self.default_value(ty.args[0])})"
        if ty.kind in ("vec", "deque"):
            return f"([] : List {lean_type(ty.args[0])}).toArray"
        if ty.kind == "optional":
            return f"(_root_.Option.none : {lean_type(ty)})"
        if ty.kind in ("umap", "pq", "stack", "queue", "ordered_set"):
            return f"([] : {lean_type(ty)})"
        if ty.kind == "pair":
            return f"({self.default_value(ty.args[0])}, {self.default_value(ty.args[1])})"
        if ty.kind == "cls" and ty.name in self.tr.classes:
            # The implicit default constructor of a class without user constructors and without default member
            # initializers: every member is default-initialized.
            info = self.tr.classes[ty.name]
            if any(m.is_ctor for m in info.methods) or any(init is not None for _, _, init in info.fields):
                raise Unsupported(f"default value of {ty}")
            values = [self.default_value(subst(fty, list(info.tparams), list(ty.args))) for _, fty, _ in info.fields]
            return f"(⟨{', '.join(values)}⟩ : {lean_type(ty)})"
        raise Unsupported(f"default value of {ty}")

    # ------------------------------------------------------------------ calls
    def trait_packets(self, sig, args):
        parameters = {p for c in sig.constraints
                      for p in re.findall(r'Cpp\.TypeTraits\.\w+ \(tag := "(\w+)"\)', c)}
        packets = {}
        for (_, formal, _), arg in zip(sig.params, args):
            if formal.kind == "tparam" and formal.name in parameters:
                cpp = strip(arg).get("type", {}).get("qualType", "")
                flags = known_type_traits(cpp)
                packet = (cpp, *flags)
                if formal.name in packets and packets[formal.name][1:] != packet[1:]:
                    raise Unsupported("conflicting type trait deductions")
                packets[formal.name] = packet
        if parameters - packets.keys():
            raise Unsupported("cannot deduce type traits for this constrained call")
        return packets

    def trait_eligibility(self, sig, args):
        if not sig.constraints or any("Cpp.TypeTraits." not in c for c in sig.constraints):
            return None
        try:
            packets = self.trait_packets(sig, args)
        except Unsupported:
            return None
        for condition in sig.constraints:
            parameter = re.search(r'\(tag := "(\w+)"\)', condition)[1]
            _, signed, int128 = packets[parameter]
            value = signed or ("Cpp.TypeTraits.isCvInt128" in condition and int128)
            if value != condition.endswith("= true)"):
                return False
        return True

    def pick(self, sigs, args, what):
        cands = [s for s in sigs if len(s.params) == len(args)
                 and self.trait_eligibility(s, args) is not False]
        if len(cands) > 1:
            collection_kinds = {"vec", "string"}
            for i, arg in enumerate(args):
                formal_kinds = {sig.params[i][1].kind for sig in cands}
                if formal_kinds != collection_kinds:
                    continue
                actual = self.tr.ty(strip(arg)["type"]["qualType"], self)
                if actual.kind in collection_kinds:
                    cands = [sig for sig in cands if sig.params[i][1].kind == actual.kind]
                    if len(cands) == 1:
                        break
        if len(cands) > 1:
            # Discard candidates whose parameter is a collection or record when the argument is a known scalar
            # (and the converse): no implicit conversion connects them.
            aggregate = {"vec", "string", "cls", "pair"}
            for i, arg in enumerate(args):
                qual = strip(arg).get("type", {}).get("qualType", "")
                if not qual or "dependent" in qual or qual == "NULL TYPE":
                    continue
                try:
                    actual = self.tr.ty(qual, self)
                except Unsupported:
                    continue
                if actual.kind in ("unknown", "tparam"):
                    continue
                kept = [sig for sig in cands if (sig.params[i][1].kind in aggregate) == (actual.kind in aggregate)]
                if kept:
                    cands = kept
                if len(cands) == 1:
                    break
        if len(cands) != 1:
            cands2 = [s for s in sigs if len(s.params) >= len(args)
                      and all(self.has_default(s, i) for i in range(len(args), len(s.params)))
                      and self.trait_eligibility(s, args) is not False]
            if len(cands2) == 1:
                return cands2[0]
            raise Unsupported(f"cannot resolve {what} with {len(args)} argument(s)")
        return cands[0]

    def has_default(self, sig, i):
        return False

    def call(self, n, pre, expected=None):
        kids = inner(n)
        callee = strip(kids[0])
        args = [a for a in kids[1:] if strip(a).get("kind") != "CXXDefaultArgExpr"]
        ck = callee.get("kind")
        # method calls: obj.f(args) / this->f(args)
        if ck in ("MemberExpr", "CXXDependentScopeMemberExpr"):
            name = callee.get("name") or callee.get("member")
            if not name.startswith("operator") and self.tr.span(callee).rstrip().endswith(">"):
                raise Unsupported("explicit member template arguments")
            base = strip(inner(callee)[0]) if inner(callee) else None
            if base is None or base.get("kind") == "CXXThisExpr":
                return self.self_call(name, args, pre)
            return self.method_call(base, name, args, pre)
        if ck == "UnresolvedMemberExpr":
            if self.tr.span(callee).rstrip().endswith(">"):
                raise Unsupported("explicit member template arguments")
            name = callee.get("name") or self.tr.member_token(callee)
            base = strip(inner(callee)[0]) if inner(callee) else None
            if base is None or base.get("kind") == "CXXThisExpr":
                return self.self_call(name, args, pre)
            return self.method_call(base, name, args, pre)
        if ck in ("DeclRefExpr", "UnresolvedLookupExpr"):
            name = callee.get("referencedDecl", {}).get("name") if ck == "DeclRefExpr" else callee.get("name")
            if not name:
                name = self.tr.token(callee)
            if ck == "DeclRefExpr" and callee.get("referencedDecl", {}).get("kind") == "CXXMethodDecl":
                # Resolve the actual declaration, not just its spelling: a global
                # function or another class can have the same name.
                ref_id = callee["referencedDecl"].get("id")
                methods = [] if self.cls is None else [
                    s for s in self.cls.methods if s.node.get("id") == ref_id and s.is_static]
                if len(methods) == 1:
                    return self.call_sig(methods[0], None, args, pre)
                if self.cls is not None and any(s.cpp_name == name for s in self.cls.methods):
                    raise Unsupported(f"static member declaration outside the current class: {name}")
                # Established standard contracts (e.g. numeric_limits::max)
                # still go through the explicitly checked free-call handler.
            if ck == "UnresolvedLookupExpr" and callee.get("usesADL") and not callee.get("lookups"):
                return self.adl_call(name, args, pre, expected)
            if ck == "DeclRefExpr" and callee.get("referencedDecl", {}).get("kind") in ("ParmVarDecl", "VarDecl"):
                fty = self.lookup(name)
                if fty is not None and fty.kind == "tparam":
                    return self.invoke_call(name, fty, args, pre, expected)
            return self.free_call(name, args, pre, callee, n)
        if ck == "DependentScopeDeclRefExpr":
            return self.policy_call(callee, args, pre, expected)
        raise Unsupported(f"call {ck}")

    def numeric_trait(self, parameter, member, result_ty):
        own = set(self.sig.tparams) | (set(self.cls.tparams) if self.cls else set())
        if parameter not in own:
            raise Unsupported(f"numeric traits of non-parameter {parameter}")
        self.reqs.add(f'Cpp.NumericTraits "{parameter}" {parameter}')
        return f'(Cpp.NumericTraits.{member} (tag := "{parameter}") (α := {parameter}))', result_ty

    def policy_call(self, callee, args, pre, expected):
        """`P::f(args)` for a template parameter `P` (a policy class with static members): a call of the field `f` of
        the explicit argument `P : <function>.Policy_P` (docs/translation.md)."""
        text = re.sub(r"\s+", "", self.tr.span(callee))
        numeric = re.fullmatch(r"std::numeric_limits<(\w+)>::(min|max|lowest|infinity)", text)
        if numeric and not args:
            parameter, member = numeric.groups()
            return self.numeric_trait(parameter, {"min": "minimum", "max": "maximum"}.get(member, member),
                                      Ty("tparam", parameter))
        m = re.fullmatch(r"(?:typename)?(\w+)::(\w+)", text)
        if m and self.cls is not None and m.group(1) in self.cls.tparams and not args:
            return self.static_call(m.group(1), m.group(2), pre, expected)
        if not m or m.group(1) not in self.sig.tparams or self.cls is not None:
            raise Unsupported(f"call through a dependent scope {text}")
        pol, member = m.group(1), m.group(2)
        texts, tys = [], []
        for a in args:
            t, ty = self.expr(a, pre)
            texts.append(t)
            tys.append(ty)
        if expected is not None and expected.kind not in ("unknown", "void"):
            rty = expected
        elif tys:
            rty = tys[0]
        else:
            raise Unsupported(f"result type of {pol}::{member}")
        methods = self.sig.policies.setdefault(pol, {})
        if member in methods and methods[member] != (tuple(tys), rty):
            raise Unsupported(f"{pol}::{member} used with two signatures")
        methods[member] = (tuple(tys), rty)
        tmp = self.fresh()
        pre.append(f"let {tmp} ← {' '.join([f'{pol}.{lean_name(member)}'] + texts)}")
        return tmp, rty

    def dependent_result(self, expected, default):
        if expected is not None and expected.kind not in ("unknown", "void"):
            return expected
        return default

    def static_call(self, parameter, member, pre, expected):
        """`P::f()` for a class template parameter `P`: the static member of the actual argument, an instance of
        `Cpp.StaticCall` (docs/translation.md)."""
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", member):
            raise Unsupported(f"static member {member}")
        rty = self.dependent_result(expected, Ty("tparam", parameter))
        self.reqs.add(f'Cpp.StaticCall "{member}" {parameter} {lean_type(rty)}')
        tmp = self.fresh()
        pre.append(f'let {tmp} ← Cpp.StaticCall.call (name := "{member}") (T := {parameter}) (R := {lean_type(rty)})')
        return tmp, rty

    def adl_call(self, name, args, pre, expected):
        """An unqualified call with dependent arguments and no declaration visible at the definition: the function
        found by argument-dependent lookup at instantiation, an instance of `Cpp.AdlCall2`."""
        if len(args) != 2 or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            raise Unsupported(f"argument-dependent call {name} with {len(args)} arguments")
        at, aty = self.expr(args[0], pre)
        bt, bty = self.expr(args[1], pre)
        if not (tparams_of(aty) or tparams_of(bty)):
            raise Unsupported(f"argument-dependent call {name} without a dependent argument")
        rty = self.dependent_result(expected, aty if aty == bty else None)
        if rty is None:
            raise Unsupported(f"result type of the argument-dependent call {name}")
        a, b, r = lean_type(aty), lean_type(bty), lean_type(rty)
        self.reqs.add(f'Cpp.AdlCall2 "{name}" {a} {b} {r}')
        tmp = self.fresh()
        pre.append(f'let {tmp} ← Cpp.AdlCall2.call (name := "{name}") (A := {a}) (B := {b}) (R := {r}) {at} {bt}')
        return tmp, rty

    def invoke_call(self, name, fty, args, pre, expected):
        """`f(x)` for a value `f` of a template parameter type `F`: its call operator, an instance of
        `Cpp.Invoke1`. Without an expected type the result is used as a condition (`bool`)."""
        if len(args) != 1:
            raise Unsupported(f"function object call {name} with {len(args)} arguments")
        at, aty = self.expr(args[0], pre)
        rty = self.dependent_result(expected, BOOL)
        a, r = lean_type(aty), lean_type(rty)
        self.reqs.add(f"Cpp.Invoke1 {fty.name} {a} {r}")
        tmp = self.fresh()
        pre.append(f"let {tmp} ← Cpp.Invoke1.call (A := {a}) (R := {r}) {self.var_name(name)} {at}")
        return tmp, rty

    def self_call(self, name, args, pre):
        if self.cls is None:
            raise Unsupported(f"member call {name} outside a class")
        sigs = [s for s in self.cls.methods if s.cpp_name == name and not s.is_ctor]
        sig = self.pick(sigs, args, name)
        if sig.is_static:
            return self.call_sig(sig, None, args, pre)
        if self.sig.is_const and not self.sig.is_ctor and not sig.is_const:
            raise Unsupported(f"non-const member {name} from a const member")
        if sig.is_const or sig.preserves_receiver:
            return self.call_sig(sig, self.self_value(), args, pre)
        return self.call_sig(sig, "self", args, pre)

    def method_call(self, base, name, args, pre):
        raw = strip(base)
        if (raw.get("kind") == "UnaryOperator" and raw.get("opcode") == "*"
                and strip(inner(raw)[0]).get("kind") == "CXXThisExpr"):
            return self.self_call(name, args, pre)
        bt, bty = self.expr(base, pre)
        if name == "operator bool" and bty == BOOL and not args:
            return bt, BOOL   # reading an element of a std::vector<bool> through its proxy
        if bty.kind in ("vec", "deque"):
            return self.vector_call(base, bt, bty, name, args, pre)
        if bty.kind == "optional":
            if name == "has_value" and not args:
                return f"{bt}.isSome", BOOL
            if name == "value" and not args:
                tmp = self.fresh()
                pre.append(f"let {tmp} ← Cpp.optionalValue {bt}")
                return tmp, bty.args[0]
            raise Unsupported(f"optional::{name}")
        if bty.kind == "ordered_set":
            if name == "size" and not args:
                return f"(UInt64.ofNat {bt}.length)", U64
            if name == "count" and len(args) == 1:
                value, _ = self.expr(args[0], pre, bty.args[0])
                tmp = self.fresh()
                pre.append(f"let {tmp} ← Cpp.orderedSetCount {self.pq_order(bty)} {bt} {value}")
                return tmp, U64
            raise Unsupported(f"set::{name} in an expression")
        if bty.kind in ("pq", "stack", "queue"):
            if name == "empty" and not args:
                return f"(List.isEmpty {bt})", BOOL
            if name == "size" and not args:
                return f"(UInt64.ofNat {bt}.length)", U64
            if name == "front" and not args and bty.kind == "queue":
                tmp = self.fresh()
                pre.append(f"let {tmp} ← Cpp.queueFront {bt}")
                return tmp, bty.args[0]
            if name == "top" and not args and bty.kind != "queue":
                self.need("Inhabited", bty.args[0])
                tmp = self.fresh()
                if bty.kind == "stack":
                    pre.append(f"let {tmp} ← Cpp.stackTop {bt}")
                else:
                    pre.append(f"let {tmp} ← Cpp.pqTop {self.pq_order(bty)} {bt}")
                return tmp, bty.args[0]
            raise Unsupported(f"{bty.kind}::{name}")
        if bty.kind == "umap" and name == "count" and len(args) == 1:
            kt, _ = self.expr(args[0], pre, INT)
            tmp = self.fresh()
            pre.append(f"let {tmp} ← Cpp.umapCount {bt} {kt}")
            return tmp, U64
        if bty.kind == "string":
            if name == "size" and not args:
                return f"(UInt64.ofInt (Cpp.size {bt}))", U64
            raise Unsupported(f"string::{name}")
        if bty.kind == "tparam" and self.cls is not None and bty.name in self.cls.tparams and len(args) == 1 \
                and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            # `f.name(x)` for a value of a class template parameter type: the member of the actual argument, an
            # instance of `Cpp.Method1` (docs/translation.md). The receiver is not changed.
            at, aty = self.expr(args[0], pre)
            rty = aty
            a, r, fty = lean_type(aty), lean_type(rty), lean_type(bty)
            self.reqs.add(f'Cpp.Method1 "{name}" {fty} {a} {r}')
            tmp = self.fresh()
            pre.append(f'let {tmp} ← Cpp.Method1.call (name := "{name}") (A := {a}) (R := {r}) {bt} {at}')
            return tmp, rty
        if bty.kind == "cls":
            info = self.tr.classes[bty.name]
            sigs = [s for s in info.methods if s.cpp_name == name and not s.is_ctor]
            sig = self.pick(sigs, args, f"{bty.name}::{name}")
            if sig.is_const or sig.preserves_receiver:
                return self.call_sig(sig, bt, args, pre, owner_ty=bty)
            if strip(base).get("kind") in ("CXXConstructExpr", "CXXTemporaryObjectExpr", "CXXUnresolvedConstructExpr"):
                # A temporary receiver is consumed here. Its updated state is not
                # written to another object; the returned value is still retained.
                return self.call_sig(sig, bt, args, pre, owner_ty=bty)
            target = self.lvalue(base)
            return self.call_sig(sig, ("obj", target, bt), args, pre, owner_ty=bty)
        raise Unsupported(f"method {name} on {bty}")

    def vector_call(self, base, bt, bty, name, args, pre):
        elem = bty.args[0]
        if name == "size" and not args:
            return f"(Cpp.size {bt})", INT
        if name == "empty" and not args:
            return f"(decide ({bt}.size = 0))", BOOL
        if name in ("back", "front") and not args:
            self.need("Inhabited", elem)
            return (f"(Cpp.back {bt})" if name == "back" else f"(Cpp.get {bt} 0)"), elem
        raise Unsupported(f"vector::{name} in an expression")

    def free_call(self, name, args, pre, callee, node):
        declaration = callee.get("referencedDecl", {})
        qualified = self.tr.qualified_functions.get(declaration.get("id"))
        if qualified is not None:
            return self.call_sig(self.tr.functions[qualified][0], None, args, pre)
        call_text = re.sub(r"\s+", "", self.tr.span(callee))
        if any(call_text in (qualified, f"cp::{qualified}", f"::cp::{qualified}")
               for qualified in self.tr.qualified_functions.values()):
            raise Unsupported(f"unresolved child namespace function {call_text}")
        if name in ("bit_width", "countr_zero") and call_text in (f"std::{name}", f"::std::{name}"):
            if len(args) != 1 or declaration.get("kind") != "FunctionDecl":
                raise Unsupported(f"unresolved standard bit operation std::{name}")
            value, ty = self.expr(args[0], pre)
            if (ty.kind not in ("u32", "u64")
                    or node["type"].get("desugaredQualType", type_of_decl(node)) != "int"):
                raise Unsupported(f"std::{name} requires an unsigned 32- or 64-bit argument")
            pre.append("Cpp.tick")
            if name == "bit_width":
                return f"(Int.ofNat (Cpp.bitWidth {value}.toNat))", INT32
            width = 32 if ty.kind == "u32" else 64
            return f"(Int.ofNat (Cpp.countrZero {width} {value}.toNat))", INT32
        if name in ("min", "max") and call_text.startswith(f"std::{name}<"):
            raise Unsupported("explicit template arguments of a standard extrema function")
        if name in ("min", "max") and not args and "numeric_limits<" in call_text:
            # std::numeric_limits<T>::min() / max() of a fixed integer type: a literal
            text = self.tr.span(callee).replace(" ", "")
            limits = {"int": (-2**31, 2**31 - 1, INT32), "longlong": (-2**63, 2**63 - 1, INT),
                      "std::int64_t": (-2**63, 2**63 - 1, INT), "int64_t": (-2**63, 2**63 - 1, INT)}
            for key, (lo, hi, ty) in limits.items():
                if f"numeric_limits<{key}>::" in text:
                    v = lo if name == "min" else hi
                    return (f"({v} : Int)" if v >= 0 else f"(({v}) : Int)"), ty
            raise Unsupported(f"numeric_limits {text}")
        if name in ("gcd", "lcm"):
            numeric_text = re.sub(r"\s+", "", self.tr.span(callee))
            if numeric_text.startswith("std::") and numeric_text != f"std::{name}":
                raise Unsupported("explicit template arguments of a standard numeric function")
        if name in ("gcd", "lcm") and len(args) == 2 and \
                numeric_text == f"std::{name}":
            # Only explicitly qualified std calls have this trusted contract; do not
            # replace a same-named user function or an ADL customization.
            at, aty = self.expr(args[0], pre)
            bt, bty = self.expr(args[1], pre)
            ty = self.common_type(aty, bty)
            if ty.kind not in ("int", "u32", "u64", "tparam"):
                raise Unsupported(f"std::{name} on {ty}")
            for operand in (aty, bty, ty):
                self.need("Cpp.NumericGcd", operand)
            self.reqs.add("Cpp.NumericCost")
            cost = "numericGcdCost" if name == "gcd" else "numericLcmCost"
            pre.append(f"Cpp.tickN (Cpp.{cost} {at} {bt})")
            return f"(Cpp.numeric{'Gcd' if name == 'gcd' else 'Lcm'} (γ := {lean_type(ty)}) {at} {bt})", ty
        # A spelling alone is not a standard-library contract: cp::max may
        # compute something entirely different. Local using declarations are
        # scoped, and dependent lookup must refer only to their shadow set.
        local_standard = any(name in scope.get("__std_extrema__", set())
                             for scope in self.scopes)
        lookups = callee.get("lookups", [])
        using_standard = call_text == name and local_standard and (
            (callee.get("kind") == "UnresolvedLookupExpr" and bool(lookups)
             and all(d.get("kind") == "UsingShadowDecl" for d in lookups))
            or (callee.get("kind") == "DeclRefExpr"
                and callee.get("foundReferencedDecl", {}).get("kind") == "UsingShadowDecl"))
        if name in ("min", "max") and len(args) == 2 and (
                call_text == f"std::{name}" or using_standard):
            at, aty = self.expr(args[0], pre)
            bt, bty = self.expr(args[1], pre, aty)
            if aty.kind == "tparam":
                self.need("Min" if name == "min" else "Max", aty)
            return f"({name} {at} {bt})", aty
        if name == "abs" and len(args) == 1:
            at, aty = self.expr(args[0], pre, INT)
            return f"(Int.natAbs {at} : Int)", INT
        sigs = self.tr.functions.get(name)
        if not sigs:
            raise Unsupported(f"unknown function {name}")
        sig = self.pick(sigs, args, name)
        value_args = {}
        if sig.value_params:
            explicit = re.fullmatch(rf"(?:cp::)?{re.escape(name)}<(.*)>", call_text)
            if explicit:
                raw = split_args(explicit.group(1))
                if len(raw) != len(sig.tparams):
                    raise Unsupported(f"template argument count of {name}")
                own_values = {**(self.cls.value_params if self.cls else {}), **self.sig.value_params}
                for parameter, text in zip(sig.tparams, raw):
                    if parameter in sig.value_params:
                        value_args[parameter] = parse_value_arg(text, sig.value_params[parameter], own_values)
                    else:
                        raise Unsupported("explicit mixed type and non-type function arguments")
        return self.call_sig(sig, None, args, pre, value_args=value_args)

    def call_sig(self, sig: Sig, receiver, args, pre, expected=None, owner_ty=None, value_args=None, evaluated_args=None):
        """Emit `let t ← f receiver args` into pre and write back mutable outputs. Returns (value, Ty)."""
        texts = []
        writes = []
        bindings = dict(value_args or {})
        info = self.tr.classes.get(sig.owner)
        if info is not None and (info.value_params or sig.tparams):
            actual = expected if sig.is_ctor else owner_ty
            if actual is None and self.cls is not None and self.cls.name == info.name:
                actual = class_ty(self.cls)
            if actual is not None:
                bindings.update(zip(info.tparams, actual.args))
        def infer(formal, actual):
            if (sig.owner or sig.constraints) and formal.kind == "tparam" and formal.name in sig.tparams:
                if formal.name in bindings and bindings[formal.name] != actual:
                    raise Unsupported("conflicting member template type arguments")
                bindings[formal.name] = actual
            elif formal.kind == "vparam" and formal.name in sig.value_params:
                if (actual.kind not in ("vparam", "vlit") or actual.args != formal.args
                        or actual.args[0].width != formal.args[0].width):
                    raise Unsupported("non-type template argument deduction conversion")
                if formal.name in bindings and bindings[formal.name] != actual:
                    raise Unsupported("conflicting non-type template arguments")
                bindings[formal.name] = actual
            elif formal.kind == actual.kind and formal.name == actual.name:
                for f, a in zip(formal.args, actual.args):
                    infer(f, a)
        if (sig.owner or sig.constraints) and sig.tparams:
            for (_, formal, _), arg in zip(sig.params, args):
                infer(formal, self.tr.ty(strip(arg)["type"]["qualType"], self))
            if set(sig.tparams) - bindings.keys():
                raise Unsupported(f"cannot infer member template arguments of {sig.cpp_name}")
        free_bindings = False
        if not sig.owner and not sig.constraints and sig.tparams and not sig.value_params and not bindings:
            # A free function template called with other template arguments than the caller's own (e.g.
            # inv_perm(arg_sort(v)) with T = int): deduce them from the argument types as C++ does. When the
            # deduction is the identity (the caller passes its own T), keep the same-name convention.
            deduced = {}
            def deduce(formal, actual):
                if formal.kind == "tparam" and formal.name in sig.tparams:
                    if formal.name in deduced and deduced[formal.name] != actual:
                        raise Unsupported(f"conflicting template arguments of {sig.cpp_name}")
                    deduced[formal.name] = actual
                elif formal.kind == actual.kind and formal.name == actual.name:
                    for f, a in zip(formal.args, actual.args):
                        deduce(f, a)
            qual = [strip(arg).get("type", {}).get("qualType", "") for arg in args]
            def readable(q):
                try:
                    self.tr.ty(q, self)
                    return True
                except Unsupported:
                    return False
            if evaluated_args is None and not all(readable(q) for q in qual):
                # The argument types are only known after translating them (calls of other templates).
                evaluated_args = []
                for (_, formal, is_ref), arg in zip(sig.params, args):
                    if is_ref:
                        evaluated_args.append((None, self.lvalue(arg)[3]))
                    else:
                        evaluated_args.append(self.expr(arg, pre))
            for index, ((_, formal, _), arg) in enumerate(zip(sig.params, args)):
                actual = evaluated_args[index][1] if evaluated_args is not None else self.tr.ty(qual[index], self)
                deduce(formal, actual)
            if set(sig.tparams) <= deduced.keys() and any(
                    deduced[p] != Ty("tparam", p) for p in sig.tparams):
                own = set(self.sig.tparams) | set(self.cls.tparams if self.cls else [])
                if any(deduced[p].kind == "tparam" and deduced[p].name not in own for p in sig.tparams):
                    raise Unsupported(f"template arguments of {sig.cpp_name}")
                bindings.update(deduced)
                free_bindings = True
        if sig.value_params:
            for index, ((_, formal, _), arg) in enumerate(zip(sig.params, args)):
                if formal.kind == "cls":
                    actual = evaluated_args[index][1] if evaluated_args is not None else self.tr.ty(strip(arg)["type"]["qualType"], self)
                    infer(formal, actual)
            if set(sig.value_params) - bindings.keys():
                raise Unsupported(f"cannot infer non-type template arguments of {sig.cpp_name}")
        for index, ((pname, pty, is_ref), arg) in enumerate(zip(sig.params, args)):
            if is_ref:
                target = self.lvalue(arg)
                texts.append(self.read_lvalue(target))
                writes.append(target)
            else:
                pty = subst(pty, list(bindings), list(bindings.values())) if bindings else self.instantiate_param(pty, sig)
                if evaluated_args is None:
                    t, _ = self.expr(arg, pre, pty)
                else:
                    t, ty = evaluated_args[index]
                    t, _ = self.convert(t, ty, pty, arg)
                texts.append(t)
        self.callees.append(sig)
        packets = self.trait_packets(sig, args)
        discharged = set()
        if packets:
            if self.trait_eligibility(sig, args) is not True:
                raise Unsupported("constrained call eligibility is not established")
            discharged.update(f'Cpp.TypeTraits "{p}" {p}' for p in packets)
            discharged.update(f'Cpp.ModToUInt32 "{p}" {p}' for p in packets)
            discharged.update("Cpp.TemplateConstraint " + c for c in sig.constraints)
            self.type_trait_bindings.update(packets.values())
            for parameter, (cpp, _, _) in packets.items():
                pre.append(f'let _ : Cpp.ModToUInt32 "{parameter}" {lean_type(bindings[parameter])} := '
                           + mod_to_uint32_binding(cpp, parameter))
        if (sig.owner and (sig.tparams or info.constraints)) or packets or sig.value_params or free_bindings:
            recorded = dict(bindings)
            if free_bindings:
                recorded["__free__"] = True
            self.member_call_bindings.setdefault(id(sig), []).append((recorded, discharged))
        parts = [sig.lean_name]
        parameters = {**(info.value_params if info else {}), **sig.value_params}
        if sig.owner or sig.constraints or free_bindings:
            parameters = {**dict.fromkeys(sig.tparams), **parameters}
        for parameter in parameters:
            if parameter in bindings:
                parts.append(f"({lean_name(parameter)} := {lean_type(bindings[parameter])})")
        if sig.is_static and info is not None and receiver is None and self.cls is not None \
                and self.cls.name == info.name:
            # a static member of this class template: its class parameters are not inferred from the arguments
            shown = set(re.findall(r"\w+", " ".join(lean_type(t) for t in [sig.ret, *(q[1] for q in sig.params)])))
            for parameter in info.tparams:
                if parameter not in parameters and parameter not in info.value_params and parameter not in shown:
                    parts.append(f"({lean_name(parameter)} := {lean_name(parameter)})")
        for parameter, (_, signed, int128) in packets.items():
            parts.append(f"(cppTypeTraits_{parameter} := ⟨{str(signed).lower()}, {str(int128).lower()}⟩)")
        for condition in sig.constraints:
            r = "Cpp.TemplateConstraint " + condition
            if r in discharged:
                parts.append(f"({constraint_binder(r)} := ⟨by decide⟩)")
        if receiver == "self":
            parts.append(self.self_value())
        elif isinstance(receiver, tuple):
            parts.append(receiver[2])
        elif receiver is not None:
            parts.append(receiver)
        parts += texts
        if sig.uses_globals:
            if not self.sig.uses_globals:
                raise Unsupported("global call dependency was not propagated")
            parts.append(self.global_value())
        tmp = self.fresh()
        pre.append(f"let {tmp} ← {' '.join(parts)}")
        outputs = sig.outputs()
        ret_ty = sig.ret if not sig.is_ctor else expected
        if sig.is_ctor and not sig.outputs():
            return tmp, expected
        values = {}
        if len(outputs) == 1:
            values[outputs[0]] = tmp
        else:
            for i, o in enumerate(outputs):
                values[o] = tmp + "".join([".2"] * i) + (".1" if i < len(outputs) - 1 else "")
        for target, (pname, _, _) in zip(writes, sig.mut_refs):
            pre.extend(self.assign_lines(target, values[pname]))
        if sig.uses_globals:
            for key, (name, _, _) in self.tr.globals.items():
                pre.append(f"{self.global_names[key]} := {values['@globals']}.{lean_name(name)}")
        if sig.is_ctor:
            return values["ret"], expected
        if receiver == "self":
            if self.sig.preserves_receiver:
                raise Unsupported("a receiver-preserving member calls a mutating member on this")
            for f, _, _ in self.cls.fields:
                pre.append(f"{self.field_names[f]} := {values['self']}.{lean_name(f)}")
        elif isinstance(receiver, tuple):
            pre.extend(self.assign_lines(receiver[1], values["self"]))
        if sig.ret.kind == "void":
            return "()", VOID
        return values["ret"], (subst(sig.ret, list(bindings), list(bindings.values())) if bindings else self.instantiate_param(sig.ret, sig))

    def instantiate_param(self, ty, sig):
        return ty

    # ------------------------------------------------------------------ lvalues
    def lvalue(self, node):
        """An lvalue path: (root lean name, [index texts], Ty of the whole)."""
        n = strip(node)
        kind = n.get("kind")
        if kind == "DeclRefExpr":
            name = n["referencedDecl"]["name"]
            key = n["referencedDecl"].get("id")
            if key in self.tr.globals:
                ty = self.tr.globals[key][1]
                return (self.global_names[key], [], ty, ty)
            ty = self.lookup(name)
            if ty is None:
                raise Unsupported(f"unknown variable {name}")
            return (self.var_name(name), [], ty, ty)
        if kind == "CXXDependentScopeMemberExpr" and inner(n) and not n.get("isArrow"):
            root, path, rty, bty = self.lvalue(inner(n)[0])
            member = n.get("member")
            if bty.kind == "pair" and member in ("first", "second"):
                i = 0 if member == "first" else 1
                return (root, path + [("pair", i)], rty, bty.args[i])
            if bty.kind == "cls":
                info = self.tr.classes[bty.name]
                for fname, fty, _ in info.fields:
                    if fname == member:
                        return (root, path + [("field", lean_name(fname))], rty, subst(fty, info.tparams, bty.args))
            typed = self.default_field_type(bty, member, for_write=True)
            if typed is not None and typed.kind in ("int", "u32", "u64", "bool", "tparam"):
                record_type, value_type = lean_type(bty), lean_type(typed)
                self.reqs.add(f'Cpp.Field "{member}" {record_type} {value_type}')
                self.reqs.add(f'Cpp.WriteField "{member}" {record_type} {value_type}')
                return (root, path + [("dependent_field", member)], rty, typed)
            raise Unsupported("unrecognized dependent assignment field")
        if kind in ("CallExpr", "CXXMemberCallExpr") and len(inner(n)) == 1:
            callee = strip(inner(n)[0])
            if callee.get("kind") in ("MemberExpr", "CXXDependentScopeMemberExpr") and \
                    (callee.get("name") or callee.get("member")) == "back" and inner(callee):
                root, path, rty, bty = self.lvalue(inner(callee)[0])
                if bty.kind != "vec":
                    raise Unsupported("back() of a non-vector")
                self.need("Inhabited", bty.args[0])
                current = self.read_lvalue((root, path, rty, bty))
                return (root, path + [("index", f"(Cpp.size {current} - 1)")], rty, bty.args[0])
        if kind == "MemberExpr":
            base = strip(inner(n)[0])
            if base.get("kind") == "CXXThisExpr":
                t, ty = self.field_ref(n["name"])
                return (t, [], ty, ty)
            root, path, rty, bty = self.lvalue(base)
            if bty.kind == "pair" and n["name"] in ("first", "second"):
                i = 0 if n["name"] == "first" else 1
                return (root, path + [("pair", i)], rty, bty.args[i])
            if bty.kind == "cls":
                info = self.tr.classes[bty.name]
                for fname, fty, _ in info.fields:
                    if fname == n["name"]:
                        return (root, path + [("field", lean_name(fname))], rty, subst(fty, info.tparams, bty.args))
            raise Unsupported(f"member lvalue {n['name']}")
        if kind == "ArraySubscriptExpr" or (kind == "CXXOperatorCallExpr" and self.operator_name(n) == "[]"):
            base, index = self.subscript_parts(n)
            root, path, rty, bty = self.lvalue(base)
            pre = []
            it, _ = self.expr(index, pre, INT)
            if pre:
                raise Unsupported("a call inside an index of an assignment target")
            if bty.kind not in ("vec", "deque"):
                raise Unsupported("subscript of an unsupported container")
            self.need("Inhabited", bty.args[0])
            return (root, path + [("index", it)], rty, bty.args[0])
        raise Unsupported(f"lvalue {kind}")

    def read_lvalue(self, target):
        root, path, _, _ = target
        text = root
        for step in path:
            text = self.read_step(text, step)
        return text

    def read_step(self, text, step):
        kind, arg = step
        if kind == "index":
            return f"(Cpp.get {text} {arg})"
        if kind == "pair":
            return f"{text}.{arg + 1}"
        if kind == "dependent_field":
            return f'(Cpp.Field.get (member := "{arg}") {text})'
        return f"{text}.{arg}"

    def assign_lines(self, target, value):
        root, path, _, _ = target
        if self.sig.preserves_receiver and root in self.field_names.values():
            raise Unsupported("a receiver-preserving member writes a field of this")
        return [f"{root} := {self.update(root, path, value)}"]

    def update(self, current, path, value):
        if not path:
            return value
        kind, arg = path[0]
        inner_cur = self.read_step(current, path[0])
        new = self.update(inner_cur, path[1:], value)
        if kind == "index":
            return f"(Cpp.set {current} {arg} {new})"
        if kind == "pair":
            return f"({new}, {current}.2)" if arg == 0 else f"({current}.1, {new})"
        if kind == "dependent_field":
            return f'(Cpp.WriteField.set (member := "{arg}") {current} {new})'
        return f"{{ {current} with {arg} := {new} }}"

    # ------------------------------------------------------------------ statements
    def flush(self, pre):
        for line in pre:
            self.emit(line)

    def block(self, node):
        self.scopes.append({})
        if node.get("kind") == "CompoundStmt":
            for s in inner(node):
                self.stmt(s)
        else:
            self.stmt(node)
        self.scopes.pop()

    def check_increment_sequencing(self, node):
        """Reject a full expression that increments a variable inside a larger expression and also uses it
        elsewhere: C++ leaves the order of those accesses unsequenced or unspecified."""
        statements = ("CompoundStmt", "IfStmt", "WhileStmt", "ForStmt", "DoStmt", "SwitchStmt")
        increments, uses = {}, {}
        def walk(n, top):
            if not isinstance(n, dict):
                return
            kind = n.get("kind")
            if kind in statements and not top:
                return
            if kind == "UnaryOperator" and n.get("opcode") in ("++", "--") and not top:
                base = strip(inner(n)[0]) if inner(n) else {}
                root = self.subscript_root(base)
                if root is not None:
                    key = root.get("referencedDecl", {}).get("id")
                    increments[key] = increments.get(key, 0) + 1
                    uses[key] = uses.get(key, 0) - 1
                if base.get("kind") == "DeclRefExpr":
                    key = base.get("referencedDecl", {}).get("id")
                    increments[key] = increments.get(key, 0) + 1
                    uses[key] = uses.get(key, 0) - 1
            if kind == "DeclRefExpr":
                key = n.get("referencedDecl", {}).get("id")
                uses[key] = uses.get(key, 0) + 1
            for child in inner(n):
                walk(child, False)
        kind = node.get("kind")
        if kind in ("ForStmt", "CompoundStmt", "NullStmt"):
            return
        if kind in ("IfStmt", "WhileStmt", "DoStmt", "SwitchStmt"):
            conds = [c for c in inner(node) if c.get("kind") not in statements]
            for c in conds:
                walk(c, False)
        else:
            walk(node, True)
        for key, count in increments.items():
            if count + uses.get(key, 0) > 1:
                raise Unsupported("a variable incremented inside an expression is used again in the same expression")

    def stmt(self, node):
        kind = node.get("kind")
        self.check_increment_sequencing(node)
        if kind == "CompoundStmt":
            self.emit("do")
            self.indent += 1
            self.block(node)
            self.emit("pure ()")
            self.indent -= 1
            return
        if kind == "NullStmt":
            return
        if kind == "DeclStmt":
            for d in inner(node):
                self.decl(d)
            return
        if kind == "ReturnStmt":
            pre = []
            value = self.self_value() if self.sig.is_ctor else None
            parts = self.assignment_parts(inner(node)[0]) if inner(node) else None
            if parts is not None:
                # `return a = e;` stores first; the value of an assignment is its left operand after the store,
                # so the left operand is read again. Its evaluation must not have side effects.
                if self.has_side_effects(parts[0]):
                    raise Unsupported("returned assignment whose left operand has side effects")
                self.expr_stmt(inner(node)[0])
                value, _ = self.expr(parts[0], pre, self.sig.ret)
                self.flush(pre)
                self.emit("return " + self.result(value))
                return
            if inner(node):
                value, _ = self.expr(inner(node)[0], pre, self.sig.ret)
                if self.sig.ret.kind == "vec" and self.is_umap_subscript(inner(node)[0]):
                    # returning the mapped vector of an unordered_map by value copies it
                    pre.append(f"Cpp.tickN {value}.size")
            self.flush(pre)
            if self.sig.is_ctor and not self.sig.uses_globals:
                self.emit("return " + value)
            else:
                self.emit("return " + self.result(value))
            return
        if kind == "IfStmt":
            self.if_stmt(node)
            return
        if kind == "ForStmt":
            self.for_stmt(node)
            return
        if kind == "WhileStmt":
            cond, body = inner(node)[-2], inner(node)[-1]
            self.while_loop(None, cond, body, [])
            return
        if kind == "DoStmt":
            # do body while (cond): the body runs first; a `continue` would have to jump to the condition,
            # which the translation does not express, so it is rejected.
            body, cond = inner(node)[0], inner(node)[-1]
            def has_continue(n):
                if n.get("kind") == "ContinueStmt":
                    return True
                if n.get("kind") in ("WhileStmt", "ForStmt", "DoStmt", "CXXForRangeStmt"):
                    return False
                return any(has_continue(c) for c in inner(n))
            if has_continue(body):
                raise Unsupported("continue in a do-while loop")
            self.emit("for _ in Cpp.forever do")
            self.indent += 1
            self.emit("Cpp.tick")
            self.continue_prefix.append([])
            self.block(body)
            self.continue_prefix.pop()
            pre = []
            ct, _ = self.expr(cond, pre, BOOL)
            self.flush(pre)
            self.emit(f"if !{ct} then break")
            self.indent -= 1
            return
        if kind == "CXXForRangeStmt":
            self.range_for(node)
            return
        if kind == "BreakStmt":
            self.emit("break")
            return
        if kind == "ContinueStmt":
            if self.continue_prefix and self.continue_prefix[-1]:
                for line in self.continue_prefix[-1]:
                    self.emit(line)
            self.emit("continue")
            return
        self.expr_stmt(node)

    def result(self, value):
        outs = []
        for o in self.sig.outputs():
            if o == "ret":
                outs.append(value)
            elif o == "self":
                outs.append(self.self_value())
            elif o == "@globals":
                outs.append(self.global_value())
            else:
                outs.append(lean_name(o))
        if not outs:
            return "()"
        if len(outs) == 1:
            return outs[0]
        return "(" + ", ".join(outs) + ")"

    def decompose(self, d):
        spelling = d["type"]
        if (any("&" in spelling.get(key, "") for key in ("qualType", "desugaredQualType"))
                or d.get("storageClass") in ("static", "extern") or d.get("tls")):
            raise Unsupported("reference or static structured binding")
        bindings = [child for child in inner(d) if child.get("kind") == "BindingDecl"]
        initializers = [child for child in inner(d) if child.get("kind") != "BindingDecl"]
        if len(initializers) != 1:
            raise Unsupported("structured binding without a single initializer")
        pre = []
        value, ty = self.expr(initializers[0], pre)
        if ty.kind not in ("tuple", "pair") or len(bindings) != len(ty.args):
            raise Unsupported("structured binding requires a tuple or pair of matching arity")
        if ty.kind == "pair" and any(a.kind not in ("int", "u32", "u64", "bool", "tparam") for a in ty.args):
            raise Unsupported("pair structured binding requires scalar elements")
        item = self.fresh()
        self.flush(pre)
        self.emit(f"let {item} := {value}")
        lvalue = strip(initializers[0]).get("valueCategory") == "lvalue"
        for i, (binding, arg) in enumerate(zip(bindings, ty.args, strict=True)):
            name = binding["name"]
            projection = ".2" * i + (".1" if i + 1 < len(bindings) else "")
            self.declare(name, arg)
            if arg.kind == "vec" and lvalue:
                self.emit(f"Cpp.tickN {item}{projection}.size")
            self.emit(f"let mut {self.var_name(name)} : {lean_type(arg)} := {item}{projection}")

    def decl(self, d):
        if d.get("kind") == "DecompositionDecl":
            self.decompose(d)
            return
        if d.get("kind") == "UsingDecl":
            if d.get("name") not in ("std::min", "std::max"):
                raise Unsupported(f"using declaration {d.get('name')}")
            self.scopes[-1].setdefault("__std_extrema__", set()).add(d["name"].split("::")[-1])
            return
        if d.get("kind") == "TypeAliasDecl":
            # a local type alias: used by the later declarations of the body
            name = d["name"]
            if name in self.local_aliases or self.lookup(name) is not None:
                raise Unsupported(f"local type alias {name} declared twice")
            self.local_aliases[name] = self.tr.ty(type_of_decl(d), self)
            return
        if d.get("kind") != "VarDecl":
            raise Unsupported(f"declaration {d.get('kind')}")
        if d.get("id") in self.tr.local_statics:
            return
        if d.get("storageClass") in ("static", "extern") or d.get("tls"):
            raise Unsupported("local static, external, or thread-local storage")
        name = d["name"]
        qual = type_of_decl(d)
        init = inner(d)
        pre = []
        if "&" in qual and not qual.strip().startswith("const") and "const" not in qual:
            raise Unsupported(f"reference variable {name}")
        if qual.startswith("auto") or qual.startswith("const auto"):
            if not init:
                raise Unsupported("auto without initializer")
            value, ty = self.expr(init[0], pre)
        else:
            ty = self.tr.ty(qual, self)
            if init:
                i0 = init[0]
                s = strip(i0)
                if s.get("kind") in ("CXXConstructExpr", "ParenListExpr", "InitListExpr", "CXXScalarValueInitExpr") \
                        and not (s.get("kind") == "CXXConstructExpr" and len(inner(s)) == 1
                                 and self.is_copy(inner(s)[0])):
                    value = self.construct(ty, s, pre)
                else:
                    value, _ = self.expr(i0, pre, ty)
                    if ty.kind == "vec" and self.is_lvalue_vector(i0):
                        tmp = self.fresh()
                        pre.append(f"let {tmp} := {value}")
                        pre.append(f"Cpp.tickN {tmp}.size")
                        value = tmp
            else:
                value = self.default_value(ty)
        self.flush(pre)
        self.declare(name, ty)
        self.emit(f"let mut {self.var_name(name)} : {lean_type(ty)} := {value}")

    def is_copy(self, node):
        s = strip(node)
        return s.get("kind") in ("DeclRefExpr", "MemberExpr", "ArraySubscriptExpr", "CXXOperatorCallExpr")

    def subscript_root(self, node):
        """The local variable `v` of an element `v[i]` (a DeclRefExpr), or None."""
        s = strip(node)
        if not (s.get("kind") == "ArraySubscriptExpr"
                or (s.get("kind") == "CXXOperatorCallExpr" and self.operator_name(s) == "[]")):
            return None
        root = strip(self.subscript_parts(s)[0])
        if root.get("kind") == "DeclRefExpr" and \
                root.get("referencedDecl", {}).get("kind") in ("VarDecl", "ParmVarDecl"):
            return root
        return None

    def is_umap_subscript(self, node):
        s = strip(node)
        if not (s.get("kind") == "ArraySubscriptExpr"
                or (s.get("kind") == "CXXOperatorCallExpr" and self.operator_name(s) == "[]")):
            return False
        base, _ = self.subscript_parts(s)
        try:
            return self.expr(base, [])[1].kind == "umap"
        except Unsupported:
            return False

    def is_lvalue_vector(self, node):
        s = strip(node)
        return s.get("kind") in ("DeclRefExpr", "MemberExpr", "ArraySubscriptExpr", "CXXOperatorCallExpr")

    def if_stmt(self, node):
        kids = inner(node)
        has_else = node.get("hasElse", False)
        if node.get("hasInit") or node.get("hasVar"):
            raise Unsupported("if with an initializer")
        cond = kids[0]
        then = kids[1]
        other = kids[2] if has_else else None
        pre = []
        ct, _ = self.expr(cond, pre, BOOL)
        self.flush(pre)
        self.emit(f"if {ct} then")
        self.indent += 1
        old_floating = self.floating_constexpr_types.copy()
        floating = re.fullmatch(r"std::is_floating_point_v<(\w+)>",
                                re.sub(r"\s+", "", self.tr.span(strip(cond))))
        if node.get("isConstexpr") and floating:
            self.floating_constexpr_types.add(floating.group(1))
        self.block_or_unit(then)
        self.floating_constexpr_types = old_floating
        self.indent -= 1
        if other is not None:
            if other.get("kind") == "IfStmt":
                self.emit("else")
                self.indent += 1
                self.if_stmt(other)
                self.indent -= 1
            else:
                self.emit("else")
                self.indent += 1
                self.block_or_unit(other)
                self.indent -= 1

    def block_or_unit(self, node):
        start = len(self.lines)
        self.block(node)
        if len(self.lines) == start:
            self.emit("pure ()")

    def has_side_effects(self, n):
        """Whether evaluating the expression may change state: calls other than a subscript, `++`/`--`,
        assignments."""
        n = strip(n)
        kind = n.get("kind")
        if kind in ("CompoundAssignOperator", "CallExpr", "CXXMemberCallExpr"):
            return True
        if kind == "BinaryOperator" and n.get("opcode") in ("=", ","):
            return True
        if kind == "UnaryOperator" and n.get("opcode") in ("++", "--"):
            return True
        if kind == "CXXOperatorCallExpr" and self.operator_name(n) != "[]":
            return True
        return any(self.has_side_effects(c) for c in inner(n))

    def assignment_parts(self, n):
        """(lhs, rhs, rebuild) of an assignment node, or None."""
        n = strip(n)
        if n.get("kind") == "BinaryOperator" and n.get("opcode") == "=":
            lhs, rhs = inner(n)
            return lhs, rhs, lambda a, b: {**n, "inner": [a, b]}
        if n.get("kind") == "CXXOperatorCallExpr" and self.operator_name(n) == "=":
            callee, lhs, rhs = inner(n)
            return lhs, rhs, lambda a, b: {**n, "inner": [callee, a, b]}
        return None

    def expr_stmt(self, node):
        n = strip(node)
        kind = n.get("kind")
        pre = []
        if kind == "BinaryOperator" and n.get("opcode") == ",":
            # A comma expression statement evaluates its operands in order.
            a, b = inner(n)
            self.expr_stmt(a)
            self.expr_stmt(b)
            return
        if kind == "CompoundAssignOperator" and strip(inner(n)[0]).get("kind") == "ConditionalOperator":
            # `(c ? a : b) op= x` stores into the selected operand: `if c then a op= x else b op= x`.
            cond, yes, no = inner(strip(inner(n)[0]))
            ct, _ = self.expr(cond, pre, BOOL)
            self.flush(pre)
            self.emit(f"if {ct} then")
            self.indent += 1
            self.expr_stmt({**n, "inner": [yes, inner(n)[1]]})
            self.indent -= 1
            self.emit("else")
            self.indent += 1
            self.expr_stmt({**n, "inner": [no, inner(n)[1]]})
            self.indent -= 1
            return
        outer = self.assignment_parts(n)
        if outer is not None and self.assignment_parts(outer[1]) is not None:
            # `a = b = c` is `b = c; a = b;`: the value of an assignment is its left operand after the store.
            inner_lhs = self.assignment_parts(outer[1])[0]
            self.expr_stmt(outer[1])
            self.expr_stmt(outer[2](outer[0], inner_lhs))
            return
        if kind == "CXXOperatorCallExpr" and self.operator_name(n) == "=" and \
                self.umap_store(n, inner(n)[1], inner(n)[2], pre):
            return
        if kind == "BinaryOperator" and n["opcode"] == "=" and self.umap_store(n, inner(n)[0], inner(n)[1], pre):
            return
        if kind == "CXXOperatorCallExpr" and self.operator_name(n) == "=":
            callee, lhs, rhs = inner(n)
            declaration = self.tr.raw_declarations.get(strip(callee).get("referencedDecl", {}).get("id"), {})
            target = self.lvalue(lhs)
            if target[3].kind == "bool" and target[1] and target[1][-1][0] == "index":
                # `v[i] = b` of a std::vector<bool>: the assignment operator of its element proxy.
                value, _ = self.expr(rhs, pre, BOOL)
                self.flush(pre)
                for line in self.assign_lines(target, value):
                    self.emit(line)
                return
            if target[3].kind == "vec":
                # std::vector::operator=: the value of the right side (a copy costs its length).
                value, _ = self.expr(rhs, pre, target[3])
                if self.is_lvalue_vector(rhs):
                    pre.append(f"Cpp.tickN {value}.size")
                self.flush(pre)
                for line in self.assign_lines(target, value):
                    self.emit(line)
                return
            if (not declaration.get("isImplicit") or declaration.get("name") != "operator="
                    or target[3].kind != "cls"
                    or any(ty.kind not in ("int", "u32", "u64", "bool")
                           for _, ty, _ in self.tr.classes[target[3].name].fields)):
                raise Unsupported("record assignment requires an implicit scalar-field assignment")
            value, ty = self.expr(rhs, pre, target[3])
            if ty != target[3]:
                raise Unsupported("record assignment type mismatch")
            self.flush(pre)
            for line in self.assign_lines(target, value):
                self.emit(line)
            return
        if kind == "BinaryOperator" and n["opcode"] == "=":
            lhs, rhs = inner(n)
            target = self.lvalue(lhs)
            if target[3].kind == "tparam" and strip(rhs).get("kind") == "BinaryOperator" \
                    and strip(rhs).get("opcode") == "*":
                value, value_type = self.expr(rhs, pre)
                if value_type.kind == "mul_result":
                    ty = lean_type(target[3])
                    self.reqs.add(f"Cpp.AssignResult {ty} {lean_type(value_type)}")
                    value = f"(Cpp.AssignResult.assign {self.read_lvalue(target)} {value})"
                else:
                    value, _ = self.convert(value, value_type, target[3], rhs)
            else:
                value, _ = self.expr(rhs, pre, target[3])
            if target[3].kind == "vec" and self.is_lvalue_vector(rhs):
                pre.append(f"Cpp.tickN {value}.size")
            self.flush(pre)
            for line in self.assign_lines(target, value):
                self.emit(line)
            return
        if kind == "CompoundAssignOperator" or (kind == "CXXOperatorCallExpr" and self.operator_name(n) in
                                                ("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=")):
            if kind == "CompoundAssignOperator":
                op = n["opcode"][:-1]
                lhs, rhs = inner(n)
            else:
                op = self.operator_name(n)[:-1]
                lhs, rhs = inner(n)[1], inner(n)[2]
            try:
                lhs_type = self.tr.ty(strip(lhs)["type"]["qualType"], self)
            except Unsupported:
                lhs_type = None  # Vector reference aliases are resolved by lvalue below.
            if lhs_type is not None and lhs_type.kind == "cls":
                if kind == "CXXOperatorCallExpr":
                    self.expr(n, pre)
                else:
                    if self.tr.functions.get("operator" + n["opcode"]):
                        raise Unsupported("unresolved compound operator has free overload candidates")
                    self.method_call(lhs, "operator" + n["opcode"], [rhs], pre)
                self.flush(pre)
                return
            target = self.lvalue(lhs)
            current = self.read_lvalue(target)
            value, _ = self.binary_parts_text(op, current, target[3], rhs, pre)
            self.flush(pre)
            for line in self.assign_lines(target, value):
                self.emit(line)
            return
        if kind == "UnaryOperator" and n["opcode"] in ("++", "--"):
            base = strip(inner(n)[0])
            if base.get("kind") == "UnaryOperator" and base.get("opcode") == "*" and \
                    strip(inner(base)[0]).get("kind") == "CXXThisExpr":
                if n.get("isPostfix"):
                    raise Unsupported("postfix increment of this in a dependent expression")
                self.self_call("operator" + n["opcode"], [], pre)
                self.flush(pre)
                return
            target = self.lvalue(inner(n)[0])
            if target[3].kind not in ("int", "u32", "u64"):
                raise Unsupported("increment of a non-integer")
            current = self.read_lvalue(target)
            sym = "+" if n["opcode"] == "++" else "-"
            for line in self.assign_lines(target, f"({current} {sym} 1)"):
                self.emit(line)
            return
        if kind == "ConditionalOperator" and self.is_assert(n):
            ct, _ = self.expr(inner(n)[0], pre, BOOL)
            self.flush(pre)
            self.emit(f"Cpp.check {ct}")
            return
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            if self.vector_stmt(n):
                return
            if self.std_stmt(n):
                return
            self.call(n, pre)
            self.flush(pre)
            return
        if kind == "CXXOperatorCallExpr" and self.operator_name(n) in ("++", "--"):
            self.expr(n, pre)
            self.flush(pre)
            return
        if kind in ("BinaryOperator", "CXXOperatorCallExpr"):
            op = n.get("opcode") if kind == "BinaryOperator" else self.operator_name(n)
            if op in ("<<", ">>"):
                self.expr(n, pre)
                self.flush(pre)
                return
        raise Unsupported(f"statement {kind}")

    def is_assert(self, n):
        """`assert(c)` expands to `static_cast<bool>(c) ? void(0) : __assert_fail(...)`."""
        kids = inner(n)
        if len(kids) != 3:
            return False
        def calls_assert_fail(x):
            if not isinstance(x, dict):
                return False
            if x.get("kind") == "DeclRefExpr" and x.get("referencedDecl", {}).get("name") == "__assert_fail":
                return True
            if x.get("kind") == "UnresolvedLookupExpr" and x.get("name") == "__assert_fail":
                return True
            return any(calls_assert_fail(c) for c in x.get("inner", []))
        return calls_assert_fail(kids[2])

    def binary_parts_text(self, op, current, cty, rhs, pre):
        """`x op= rhs`: `x = (type of x)(x op rhs)`."""
        rt, rty = self.expr(rhs, pre)
        value, vty = self.arith(op, current, cty, None, rt, rty, rhs)
        return self.convert(value, vty, cty)

    def vector_stmt(self, n):
        kids = inner(n)
        callee = strip(kids[0])
        if callee.get("kind") not in ("MemberExpr", "CXXDependentScopeMemberExpr", "UnresolvedMemberExpr"):
            return False
        name = callee.get("name") or callee.get("member")
        if callee.get("kind") == "UnresolvedMemberExpr":
            name = self.tr.member_token(callee)
        base = inner(callee)[0] if inner(callee) else None
        if base is None:
            return False
        sb = strip(base)
        if sb.get("kind") == "CXXThisExpr":
            return False
        pre0 = []
        try:
            bt, bty = self.expr(base, pre0)
        except Unsupported:
            return False
        if bty.kind == "optional":
            args = kids[1:]
            pre = list(pre0)
            target = self.lvalue(base)
            if name == "reset" and not args:
                value = self.default_value(bty)
            elif name == "emplace" and len(args) == 1:
                item, _ = self.expr(args[0], pre, bty.args[0])
                value = f"(some {item})"
            else:
                return False
            self.flush(pre)
            for line in self.assign_lines(target, value):
                self.emit(line)
            return True
        if bty.kind == "ordered_set":
            if name not in ("insert", "erase") or len(kids) != 2:
                return False
            target = self.lvalue(base)
            if pre0 or any(part != "field" for part, _ in target[1]):
                raise Unsupported("set updates require a pure local or member receiver")
            pre = []
            key, _ = self.expr(kids[1], pre, bty.args[0])
            fn = "orderedSetInsert" if name == "insert" else "orderedSetErase"
            tmp = self.fresh()
            pre.append(f"let {tmp} ← Cpp.{fn} {self.pq_order(bty)} {self.read_lvalue(target)} {key}")
            self.flush(pre)
            for line in self.assign_lines(target, tmp):
                self.emit(line)
            return True
        if bty.kind in ("pq", "stack", "queue"):
            args = [a for a in kids[1:] if strip(a).get("kind") != "CXXDefaultArgExpr"]
            target = self.lvalue(base)
            cur = self.read_lvalue(target)
            elem = bty.args[0]
            pre = list(pre0)
            tmp = self.fresh()
            if name in ("push", "emplace"):
                if name == "emplace" and len(args) == 2 and elem.kind == "pair":
                    a = self.expr(args[0], pre, elem.args[0])[0]
                    b = self.expr(args[1], pre, elem.args[1])[0]
                    value = f"({a}, {b})"
                elif len(args) == 1:
                    value, _ = self.expr(args[0], pre, elem)
                else:
                    raise Unsupported(f"{bty.kind}::{name} arguments")
                fn = f"Cpp.{bty.kind}Push"
                pre.append(f"let {tmp} ← {fn} {cur} {value}")
            elif name == "pop" and not args:
                if bty.kind in ("stack", "queue"):
                    pre.append(f"let {tmp} ← Cpp.{bty.kind}Pop {cur}")
                else:
                    self.need("Inhabited", elem)
                    pre.append(f"let {tmp} ← Cpp.pqPop {self.pq_order(bty)} {cur}")
            else:
                raise Unsupported(f"{bty.kind}::{name}")
            self.flush(pre)
            for line in self.assign_lines(target, tmp):
                self.emit(line)
            return True
        if bty.kind == "umap" and name == "clear" and len(kids) == 1:
            target = self.lvalue(base)
            tmp = self.fresh()
            self.flush(pre0)
            self.emit(f"let {tmp} ← Cpp.umapClear {self.read_lvalue(target)}")
            for line in self.assign_lines(target, tmp):
                self.emit(line)
            return True
        if bty.kind == "deque":
            args = kids[1:]
            target = self.lvalue(base)
            if pre0:
                raise Unsupported("effects in the deque receiver")
            if name == "swap" and len(args) == 1:
                other = self.lvalue(args[0])
                if target[0] == other[0] or other[3] != bty:
                    raise Unsupported("deque swap requires separate equal-typed receivers")
                before = self.fresh()
                self.emit(f"let {before} := {self.read_lvalue(target)}")
                for line in self.assign_lines(target, self.read_lvalue(other)):
                    self.emit(line)
                for line in self.assign_lines(other, before):
                    self.emit(line)
                self.emit("Cpp.tick")
                return True
            if name != "emplace_back" or len(args) > 1:
                return False
            pre = []
            elem = bty.args[0]
            if args:
                item, _ = self.expr(args[0], pre, elem)
            else:
                item = self.default_value(elem)
            self.flush(pre)
            self.emit("Cpp.tick")
            for line in self.assign_lines(target, f"({self.read_lvalue(target)}.push {item})"):
                self.emit(line)
            return True
        if bty.kind != "vec":
            return False
        args = [a for a in kids[1:] if strip(a).get("kind") != "CXXDefaultArgExpr"]
        target = self.lvalue(base)
        cur = self.read_lvalue(target)
        elem = bty.args[0]
        pre = []
        if name == "emplace_back" and elem.kind == "tparam" and any(
                strip(a).get("kind") == "PackExpansionExpr" for a in args):
            # emplace_back(a, b, args...) of a class type parameter E: E's constructor on the tuple
            # (a, b, args) through Cpp.Construct, which updates the constructor state.
            if not args or strip(args[-1]).get("kind") != "PackExpansionExpr" or \
                    sum(strip(a).get("kind") == "PackExpansionExpr" for a in args) != 1:
                raise Unsupported("a forwarded pack must be the last constructor argument")
            if self.lookup(CONSTRUCT_STATE) is None:
                raise Unsupported("construction of a class type parameter without its state")
            packed = strip(inner(strip(args[-1]))[0])
            pack_name = packed.get("referencedDecl", {}).get("name")
            pty = self.lookup(pack_name) if packed.get("kind") == "DeclRefExpr" else None
            if pty is None or pty.kind != "tparam" or pty.name not in self.tr.packs:
                raise Unsupported("a forwarded pack must be a pack parameter")
            texts, tys = [], []
            for a in args[:-1]:
                at, aty = self.expr(a, pre)
                texts.append(at)
                tys.append(aty)
            texts.append(self.var_name(pack_name))
            tys.append(pty)
            tuple_text = "(" + ", ".join(texts) + ")" if len(texts) > 1 else texts[0]
            tuple_ty = " × ".join(lean_type(t) for t in tys)
            self.reqs.add(f"Cpp.ConstructState {lean_type(elem)}")
            self.reqs.add(f"Cpp.Construct {lean_type(elem)} ({tuple_ty})")
            state = self.var_name(CONSTRUCT_STATE)
            tmp = self.fresh()
            self.flush(pre)
            self.emit(f"let {tmp} ← Cpp.Construct.make (E := {lean_type(elem)}) (Args := {tuple_ty}) {tuple_text} {state}")
            self.emit(f"{state} := {tmp}.2")
            self.emit("Cpp.tick")
            for line in self.assign_lines(target, f"({self.read_lvalue(target)}.push {tmp}.1)"):
                self.emit(line)
            return True
        if name in ("push_back", "emplace_back"):
            if name == "emplace_back" and len(args) != 1:
                if not args and (elem.kind in ("int", "u32", "u64", "bool")
                                 or (elem.kind == "vec" and elem.length is None)):
                    value = self.default_value(elem)
                elif elem.kind == "pair" and len(args) == 2:
                    a = self.expr(args[0], pre, elem.args[0])[0]
                    b = self.expr(args[1], pre, elem.args[1])[0]
                    value = f"({a}, {b})"
                elif elem.kind == "tuple" and len(args) == len(elem.args):
                    value = self.tuple_value(elem, args, pre)
                elif elem.kind == "tparam" and len(args) >= 3 and self.lookup(CONSTRUCT_STATE) is not None:
                    before_args = len(pre)
                    values = [self.expr(arg, pre) for arg in args]
                    if len(pre) != before_args:
                        raise Unsupported("effects in dependent emplace_back arguments")
                    value = self.construct_call(elem, [text for text, _ in values] + ["()"],
                                                [lean_type(ty) for _, ty in values] + ["Unit"], pre)
                else:
                    raise Unsupported("emplace_back arguments")
            else:
                value, _ = self.expr(args[0], pre, elem)
            self.flush(pre)
            self.emit("Cpp.tick")
            for line in self.assign_lines(target, f"({cur}.push {value})"):
                self.emit(line)
            return True
        if name == "pop_back" and not args:
            for line in self.assign_lines(target, f"{cur}.pop"):
                self.emit(line)
            return True
        if name == "clear" and not args:
            for line in self.assign_lines(target, f"([] : List {lean_type(elem)}).toArray"):
                self.emit(line)
            return True
        if name == "assign" and len(args) == 2 and self.whole_range(args[0], args[1]) is not None:
            # v.assign(w.begin(), w.end()): a copy of w (one tick per element)
            src = self.whole_range(args[0], args[1])
            st, sty = self.expr(src, pre)
            if sty != bty:
                raise Unsupported("assign from a vector of another type")
            tmp = self.fresh()
            pre.append(f"let {tmp} := {st}")
            pre.append(f"Cpp.tickN {tmp}.size")
            self.flush(pre)
            for line in self.assign_lines(target, tmp):
                self.emit(line)
            return True
        if name in ("resize", "assign") and len(args) in (1, 2):
            nt, _ = self.expr(args[0], pre, INT)
            vt = self.expr(args[1], pre, elem)[0] if len(args) == 2 else self.default_value(elem)
            tmp = self.fresh()
            pre.append(f"let {tmp} := {nt}")
            pre.append(f"Cpp.tickN {tmp}.toNat")
            self.flush(pre)
            value = f"(Cpp.resize {cur} {tmp} {vt})" if name == "resize" else f"(Cpp.replicate {tmp} {vt})"
            for line in self.assign_lines(target, value):
                self.emit(line)
            return True
        if name == "reserve":
            return True
        if name == "erase" and len(args) == 2:
            # v.erase(std::unique(v.begin(), v.end()), v.end()): collapse runs of equal elements (O(n))
            call = peel(args[0])
            ck = inner(call)
            callee = strip(ck[0]) if ck else {}
            cname = callee.get("referencedDecl", {}).get("name") if callee.get("kind") == "DeclRefExpr" else callee.get("name")
            if call.get("kind") != "CallExpr" or cname != "unique" or len(ck) != 3:
                raise Unsupported("vector::erase other than the erase-unique idiom")
            src = self.whole_range(ck[1], ck[2])
            endb = peel(args[1])
            if src is None or endb.get("kind") not in ("CXXMemberCallExpr", "CallExpr"):
                raise Unsupported("vector::erase other than the erase-unique idiom")
            ecallee = strip(inner(endb)[0])
            if (ecallee.get("name") or ecallee.get("member")) != "end" \
                    or self.lvalue(inner(ecallee)[0])[:2] != target[:2] or self.lvalue(src)[:2] != target[:2]:
                raise Unsupported("vector::erase other than the erase-unique idiom")
            if elem.kind in ("tparam", "int", "u32", "u64", "bool"):
                self.need("DecidableEq", elem)
            else:
                raise Unsupported(f"std::unique of {elem}")
            self.flush(pre)
            self.emit(f"Cpp.tickN {cur}.size")
            for line in self.assign_lines(target, f"(Cpp.unique {cur})"):
                self.emit(line)
            return True
        raise Unsupported(f"vector::{name}")

    def whole_range(self, a, b):
        """The vector `w` when the arguments are `w.begin(), w.end()` (the same variable), else None."""
        def member(node, want):
            node = peel(node)
            if node.get("kind") not in ("CXXMemberCallExpr", "CallExpr") or len(inner(node)) != 1:
                return None
            callee = strip(inner(node)[0])
            if callee.get("kind") not in ("MemberExpr", "CXXDependentScopeMemberExpr") or not inner(callee) \
                    or (callee.get("name") or callee.get("member")) != want:
                return None
            return strip(inner(callee)[0])
        x, y = member(a, "begin"), member(b, "end")
        if x is None or y is None or x.get("kind") != "DeclRefExpr" or y.get("kind") != "DeclRefExpr":
            return None
        if x.get("referencedDecl", {}).get("id") != y.get("referencedDecl", {}).get("id"):
            return None
        return x

    def std_stmt(self, n):
        kids = inner(n)
        callee = strip(kids[0])
        if callee.get("kind") not in ("DeclRefExpr", "UnresolvedLookupExpr"):
            return False
        name = callee.get("referencedDecl", {}).get("name") if callee.get("kind") == "DeclRefExpr" \
            else callee.get("name")
        args = kids[1:]
        if name == "swap" and len(args) == 2:
            a = self.lvalue(args[0])
            b = self.lvalue(args[1])
            tmp = self.fresh()
            self.emit(f"let {tmp} := {self.read_lvalue(a)}")
            for line in self.assign_lines(a, self.read_lvalue(b)):
                self.emit(line)
            for line in self.assign_lines(b, tmp):
                self.emit(line)
            return True
        if name == "assert" or name == "__assert_fail":
            raise Unsupported("assert")
        if name in ("iota", "stable_sort", "reverse") and len(args) == (2 if name == "reverse" else 3):
            bases = []
            for arg, which in zip(args[:2], ("begin", "end")):
                call = strip(arg)
                callee = strip(inner(call)[0]) if inner(call) else {}
                member = callee.get("name") or callee.get("member")
                if call.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or member != which or not inner(callee):
                    raise Unsupported(f"std::{name} over a range other than v.begin(), v.end()")
                bases.append(inner(callee)[0])
            target = self.lvalue(bases[0])
            if self.lvalue(bases[1])[:2] != target[:2]:
                raise Unsupported(f"std::{name} over two different vectors")
            if target[3].kind != "vec":
                raise Unsupported(f"std::{name} of a non-vector")
            elem = target[3].args[0]
            cur = self.read_lvalue(target)
            if name == "reverse":
                # std::reverse(v.begin(), v.end()): Array.reverse, one step per element.
                self.emit(f"Cpp.tickN {cur}.size")
                for line in self.assign_lines(target, f"{cur}.reverse"):
                    self.emit(line)
                return True
            if name == "iota":
                # std::iota(v.begin(), v.end(), x): v[i] = x + i, one step per element.
                if elem.kind != "int":
                    raise Unsupported(f"std::iota of {elem}")
                pre = []
                start, _ = self.expr(args[2], pre, elem)
                self.flush(pre)
                self.emit(f"Cpp.tickN {cur}.size")
                for line in self.assign_lines(target, f"(Cpp.iota {cur}.size {start})"):
                    self.emit(line)
                return True
            # std::stable_sort(v.begin(), v.end(), [&](E a, E b) { return e; }): a stable merge sort by the
            # comparator, O(n log n) comparisons. The comparator must be a lambda whose body is one return of a
            # pure expression over its parameters and captured variables.
            lam = strip(args[2])
            if lam.get("kind") != "LambdaExpr":
                raise Unsupported("std::stable_sort comparator other than a lambda")
            record = next((c for c in inner(lam) if c.get("kind") == "CXXRecordDecl"), None)
            call_op = next((c for c in inner(record or {}) if c.get("kind") == "CXXMethodDecl"
                            and c.get("name") == "operator()"), None)
            body = inner(lam)[-1] if inner(lam) else {}
            if call_op is None or body.get("kind") != "CompoundStmt":
                raise Unsupported("std::stable_sort comparator shape")
            params = [c for c in inner(call_op) if c.get("kind") == "ParmVarDecl"]
            stmts = inner(body)
            if len(params) != 2 or len(stmts) != 1 or stmts[0].get("kind") != "ReturnStmt" or not inner(stmts[0]):
                raise Unsupported("std::stable_sort comparator must be one return of two parameters")
            self.scopes.append({})
            names = []
            for p in params:
                pty = self.tr.ty(type_of_decl(p), self)
                if pty != elem:
                    raise Unsupported("std::stable_sort comparator parameter type")
                self.declare(p["name"], pty)
                names.append(self.scopes[-1]["__names__"][p["name"]])
            pre = []
            cmp, _ = self.expr(inner(stmts[0])[0], pre, BOOL)
            self.scopes.pop()
            if pre:
                raise Unsupported("std::stable_sort comparator with calls or steps")
            self.emit(f"Cpp.tickN (Cpp.sortCost {cur}.size)")
            for line in self.assign_lines(target, f"(Cpp.stableSortBy (fun {names[0]} {names[1]} => {cmp}) {cur})"):
                self.emit(line)
            return True
        if name == "sort" and len(args) == 2:
            bases = []
            for arg, which in zip(args, ("begin", "end")):
                call = strip(arg)
                callee = strip(inner(call)[0]) if inner(call) else {}
                member = callee.get("name") or callee.get("member")
                if call.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or member != which or not inner(callee):
                    raise Unsupported("std::sort over a range other than v.begin(), v.end()")
                bases.append(inner(callee)[0])
            target = self.lvalue(bases[0])
            if self.lvalue(bases[1])[:2] != target[:2]:
                raise Unsupported("std::sort over two different vectors")
            if target[3].kind != "vec":
                raise Unsupported("std::sort of a non-vector")
            elem = target[3].args[0]
            fn = "Cpp.sort"
            if elem.kind == "pair":
                # operator< of std::pair is lexicographic
                fn = "Cpp.sortLex"
                for comp in elem.args:
                    if comp.kind not in ("tparam", "int", "u32", "u64", "bool"):
                        raise Unsupported(f"std::sort of pairs of {comp}")
                    self.need("LT", comp)
                    self.need("DecidableLT", comp)
                self.need("DecidableEq", elem.args[0])
            elif elem.kind in ("tparam", "int", "u32", "u64"):
                self.need("LT", elem)
                self.need("DecidableLT", elem)
            else:
                raise Unsupported(f"std::sort of {elem}")
            cur = self.read_lvalue(target)
            self.emit(f"Cpp.tickN (Cpp.sortCost {cur}.size)")
            for line in self.assign_lines(target, f"({fn} {cur})"):
                self.emit(line)
            return True
        return False

    # ------------------------------------------------------------------ loops
    def assigned_names(self, node, out=None):
        """Variables (and fields) a statement may change."""
        if out is None:
            out = set()
        if not isinstance(node, dict):
            return out
        kind = node.get("kind")
        def root(n, dependent=False):
            """The changed variable; `v[]` when only elements of `v` change (its size does not)."""
            n = strip_casts(n)
            element = False
            while True:
                k = n.get("kind")
                if k == "DeclRefExpr":
                    return n["referencedDecl"]["name"] + ("[]" if element else "")
                if k == "MemberExpr" or (dependent and k == "CXXDependentScopeMemberExpr" and inner(n) and not n.get("isArrow")):
                    b = strip(inner(n)[0])
                    if b.get("kind") == "CXXThisExpr":
                        return "this." + (n.get("name") or n["member"]) + ("[]" if element else "")
                    n = b
                    continue
                if k == "ArraySubscriptExpr":
                    element = True
                    n = strip(inner(n)[0])
                    continue
                if k == "CXXOperatorCallExpr" and self.operator_name(n) == "[]":
                    element = True
                    n = strip(inner(n)[1])
                    continue
                return None
        if kind in ("BinaryOperator", "CXXOperatorCallExpr"):
            op = node.get("opcode") if kind == "BinaryOperator" else self.operator_name(node)
            if op in ("<<", ">>"):
                base = self.stream_base(node)
                try:
                    sty = self.tr.ty(base.get("type", {}).get("qualType", ""), self)
                except Unsupported:
                    sty = None
                if sty is not None and sty.kind in ("istream", "ostream"):
                    out.add(root(base))
                    if op == ">>":
                        out.add(root(inner(node)[1 if kind == "BinaryOperator" else 2]))
        if kind in ("BinaryOperator",) and node.get("opcode") == "=":
            out.add(root(inner(node)[0], dependent=True))
        if kind == "CompoundAssignOperator":
            out.add(root(inner(node)[0], dependent=True))
        if kind == "UnaryOperator" and node.get("opcode") in ("++", "--"):
            out.add(root(inner(node)[0], dependent=True))
        if kind == "CXXOperatorCallExpr" and self.operator_name(node).endswith("=") and \
                self.operator_name(node) not in ("==", "!=", "<=", ">="):
            out.add(root(inner(node)[1], dependent=True))
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            callee = strip(inner(node)[0])
            if callee.get("kind") in ("MemberExpr", "CXXDependentScopeMemberExpr", "UnresolvedMemberExpr") and inner(callee):
                name = callee.get("name") or callee.get("member")
                if name is None and callee.get("kind") == "UnresolvedMemberExpr":
                    name = self.tr.member_token(callee)
                on_this = strip(inner(callee)[0]).get("kind") == "CXXThisExpr"
                read_only_member = on_this and self.cls is not None and any(
                    m.cpp_name == name for m in self.cls.methods) and all(
                    m.is_const or m.preserves_receiver for m in self.cls.methods if m.cpp_name == name)
                if read_only_member:
                    # A receiver-preserving member can still change its reference arguments.
                    refs = set()
                    for m in self.cls.methods:
                        if m.cpp_name == name:
                            refs |= {i for i, p in enumerate(m.params) if p[2]}
                    for i, a in enumerate(inner(node)[1:]):
                        if i in refs:
                            out.add(root(a))
                elif name not in ("size", "empty", "back", "front"):
                    out.add(root(inner(callee)[0]))
                    if on_this:
                        out.add("this.*")
            elif callee.get("referencedDecl", {}).get("name") == "__assert_fail" or callee.get("name") == "__assert_fail":
                pass   # a failed assert stops the call; it changes nothing the loop could observe
            elif (callee.get("referencedDecl", {}).get("name") or callee.get("name")) in ("min", "max") and \
                    re.match(r"std::(min|max)\b", re.sub(r"\s+", "", self.tr.span(node))):
                pass   # std::min / std::max change nothing
            elif (callee.get("referencedDecl", {}).get("name") or callee.get("name")) in ("reverse", "sort") and \
                    re.match(r"std::(reverse|sort)\(", re.sub(r"\s+", "", self.tr.span(node))):
                # std::reverse / std::sort(v.begin(), v.end()) change only the elements of v
                for a in inner(node)[1:]:
                    c = strip(a)
                    if c.get("kind") in ("CXXMemberCallExpr", "CallExpr") and inner(c):
                        member = strip(inner(c)[0])
                        if inner(member):
                            out.add(root(inner(member)[0]))
            else:
                out.add("*call")
                for a in inner(node)[1:]:
                    out.add(root(a))
        for c in inner(node):
            self.assigned_names(c, out)
        return out

    def read_names(self, node, out=None):
        if out is None:
            out = set()
        if not isinstance(node, dict):
            return out
        kind = node.get("kind")
        if kind == "DeclRefExpr":
            out.add(node["referencedDecl"]["name"])
        if kind == "MemberExpr" and strip(inner(node)[0]).get("kind") == "CXXThisExpr":
            out.add("this." + node["name"])
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            callee = strip(inner(node)[0])
            name = callee.get("name") or callee.get("member")
            if name == "size" and inner(callee):
                base = strip(inner(callee)[0])
                if base.get("kind") == "DeclRefExpr":
                    out.add(base["referencedDecl"]["name"] + ".size")
                    return out
                if base.get("kind") == "MemberExpr" and strip(inner(base)[0]).get("kind") == "CXXThisExpr":
                    out.add("this." + base["name"] + ".size")
                    return out
            elif name not in ("size",):
                out.add("*call")
        for c in inner(node):
            self.read_names(c, out)
        return out

    def conflicts(self, read, changed):
        """Whether a change in `changed` can affect an expression reading `read`."""
        if "*call" in read:
            return True
        for r in read:
            if r.endswith(".size"):
                if r.removesuffix(".size") in changed:
                    return True
            elif r in changed or r + "[]" in changed:
                return True
            if r.startswith("this.") and ("this.*" in changed or "*call" in changed):
                return True
        return False

    def counted(self, init, cond, inc, body):
        """Recognise `for (int i = a; i < b; i++)` / `for (int i = a; i >= b; i--)`. Returns (var, list text) or None."""
        if init is None or init.get("kind") != "DeclStmt" or len(inner(init)) != 1:
            return None
        d = inner(init)[0]
        if d.get("kind") != "VarDecl" or self.tr.ty(type_of_decl(d), self) != INT or not inner(d):
            return None
        var = d["name"]
        if cond is None or inc is None:
            return None
        c = strip(cond)
        if c.get("kind") != "BinaryOperator" or c["opcode"] not in ("<", "<=", ">=", ">"):
            return None
        lhs = strip(inner(c)[0])
        if lhs.get("kind") != "DeclRefExpr" or lhs["referencedDecl"]["name"] != var:
            return None
        i = strip(inc)
        step = None
        if i.get("kind") == "UnaryOperator" and i["opcode"] in ("++", "--"):
            target = strip(inner(i)[0])
            if target.get("kind") == "DeclRefExpr" and target["referencedDecl"]["name"] == var:
                step = 1 if i["opcode"] == "++" else -1
        if step is None:
            return None
        if (step == 1) != (c["opcode"] in ("<", "<=")):
            return None
        changed = self.assigned_names(body)
        bound = inner(c)[1]
        read = self.read_names(bound)
        if var in changed or var + "[]" in changed or self.conflicts(read, changed):
            return None
        return var, inner(d)[0], c["opcode"], bound, step

    def for_stmt(self, node):
        kids = node.get("inner", [])
        init, _, cond, inc, body = kids
        init = init if isinstance(init, dict) and init else None
        cond = cond if isinstance(cond, dict) and cond else None
        inc = inc if isinstance(inc, dict) and inc else None
        pattern = self.counted(init, cond, inc, body)
        self.scopes.append({})
        if pattern is not None:
            var, start, op, bound, step = pattern
            pre = []
            a, _ = self.expr(start, pre, INT)
            b, _ = self.expr(bound, pre, INT)
            self.flush(pre)
            if op == "<":
                rng = f"(Cpp.range {a} {b})"
            elif op == "<=":
                rng = f"(Cpp.range {a} ({b} + 1))"
            elif op == ">=":
                rng = f"(Cpp.rangeDown {b} {a})"
            else:
                rng = f"(Cpp.rangeDown ({b} + 1) {a})"
            self.declare(var, INT)
            self.emit(f"for {self.var_name(var)} in {rng} do")
            self.indent += 1
            self.emit("Cpp.tick")
            self.continue_prefix.append([])
            self.block(body)
            self.continue_prefix.pop()
            self.indent -= 1
        else:
            if init is not None:
                # the variable of the initializer is local to the loop
                self.emit("do")
                self.indent += 1
                self.stmt(init)
            inc_lines = []
            if inc is not None:
                saved = self.lines
                self.lines = []
                saved_indent = self.indent
                self.indent = 0
                self.expr_stmt(inc)
                inc_lines = [l.strip() for l in self.lines]
                self.lines = saved
                self.indent = saved_indent
            self.while_loop(None, cond, body, inc_lines)
            if init is not None:
                self.indent -= 1
        self.scopes.pop()

    def while_loop(self, _init, cond, body, inc_lines):
        self.emit("for _ in Cpp.forever do")
        self.indent += 1
        self.emit("Cpp.tick")
        if cond is not None:
            pre = []
            ct, _ = self.expr(cond, pre, BOOL)
            self.flush(pre)
            self.emit(f"if !{ct} then break")
        self.continue_prefix.append(inc_lines)
        self.block(body)
        self.continue_prefix.pop()
        for line in inc_lines:
            self.emit(line)
        self.indent -= 1

    def range_for(self, node):
        kids = inner(node)
        decls = [k for k in kids if k.get("kind") == "DeclStmt"]
        if len(decls) < 2:
            raise Unsupported("range for without a loop variable")
        rng_init = inner(inner(decls[0])[0])[0]
        loop = inner(decls[-1])[0]
        body = kids[-1]
        pre = []
        rt, rty = self.expr(rng_init, pre)
        if rty.kind != "vec":
            raise Unsupported("range for over a non-vector")
        elem = rty.args[0]
        qual = type_of_decl(loop)
        changed = self.assigned_names(body)
        read = {r.removesuffix(".size") for r in self.read_names(rng_init)}
        if self.conflicts(read, changed):
            raise RangeMutation("range for over a vector the body changes")
        if loop.get("kind") == "DecompositionDecl":
            names = [b["name"] for b in inner(loop) if b.get("kind") == "BindingDecl"]
            if elem.kind != "pair" or len(names) != 2:
                raise Unsupported("structured binding of a non-pair")
            if any(n in changed or n + "[]" in changed for n in names):
                raise Unsupported("assignment through a structured binding")
            bound = list(zip(names, elem.args))
        else:
            if "&" in qual and "const" not in qual and loop["name"] in changed:
                raise Unsupported("range for by mutable reference")
            bound = None
        self.flush(pre)
        self.scopes.append({})
        if bound is None:
            self.declare(loop["name"], elem)
            self.emit(f"for {self.var_name(loop['name'])} in {rt} do")
            self.indent += 1
            self.emit("Cpp.tick")
        else:
            item = self.fresh()
            self.emit(f"for {item} in {rt} do")
            self.indent += 1
            self.emit("Cpp.tick")
            for k, (name, ty) in enumerate(bound):
                self.declare(name, ty)
                self.emit(f"let {self.var_name(name)} : {lean_type(ty)} := {item}.{k + 1}")
        self.continue_prefix.append([])
        self.block(body)
        self.continue_prefix.pop()
        self.indent -= 1
        self.scopes.pop()


def subst(ty: Ty, names, args):
    if ty.kind in ("tparam", "vparam") and ty.name in names:
        i = names.index(ty.name)
        return args[i] if i < len(args) else ty
    if ty.args:
        return Ty(ty.kind, ty.name, tuple(subst(a, names, args) for a in ty.args), width=ty.width,
                  length=subst(ty.length, names, args) if ty.length is not None else None)
    return ty


# ------------------------------------------------------------------------------------------ translator

class Translator:
    def __init__(self, decls, source_bytes=b"", external=()):
        self.source_bytes = source_bytes
        normalized = expose_nested_deque_records(normalize_ordered_set_key_adapters(decls), source_bytes)
        self.decls = [self.bind_stdout(decl) for decl in normalized]
        self.external = list(external)   # (decls, source bytes) of the dependencies: callable, not emitted          # list of top-level AST nodes in source order
        self.classes: dict[str, ClassInfo] = {}
        self.aliases: dict[str, Ty] = {}
        self.nested_record_names = {}
        self.constants: dict[str, tuple[str, Ty, str]] = {}
        self.static_constant_methods: set[str] = set()
        self.globals: dict[str, tuple[str, Ty, int | None]] = {}
        self.global_initializers: dict[str, dict] = {}
        self.local_statics: set[str] = set()
        self.static_members: dict[str, str] = {}
        self.static_member_literals: dict[str, str] = {}
        self.static_member_definitions: dict[str, str] = {}
        self.global_state_name = "cp.GlobalState"
        self.static_family = None          # (class name, its type parameter) of a templated static counter
        self.dep_layouts = {}              # dependency class template -> (type parameters, {field: type text})
        self.tparam_defaults = {}          # type parameter -> the spelling of its default argument
        self.packs = set()                 # type parameter packs
        self.static_family_member = None
        self.static_tag = "cppStaticSpecialization"
        while re.search(rb"\b" + self.static_tag.encode() + rb"\b", source_bytes):
            self.static_tag += "_"
        self.functions: dict[str, list[Sig]] = {}
        self.qualified_functions: dict[str, str] = {}
        self.order: list = []       # ("class", ClassInfo) / ("fn", Sig)
        self.tparams_stack: list[set] = []

    def bind_stdout(self, node):
        """Give direct uses of the standard output stream a model-only mutable parameter."""
        if node.get("kind") in ("FunctionDecl", "CXXMethodDecl"):
            body = next((child for child in inner(node) if child.get("kind") == "CompoundStmt"), None)
            if body is None:
                return node
            name = "cppStdout"
            while re.search(rb"\b" + name.encode() + rb"\b", self.source_bytes):
                name += "_"
            declaration = {"kind": "ParmVarDecl", "id": "lean_stdout:" + node["id"], "name": name,
                           "type": {"qualType": "std::ostream &"}}

            def replace(part):
                ref = part.get("referencedDecl", {})
                if (part.get("kind") == "DeclRefExpr" and ref.get("kind") == "VarDecl"
                        and ref.get("name") == "cout"
                        and ref.get("type", {}).get("desugaredQualType") == "std::basic_ostream<char>"
                        and re.fullmatch(r"(?:\s*::)?\s*std\s*::\s*cout", self.span(part))):
                    return {**part, "referencedDecl": declaration}
                children = inner(part)
                if children:
                    return {**part, "inner": [replace(child) for child in children]}
                return part

            rewritten = replace(body)
            if rewritten == body:
                return node
            if return_type_text(node["type"]["qualType"]) != "void":
                raise Unsupported("implicit standard output requires a void function")
            children = [rewritten if child is body else child for child in inner(node)]
            children.insert(children.index(rewritten), declaration)
            return {**node, "inner": children, "lean_stdout_parameter": name}
        if node.get("kind") in ("ClassTemplateDecl", "CXXRecordDecl", "FunctionTemplateDecl"):
            return {**node, "inner": [self.bind_stdout(child) for child in inner(node)]}
        return node

    def token(self, node):
        """The first token of a node (Clang's JSON omits the name of some unresolved expressions)."""
        begin = node.get("range", {}).get("begin", {})
        begin = begin.get("spellingLoc", begin)
        if "offset" not in begin or "tokLen" not in begin:
            raise Unsupported(f"no source location for {node.get('kind')}")
        return self.source_bytes[begin["offset"]:begin["offset"] + begin["tokLen"]].decode()

    def member_token(self, node):
        end = node.get("range", {}).get("end", {})
        if "spellingLoc" in end or "offset" not in end or "tokLen" not in end:
            raise Unsupported("unresolved member name requires a direct source token")
        name = self.source_bytes[end["offset"]:end["offset"] + end["tokLen"]].decode()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            raise Unsupported("unresolved member name token")
        return name

    def span(self, node):
        """The source text of a node."""
        rng = node.get("range", {})
        begin = rng.get("begin", {})
        end = rng.get("end", {})
        begin = begin.get("spellingLoc", begin)
        end = end.get("spellingLoc", end)
        if "offset" not in begin or "offset" not in end or "tokLen" not in end:
            raise Unsupported(f"no source range for {node.get('kind')}")
        return self.source_bytes[begin["offset"]:end["offset"] + end["tokLen"]].decode()

    def ty(self, text, fn: Fn | None = None):
        tps = set()
        values = {}
        if fn is not None:
            tps = set(fn.sig.tparams) | (set(fn.cls.tparams) if fn.cls else set())
            values = {**(fn.cls.value_params if fn.cls else {}), **fn.sig.value_params}
            text = container_text(text, fn.sig.containers)
        aliases = {**self.aliases, **fn.local_aliases} if fn is not None else self.aliases
        return parse_type(text, tps - values.keys(), self.classes, values, aliases)

    def type_constraint(self, expression, names, values):
        def unwrap(text):
            while text.startswith("(") and text.endswith(")"):
                depth = 0
                for i, ch in enumerate(text):
                    depth += (ch == "(") - (ch == ")")
                    if depth == 0:
                        break
                if i != len(text) - 1:
                    break
                text = text[1:-1]
            return text
        expression = unwrap(re.sub(r"\s+", "", expression))
        negated = expression.startswith("!")
        if negated:
            rest = expression[1:]
            if "||" in rest and not rest.startswith("("):
                raise Unsupported("unparenthesized negated type constraint")
            expression = unwrap(rest)
        match = re.fullmatch(r"std::is_signed_v<(\w+)>(.*)", expression)
        if not match:
            raise Unsupported("unsupported type constraint")
        parameter, tail = match.groups()
        if parameter not in names or parameter in values:
            raise Unsupported("type constraint requires a type parameter")
        predicate = f'(Cpp.TypeTraits.isSigned (tag := "{parameter}") (α := {parameter}))'
        if tail:
            expected = f"||std::is_same_v<std::remove_cv_t<{parameter}>,__int128>"
            if tail != expected:
                raise Unsupported("unsupported compound type constraint")
            predicate = f'({predicate} || (Cpp.TypeTraits.isCvInt128 (tag := "{parameter}") (α := {parameter})))'
        return f"({predicate} = {'false' if negated else 'true'})"

    def template_params(self, node, allow_constraints=False, allow_type_constraints=False):
        names, values, constraints = [], {}, []
        for param in inner(node):
            kind = param.get("kind")
            if kind not in ("TemplateTypeParmDecl", "NonTypeTemplateParmDecl", "TemplateTemplateParmDecl"):
                continue
            name = param.get("name")
            if (allow_constraints and not name and kind == "NonTypeTemplateParmDecl"
                    and not param.get("isParameterPack")):
                spelling = type_of_decl(param)
                match = re.fullmatch(r"std::enable_if_t<(.*)>\s*\*", spelling)
                defaults = inner(param)
                if (not match or len(defaults) != 1 or len(inner(defaults[0])) != 1
                        or inner(defaults[0])[0].get("kind") != "CXXNullPtrLiteralExpr"):
                    raise Unsupported("template constraint requires std::enable_if_t and nullptr default")
                if allow_type_constraints and "is_signed_v" in match.group(1):
                    constraints.append(self.type_constraint(match.group(1), names, values))
                    continue
                expression = match.group(1).replace("(", "").replace(")", "")
                comparison = re.fullmatch(r"\s*(\w+)\s*(<=|>=|==|!=|<|>)\s*(\w+)\s*", expression)
                if not comparison:
                    raise Unsupported("class constraint comparison")
                left, op, right = comparison.groups()
                variable = left if left in values else right
                literal = right if left in values else left
                if (variable not in values or values[variable].kind not in ("int", "u32", "u64")
                        or not re.fullmatch(r"0|[1-9][0-9]*", literal) or int(literal) >= 2**31):
                    raise Unsupported("class constraint needs one integral parameter and a nonnegative int literal")
                ty = values[variable]
                rendered = {variable: lean_name(variable), literal: f"({int(literal)} : {lean_type(ty)})"}
                op = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(op, op)
                constraints.append(f"({rendered[left]} {op} {rendered[right]})")
                continue
            if name and param.get("isParameterPack") and kind == "TemplateTypeParmDecl":
                # A type parameter pack `class... Args`: one Lean type `Args` (the tuple of the pack, `Unit` for an
                # empty pack). Its function parameter is only forwarded as `args...` to a constructor.
                self.packs.add(name)
            elif not name or param.get("isParameterPack") or kind == "TemplateTemplateParmDecl":
                raise Unsupported(f"template parameter {kind}: named non-pack parameters required")
            if constraints:
                raise Unsupported("class constraint parameters must be trailing")
            names.append(name)
            default = param.get("defaultArg", {}).get("type", {}).get("qualType")
            if kind == "TemplateTypeParmDecl" and default:
                # a name with different defaults in different templates has no usable default (None)
                self.tparam_defaults[name] = default if self.tparam_defaults.get(name, default) == default else None
            if kind == "NonTypeTemplateParmDecl":
                ty = parse_type(type_of_decl(param), set(), self.classes, aliases=self.aliases)
                if ty.kind not in ("int", "u32", "u64", "bool") or ty.width > 64:
                    raise Unsupported(f"non-type template parameter {name}")
                values[name] = ty
        return names, values, constraints

    def inline_template_static_constants(self):
        """`static const T NAME;` in a class template with the out-of-line definition
        `template <...> const T C<...>::NAME = e;` becomes the static member function `T NAME() { return e; }` of the
        model (one step per use); its uses call it."""
        members = {}
        for node in self.decls:
            if node.get("kind") != "ClassTemplateDecl":
                continue
            rec = next((c for c in inner(node) if c.get("kind") == "CXXRecordDecl" and c.get("completeDefinition")), None)
            for c in inner(rec or {}):
                if (c.get("kind") == "VarDecl" and c.get("storageClass") == "static" and not inner(c)
                        and not c.get("constexpr") and re.search(r"\bconst\b", type_of_decl(c))
                        and not re.search(r"[&*\[]|\bvolatile\b", type_of_decl(c))):
                    members[c["id"]] = (rec, c)
        if not members:
            return
        kept = []
        for node in self.decls:
            if node.get("kind") == "VarDecl" and node.get("previousDecl") in members and len(inner(node)) >= 1:
                rec, c = members.pop(node["previousDecl"])
                init = [x for x in inner(node) if x.get("kind") != "NestedNameSpecifier"]
                if len(init) != 1:
                    raise Unsupported("static constant definition requires one initializer")
                ty = re.sub(r"\bconst\b", "", type_of_decl(c)).strip()
                c.clear()
                c.update({"kind": "CXXMethodDecl", "name": node["name"], "id": node["previousDecl"],
                          "storageClass": "static", "type": {"qualType": f"{ty} ()"},
                          "lean_static_constant": True,
                          "inner": [{"kind": "CompoundStmt", "inner": [{"kind": "ReturnStmt", "inner": init}]}]})
                self.static_constant_methods.add(node["previousDecl"])
                continue
            kept.append(node)
        self.decls[:] = kept

    def collect_constant(self, node):
        """Direct literals and fully initialized fixed arrays of direct literals."""
        spelling = type_of_decl(node)
        if not re.search(r"\bconst\b", spelling) or re.search(r"\bvolatile\b", spelling):
            raise Unsupported("global variable requires a nonvolatile constant")
        children = inner(node)
        if len(children) != 1:
            raise Unsupported("global constant requires one initializer")
        value = children[0]
        fixed = re.fullmatch(r"(.+)\[(\d+)\]", spelling)
        if fixed:
            ty = self.ty(fixed[1])
            elements = inner(value)
            if (not node.get("constexpr") or value.get("kind") != "InitListExpr"
                    or not elements or len(elements) != int(fixed[2])):
                raise Unsupported("constant array requires a full literal initializer")
            items = ", ".join(self.constant_literal(ty, e) for e in elements)
            literal = f"([{items}] : List {lean_type(ty)}).toArray"
            ty = Ty("constant_array", args=(ty,))
        else:
            ty = self.ty(spelling)
            literal = self.constant_literal(ty, value)
        self.constants[node["id"]] = (node.get("lean_cpp_name", node["name"]), ty, literal)

    def constant_literal(self, ty, value):
        if ty.kind not in ("int", "u32", "u64", "bool"):
            raise Unsupported("global constant requires a scalar literal")
        # Implicit conversions are deliberately excluded here. Their source
        # widths and signedness require a separate conversion rule.
        sign = 1
        if value.get("kind") == "UnaryOperator" and value.get("opcode") == "-":
            sign = -1
            value = inner(value)[0]
        if ty.kind == "bool" and value.get("kind") == "CXXBoolLiteralExpr" and sign == 1:
            literal = "true" if value["value"] else "false"
        elif ty.kind != "bool" and value.get("kind") == "IntegerLiteral":
            source_ty = self.ty(type_of_decl(value))
            number = sign * int(value["value"])
            width = 32 if ty.kind == "u32" else 64 if ty.kind == "u64" else ty.width
            lower, upper = (-(2**(width-1)), 2**(width-1)) if ty.kind == "int" else (0, 2**width)
            if source_ty.kind != ty.kind or source_ty.width != ty.width or not lower <= number < upper:
                raise Unsupported("global constant literal conversion or range")
            literal = str(number)
        else:
            raise Unsupported("global constant initializer is not a direct scalar literal")
        return literal

    def collect_global(self, node):
        spelling = type_of_decl(node)
        if node.get("tls"):
            raise Unsupported("thread-local global state")
        if re.search(r"\b(?:const|volatile)\b|[&*]", spelling):
            raise Unsupported("global state requires a mutable nonvolatile value")
        array = re.fullmatch(r"(.+)\[(\d+)\]", spelling)
        size = int(array[2]) if array else None
        ty = self.ty(array[1].strip() if array else spelling)
        if ty.kind not in ("int", "u32", "u64", "bool", "cls"):
            raise Unsupported("global state value type")
        if size is not None:
            if size == 0:
                raise Unsupported("zero-length global array")
            ty = Ty("vec", args=(ty,))
        element = ty.args[0] if size is not None else ty
        initializers = inner(node)
        if element.kind == "cls":
            if (len(initializers) != 1 or initializers[0].get("kind") != "CXXConstructExpr"
                    or inner(initializers[0]) or initializers[0].get("ctorType", {}).get("qualType") != "void ()"
                    or initializers[0].get("range", {}).get("begin", {}).get("offset") != node.get("loc", {}).get("offset")):
                raise Unsupported("global class requires implicit default construction")
            self.global_initializers[node["id"]] = initializers[0]
        elif initializers:
            raise Unsupported("global state initialization requires static zero initialization")
        if node.get("storageClass") == "extern":
            raise Unsupported("external global state declaration")
        self.globals[node["id"]] = (node["name"], ty, size)

    def collect_static_member_definition(self, node):
        declaration = node.get("previousDecl")
        if declaration not in self.static_members:
            raise Unsupported("unrecognized static data definition")
        if node.get("tls") or node.get("storageClass") == "extern":
            raise Unsupported("thread-local or external static data definition")
        ty = self.ty(type_of_decl(node))
        children = inner(node)
        literal = strip(children[0]) if len(children) == 1 else {}
        family_member = declaration == self.static_family_member
        upper = 2**31 if family_member else 2**32
        allowed_type = (ty.kind == "int" and ty.width == 32) if family_member else ty.kind == "u32"
        if (not allowed_type or literal.get("kind") != "IntegerLiteral"
                or not 0 <= int(literal["value"]) < upper):
            raise Unsupported("static data needs an in-range UInt32 literal initializer")
        name = self.static_members[declaration]
        if declaration in self.globals or any(lean_name(n) == lean_name(name) for n, _, _ in self.globals.values()):
            raise Unsupported("ambiguous static data model name")
        self.static_member_definitions[node["id"]] = declaration
        self.static_member_literals[declaration] = literal["value"]
        self.globals[declaration] = (name, ty, None)

    def global_state_type(self):
        if self.static_family is None:
            return self.global_state_name
        return f"({self.global_state_name} {self.static_family[1]} {self.static_tag})"

    def resolve_static_member_references(self):
        if not self.static_members:
            return
        if self.static_members.keys() != self.static_member_literals.keys():
            raise Unsupported("static data declaration needs an out-of-line definition")

        def visit(node):
            ref = node.get("referencedDecl", {})
            canonical = self.static_member_definitions.get(ref.get("id"))
            if canonical is not None:
                ref["id"] = canonical
            member = node.get("referencedMemberDecl")
            if member in self.static_members or member in self.static_member_definitions:
                raise Unsupported("object-qualified static data access may evaluate the receiver")
            for child in inner(node):
                visit(child)

        for declaration in self.decls:
            visit(declaration)

    def collect_local_statics(self):
        """Lift zero and empty-vector local statics from non-template free functions."""
        def visit(node, owner):
            kind = node.get("kind")
            if kind in ("LambdaExpr", "CXXRecordDecl", "FunctionDecl"):
                return
            if kind == "VarDecl" and node.get("storageClass") == "static":
                spelling = type_of_decl(node)
                canonical = node["type"].get("desugaredQualType", spelling)
                if node.get("tls") or re.search(r"\b(?:const|volatile)\b|[&*]", canonical):
                    raise Unsupported("local static must be a mutable nonvolatile value")
                ty = self.ty(spelling)
                children = inner(node)
                initializer = strip(children[0]) if len(children) == 1 else {}
                is_zero = (ty.kind == "u32" and initializer.get("kind") == "IntegerLiteral"
                           and initializer.get("value") == "0")
                vector = re.fullmatch(r"std::vector<(.*)>", canonical)
                is_empty_vector = (ty.kind == "vec" and vector and len(split_args(vector[1])) == 1
                                   and initializer.get("kind") == "CXXConstructExpr" and not inner(initializer)
                                   and initializer.get("ctorType", {}).get("qualType") == "void () noexcept")
                if not (is_zero or is_empty_vector):
                    raise Unsupported("local static needs zero or empty vector initialization")
                name = f"{owner.replace('::', '_')}_{node['name']}"
                if any(lean_name(existing) == lean_name(name) for existing, _, _ in self.globals.values()):
                    raise Unsupported("ambiguous local static model name")
                self.local_statics.add(node["id"])
                self.globals[node["id"]] = (name, ty, None)
            for child in inner(node):
                visit(child, owner)

        for name, signatures in self.functions.items():
            if len(signatures) != 1:
                continue
            sig = signatures[0]
            if sig.tparams or sig.node.get("lean_hidden_friend") or sig.node not in self.decls:
                continue
            result_spelling = type_of_decl(sig.node).split("(")[0]
            if "&" in result_spelling or "*" in result_spelling:
                continue
            for body in inner(sig.node):
                if body.get("kind") == "CompoundStmt":
                    visit(body, name)

    def collect(self):
        for decls, data in self.external:
            for node in decls:
                if node.get("lean_cpp_name"):
                    raise Unsupported("dependency functions in child namespaces")
                kind = node.get("kind")
                if kind == "FunctionDecl" and any(x.get("kind") == "CompoundStmt" for x in inner(node)):
                    name = node["name"]
                    ret = parse_type(node["type"]["qualType"].split("(")[0].strip(), set(), set(self.classes))
                    sig = Sig(name, f"cp.{name}", self.param_list(node, []), ret, node=node)
                    self.functions.setdefault(name, []).append(sig)
                elif kind == "ClassTemplateDecl":
                    # Only the field layout of a dependency class template is used: the types of the members of a
                    # template parameter whose default argument is this class (docs/translation.md).
                    tps = [p["name"] for p in inner(node) if p.get("kind") == "TemplateTypeParmDecl" and p.get("name")]
                    rec = next((c for c in inner(node) if c.get("kind") == "CXXRecordDecl"
                                and c.get("completeDefinition")), None)
                    if rec is None:
                        raise Unsupported(f"templates and classes of a dependency ({node.get('name')})")
                    fields = {c["name"]: type_of_decl(c) for c in inner(rec) if c.get("kind") == "FieldDecl"}
                    self.dep_layouts[node["name"]] = (tps, fields)
                elif kind == "FunctionTemplateDecl" and node.get("name") in ("operator<<", "operator>>"):
                    continue   # stream operators of a dependency are outside the models (docs/translation.md)
                elif kind in ("FunctionTemplateDecl", "CXXRecordDecl"):
                    raise Unsupported(f"templates and classes of a dependency ({node.get('name')})")
        self.inline_template_static_constants()
        for node in self.decls:
            kind = node.get("kind")
            if kind == "ClassTemplateDecl":
                tps, values, constraints = self.template_params(node, allow_constraints=True)
                rec = next((c for c in inner(node) if c.get("kind") == "CXXRecordDecl" and c.get("completeDefinition")), None)
                if rec is not None and not self.collect_record_family(rec, tps, values, constraints):
                    self.collect_class(rec, tps, values, constraints)
            elif kind == "CXXRecordDecl" and node.get("completeDefinition"):
                self.collect_class(node, [])
            elif kind == "FunctionTemplateDecl":
                tps, values, constraints = self.template_params(node, allow_constraints=True, allow_type_constraints=True)
                fn = next((c for c in inner(node) if c.get("kind") == "FunctionDecl"
                           and any(x.get("kind") == "CompoundStmt" for x in inner(c))), None)
                if fn is not None:
                    self.collect_function(fn, tps, values, constraints)
            elif kind == "FunctionDecl":
                if any(x.get("kind") == "CompoundStmt" for x in inner(node)):
                    self.collect_function(node, [])
            elif kind == "VarDecl":
                if node.get("previousDecl") in self.static_members:
                    self.collect_static_member_definition(node)
                elif re.search(r"\bconst\b", type_of_decl(node)):
                    self.collect_constant(node)
                else:
                    self.collect_global(node)
            elif kind == "ClassTemplateSpecializationDecl":
                spelling = " ".join(self.span(node).split())
                if not re.fullmatch(r"(?:extern )?template (?:struct|class) (?:cp::)?\w+<.*>", spelling):
                    raise Unsupported("explicit class template specialization")
            elif kind == "TypeAliasDecl":
                spelling = type_of_decl(node)
                if re.search(r"[&*]|\b(?:const|volatile)\b", spelling):
                    raise Unsupported("namespace type alias must be an unqualified value type")
                self.aliases[node.get("lean_cpp_name", node["name"])] = self.ty(spelling)
            elif kind == "TypeAliasTemplateDecl" and node.get("lean_cpp_name"):
                params, values, constraints = self.template_params(node)
                aliases = [n for n in inner(node) if n.get("kind") == "TypeAliasDecl"]
                family_names = {outer for outer, _ in self.nested_record_names.values()}
                if len(aliases) != 1 or values or constraints:
                    raise Unsupported("qualified alias requires a type-only record family")
                target = type_of_decl(aliases[0]).removeprefix("cp::")
                primary = target.split("<", 1)[0]
                if primary not in family_names or target != primary + "<" + ", ".join(params) + ">":
                    raise Unsupported("qualified alias must forward the record family parameters")
            elif kind in ("TypeAliasTemplateDecl", "FullComment"):
                pass
            else:
                raise Unsupported(f"top-level {kind}")
        for name, sigs in self.functions.items():
            # Operators from different headers share the cp namespace. Stable
            # parameter tags prevent a lone stream operator in each component
            # from defining the same Lean constant.
            if len(sigs) > 1 or name.startswith("operator"):
                tags = set()
                for sig in sigs:
                    tag = "_".join(type_tag(p[1]) for p in sig.params) if sig.params else "0"
                    twins = [other for other in sigs
                             if ("_".join(type_tag(p[1]) for p in other.params) if other.params else "0") == tag]
                    if len(twins) > 1:
                        if len(twins) != 2 or {bool(other.node.get("lean_hidden_friend")) for other in twins} != {False, True}:
                            raise Unsupported(f"overloads of {name} with the same parameter kinds")
                        if twins[0].ret != twins[1].ret or [p[1:] for p in twins[0].params] != [p[1:] for p in twins[1].params]:
                            raise Unsupported(f"different signatures sharing a hidden-friend tag: {name}")
                        tag += "_hidden" if sig.node.get("lean_hidden_friend") else "_qualified"
                    if tag in tags:
                        raise Unsupported(f"overloads of {name} with the same parameter kinds")
                    tags.add(tag)
                    sig.lean_name = f"cp.{lean_name(name)}_{tag}"
        self.resolve_static_member_references()
        self.collect_local_statics()
        if self.globals:
            name = "initializeGlobals"
            if (self.local_statics or self.static_members
                    or all(size is None and ty.kind in ("int", "u32", "u64", "bool")
                           for _, ty, size in self.globals.values())):
                # Scalar state names and local static names identify their storage. A distinct
                # state/initializer lets clients import several such models.
                keys = tuple(name for name, _, _ in self.globals.values())
                suffix = hashlib.sha256(repr(keys).encode()).hexdigest()[:16]
                self.global_state_name += "_" + suffix
                name += "_" + suffix
            occupied = {node.get("name") for node in self.decls}
            while name in occupied:
                name += "_"
            self.initializer_name = name
            node = {"kind": "FunctionDecl", "id": "lean_global_initializer", "name": name,
                    "lean_global_initializer": True, "inner": []}
            family_params = [self.static_family[1]] if self.static_family is not None else []
            if family_params and self.globals.keys() != {self.static_family_member}:
                raise Unsupported("template static state must be separate from other mutable state")
            self.order.append(("fn", Sig(name, "cp." + name, [], VOID, node=node, tparams=family_params,
                                         uses_globals=True, initializes_globals=True, public=False)))

    def constructed_element(self, method, tps):
        """Find stateful construction of a class type parameter in a vector or from a forwarded pack."""
        def vector_of_parameter(node):
            depth = 0
            node = strip(node)
            while node.get("kind") == "ArraySubscriptExpr" and inner(node):
                depth += 1
                node = strip(inner(node)[0])
            try:
                ty = parse_type(type_of_decl(node), set(tps), self.classes, aliases=self.aliases)
            except Unsupported:
                return False
            for _ in range(depth + 1):
                if ty.kind != "vec" or ty.length is not None:
                    return False
                ty = ty.args[0]
            return ty.kind == "tparam" and ty.name in tps

        def constructs(n, dependent_vector=False):
            if not isinstance(n, dict):
                return False
            kind = n.get("kind")
            spelling = n.get("type", {}).get("qualType", "")
            if kind == "VarDecl":
                dependent_vector = vector_of_parameter(n)
            if kind == "PackExpansionExpr" or (kind == "InitListExpr" and
                    (spelling in tps or (spelling == "void" and dependent_vector))):
                return True
            if kind in ("CallExpr", "CXXMemberCallExpr") and len(inner(n)) >= 4:
                callee = strip(inner(n)[0])
                name = callee.get("name") or callee.get("member")
                if not name and callee.get("kind") == "UnresolvedMemberExpr":
                    name = self.member_token(callee)
                if name == "emplace_back" and inner(callee) and vector_of_parameter(inner(callee)[0]):
                    return True
            return any(constructs(c, dependent_vector) for c in inner(n))
        if not constructs(method):
            return None
        candidates = [t for t in tps if self.tparam_defaults.get(t)
                      and re.match(r"(?:cp::)?(\w+)", self.tparam_defaults[t].strip()).group(1) in self.dep_layouts]
        if len(candidates) != 1:
            return None   # no constructor state; a construction of a type parameter is then rejected
        return candidates[0]

    def param_list(self, node, tps, containers=(), values=None):
        params = []
        for p in inner(node):
            if p.get("kind") == "ParmVarDecl":
                qual = container_text(type_of_decl(p), containers)
                pack = re.fullmatch(r"\s*(\w+)\s*\.\.\.\s*", qual)
                if pack and pack.group(1) in self.packs and pack.group(1) in tps:
                    params.append((p.get("name") or f"arg{len(params)}", Ty("tparam", pack.group(1)), False))
                    continue
                is_ref = "&" in qual and not re.search(r"\bconst\b", qual)
                params.append((p.get("name") or f"arg{len(params)}", parse_type(qual, set(tps) - (values or {}).keys(), self.classes, values, self.aliases), is_ref))
        return params

    def collect_function(self, node, tps, values=None, constraints=None):
        values = values or {}
        name = node.get("lean_cpp_name", node["name"])
        if name != node["name"]:
            if name in self.functions:
                raise Unsupported(f"overloaded child namespace function {name}")
            self.qualified_functions[node["id"]] = name
        model_name = scoped_lean_name(name)
        # A template parameter used as `T::value_type` is a random-access container (modelled by std::vector)
        text = json.dumps(node)
        containers = [t for t in tps if f"{t}::value_type" in text]
        tps = [f"{t}_value_type" if t in containers else t for t in tps]
        ret_text = container_text(return_type_text(node["type"]["qualType"]), containers)
        ret = parse_type(ret_text, set(tps) - values.keys(), self.classes, values, self.aliases)
        sig = Sig(name, f"cp.{model_name}", self.param_list(node, tps, containers, values), ret, node=node, tparams=tps, value_params=values, constraints=constraints or [])
        sig.containers = containers
        self.functions.setdefault(name, []).append(sig)
        self.order.append(("fn", sig))

    def collect_record_family(self, rec, tps, values, constraints):
        members = [n for n in inner(rec) if n.get("kind") == "CXXRecordDecl" and n.get("completeDefinition")]
        if not members:
            return False
        if (rec.get("tagUsed") != "struct" or rec.get("bases") or values or constraints or not tps
                or any(n not in members and not n.get("isImplicit") and n.get("kind") != "FullComment"
                       for n in inner(rec))):
            raise Unsupported("nested records require a public type-only template family")
        qualifiers = {n["name"]: rec["name"] + "_" + n["name"] for n in members}
        if len(qualifiers) != len(members) or set(tps) & qualifiers.keys():
            raise Unsupported("ambiguous nested record names")
        global_names = {n.get("name") for n in self.decls}
        if set(qualifiers.values()) & (global_names | self.classes.keys()):
            raise Unsupported("nested record model name conflicts with a class")
        unqualified = {"TypeAliasDecl", "TypedefDecl", "TemplateTypeParmDecl", "EnumDecl"}
        def reject_shadowing(node):
            if node.get("kind") in unqualified and node.get("name") in qualifiers:
                raise Unsupported("shadowing a nested record type")
            for child in inner(node):
                reject_shadowing(child)
        for member in members:
            reject_shadowing(member)
        spelling = re.compile(r"(?<![A-Za-z0-9_:])(" + "|".join(map(re.escape, qualifiers)) + r")\b")
        args = "<" + ", ".join(tps) + ">"
        def map_types(value):
            if isinstance(value, list):
                return [map_types(x) for x in value]
            if not isinstance(value, dict):
                return value
            return {k: spelling.sub(lambda m: qualifiers[m[0]] + args, v)
                    if k in ("qualType", "desugaredQualType") and isinstance(v, str)
                    else map_types(v) for k, v in value.items()}
        for member in members:
            cpp_name = member["name"]
            record = map_types(member)
            record["name"] = qualifiers[cpp_name]
            self.collect_class(record, tps)
            self.nested_record_names[record["name"]] = (rec["name"], cpp_name)
        return True

    def collect_class(self, rec, tps, values=None, constraints=None):
        values = values or {}
        name = rec["name"]
        if rec.get("bases"):
            raise Unsupported("class inheritance")
        info = ClassInfo(name, tps, [], [], value_params=values, constraints=constraints or [],
                         model_only=rec.get("lean_model_only", False))
        self.classes[name] = info
        tset = set(tps) - values.keys()
        access = "public" if rec.get("tagUsed") == "struct" else "private"
        for c in inner(rec):
            kind = c.get("kind")
            member_tps, member_values, member_constraints = [], {}, []
            if kind == "FunctionTemplateDecl":
                member_tps, member_values, member_constraints = self.template_params(c, allow_constraints=True, allow_type_constraints=True)
                if set(member_tps) & set(tps):
                    raise Unsupported("member template parameter shadows a class parameter")
                declarations = [x for x in inner(c)
                                if x.get("kind") in ("CXXMethodDecl", "CXXConstructorDecl")
                                and any(y.get("kind") == "CompoundStmt" for y in inner(x))]
                if not declarations:
                    raise Unsupported("member template without a body")
                # Clang also lists concrete instantiations here. Emit the generic
                # declaration once; the same definition covers those instances.
                c = declarations[0]
                kind = c["kind"]
            if kind == "AccessSpecDecl":
                access = c.get("access", access)
            if kind == "VarDecl" and c.get("storageClass") == "static" and c.get("constexpr") and not tps:
                # A static constexpr literal member is a constant of the model (docs/translation.md).
                c["lean_cpp_name"] = f"{name}_{c['name']}"
                self.collect_constant(c)
                continue
            if kind == "VarDecl":
                spelling = type_of_decl(c)
                if (c.get("storageClass") != "static" or c.get("tls") or inner(c)
                        or re.search(r"\b(?:const|volatile)\b|[&*]", spelling)):
                    raise Unsupported("static member needs a mutable out-of-line definition")
                if tps:
                    # One signed int counter per specialization of a one-parameter class template
                    # (e.g. Edge<T>::next_id): the state is indexed by T and the C++ specialization tag.
                    if len(tps) != 1 or values or constraints or spelling != "int" or self.static_family is not None:
                        raise Unsupported("templated static state requires one class type and one signed int member")
                    self.static_family = (name, tps[0])
                    self.static_family_member = c["id"]
                elif self.ty(spelling).kind != "u32":
                    raise Unsupported("static member needs a mutable UInt32 out-of-line definition")
                self.static_members[c["id"]] = name + "_" + c["name"]
                continue
            if kind == "FieldDecl":
                init = inner(c)[0] if inner(c) else None
                fty = parse_type(type_of_decl(c), tset, self.classes, values, self.aliases)
                if fty.kind in ("istream", "ostream"):
                    raise Unsupported("stream state stored in a class field")
                info.fields.append((c["name"], fty, init))
                if access == "public":
                    info.public_fields.add(c["name"])
            elif kind in ("CXXMethodDecl", "CXXConstructorDecl"):
                if c.get("isImplicit"):
                    continue
                if not any(x.get("kind") == "CompoundStmt" for x in inner(c)):
                    if c.get("explicitlyDeleted"):
                        if kind == "CXXConstructorDecl":
                            raise Unsupported("deleted constructor")
                        continue
                    if not (c.get("explicitlyDefaulted") and c["name"] in ("operator==", "operator<=>")):
                        raise Unsupported(f"member without a body: {c['name']}")
                is_ctor = kind == "CXXConstructorDecl"
                qual = c["type"]["qualType"]
                all_values = {**values, **member_values}
                all_tps = list(tps) + member_tps
                return_text = return_type_text(qual)
                if is_ctor:
                    ret = VOID
                elif c.get("explicitlyDefaulted") and c["name"] == "operator<=>" and return_text == "auto":
                    # The model accepts scalar fields whose instance supplies a strong order.
                    ret = ORDERING
                else:
                    ret = parse_type(return_text, set(all_tps) - all_values.keys(), self.classes, all_values, self.aliases)
                sig = Sig(c["name"].split("<")[0] if is_ctor else c["name"], "", self.param_list(c, all_tps, values=all_values), ret, owner=name,
                          is_const=qual.rstrip().endswith("const") or is_ctor
                          or bool(re.search(r"\(&\s*\(.*\)\s*const\s*\)\s*\[", qual)), is_static=c.get("storageClass") == "static",
                          is_ctor=is_ctor, node=c, tparams=member_tps, value_params=member_values,
                          constraints=member_constraints, public=access == "public")
                if (is_ctor and len(sig.params) == 1 and sig.params[0][1].kind == "cls"
                        and sig.params[0][1].name == name
                        and not any(ty.kind == "deque" for _, ty, _ in info.fields)):
                    raise Unsupported("user-defined record copy constructor")
                element = self.constructed_element(c, tps)
                if element is not None:
                    # The method constructs values of a class type parameter `E` (emplace_back with a forwarded
                    # pack): the state of E's constructors (e.g. Edge's id counter) is passed in and returned.
                    sig.params.append((CONSTRUCT_STATE, Ty("cstate", args=(Ty("tparam", element),)), True))
                info.methods.append(sig)
            elif kind == "CXXDestructorDecl" and c.get("isImplicit"):
                continue
            elif kind == "FullComment":
                continue
            elif kind in ("CXXRecordDecl", "AccessSpecDecl", "TypeAliasDecl", "TypedefDecl"):
                if kind == "CXXRecordDecl" and c.get("completeDefinition"):
                    raise Unsupported("nested class")
            elif kind == "FriendDecl":
                # a friend function defined in the class is a free function (it may read the private fields)
                fn = next((x for x in inner(c) if x.get("kind") == "FunctionDecl"), None)
                if fn is None:
                    raise Unsupported("friend other than a function")
                if any(x.get("kind") == "CompoundStmt" for x in inner(fn)):
                    fn["lean_hidden_friend"] = True
                    self.collect_function(fn, list(tps), values)
            else:
                raise Unsupported(f"class member {kind}")
        # names
        groups = {}
        for s in info.methods:
            groups.setdefault("init" if s.is_ctor else s.cpp_name, []).append(s)
        for base, sigs in groups.items():
            for s in sigs:
                suffix = ""
                if len(sigs) > 1:
                    suffix = "_" + "_".join(type_tag(p[1]) for p in s.params) if s.params else "_0"
                    # const and non-const overloads with the same parameters (e.g. operator[]).
                    same = [o for o in sigs if [p[1] for p in o.params] == [p[1] for p in s.params]]
                    if len(same) == 2 and len({o.is_const for o in same}) == 2 and s.is_const:
                        suffix += "_const"
                if (s.is_ctor and not s.params and all(o is s or
                        (len(o.params) == 1 and o.params[0][1].kind == "cls" and o.params[0][1].name == name)
                        for o in sigs)):
                    suffix = ""
                if (s.is_ctor and len(s.params) == 1 and s.params[0][1].kind == "cls"
                        and s.params[0][1].name == name):
                    declaration = next(p for p in inner(s.node) if p.get("kind") == "ParmVarDecl")
                    spelling = type_of_decl(declaration)
                    if "&&" in spelling and not re.search(r"\bconst\b", spelling):
                        suffix = "_move"
                    elif "&&" not in spelling and re.search(r"\bconst\b", spelling):
                        suffix = "_copy"
                    else:
                        raise Unsupported("unsupported copy/move constructor qualification")
                s.lean_name = f"cp.{name}.{lean_name(base)}{suffix}"
        self.order.append(("class", info))

    # --------------------------------------------------------------- emission
    @staticmethod
    def body_key(node):
        body = next((c for c in inner(node) if c.get("kind") == "CompoundStmt"), None)
        if body is None:
            return None
        def offset(location):
            return location.get("spellingLoc", location).get("offset")
        bounds = body.get("range", {})
        begin, end = offset(bounds.get("begin", {})), offset(bounds.get("end", {}))
        return (node.get("name"), begin, end) if begin is not None and end is not None else None

    def resolve_function(self, declaration_id):
        matches = self.function_declarations.get(declaration_id, [])
        if len(matches) != 1:
            raise Unsupported("cannot identify the resolved operator definition")
        return matches[0]

    def constructor_name(self, node):
        if node.get("kind") not in ("CXXConstructExpr", "CXXTemporaryObjectExpr", "CXXUnresolvedConstructExpr"):
            return None
        spelling = type_of_decl(node)
        match = re.fullmatch(r"(?:cp::)?(\w+)(?:<.*>)?", spelling)
        if not match or match[1] not in self.classes:
            return None
        # An implicit copy/move of a supported scalar record is a value
        # transfer. Conversion constructors can read/update the state.
        signature = node.get("ctorType", {}).get("qualType", "")
        if (len(inner(node)) == 1 and re.fullmatch(
                rf"void \((?:const )?(?:cp::)?{re.escape(match[1])} &&?\)(?: noexcept)?", signature)):
            return None
        return match[1]

    def translate(self) -> str:
        self.collect()
        sigs = []
        for kind, item in self.order:
            if kind == "class":
                sigs += [(sig, item) for sig in item.methods]
            else:
                sigs.append((item, None))
        if self.globals:
            if self.static_members and set(self.globals) - self.static_members.keys() - self.local_statics:
                raise Unsupported("class static data cannot share state with namespace globals")

            def dependencies(node):
                direct, calls = False, set()
                def walk(n):
                    nonlocal direct
                    reference = n.get("referencedDecl", {})
                    if reference.get("id") in self.globals:
                        direct = True
                    if self.static_members:
                        constructor = self.constructor_name(n)
                        if constructor is not None:
                            calls.add(constructor)
                    if reference.get("kind") in ("FunctionDecl", "CXXMethodDecl"):
                        calls.add(self.qualified_functions.get(reference.get("id"), reference.get("name")))
                    if n.get("kind") in ("UnresolvedLookupExpr", "MemberExpr", "CXXDependentScopeMemberExpr"):
                        calls.add(n.get("name") or n.get("member"))
                    if self.static_members and n.get("kind") == "UnresolvedMemberExpr":
                        calls.add(n.get("name") or self.member_token(n))
                    for child in inner(n):
                        walk(child)
                walk(node)
                return direct, calls
            graph = {id(sig): dependencies(sig.node) for sig, _ in sigs}
            changed = True
            while changed:
                changed = False
                affected = {sig.cpp_name for sig, _ in sigs if sig.uses_globals}
                for sig, info in sigs:
                    direct, calls = graph[id(sig)]
                    if not sig.uses_globals and (direct or calls & affected):
                        if self.static_family is not None and (info is None or info.name != self.static_family[0]):
                            raise Unsupported("template static state cannot cross class specialization")
                        params = [p for p in inner(sig.node) if p.get("kind") == "ParmVarDecl"]
                        if not self.static_members:
                            if any("&" in type_of_decl(p) for p in params):
                                raise Unsupported("global state in reference-parameter functions")
                            if info and any(typ.kind not in ("int", "u32", "u64", "bool") or size is not None
                                            for _, typ, size in self.globals.values()):
                                raise Unsupported("a method may use only independent scalar global state")
                        else:
                            # Addressable scalar statics could alias scalar
                            # reference inputs. Class records and streams
                            # are distinct objects. Local caches only escape
                            # by value in the supported subset.
                            for param, (_, ty, _) in zip(params, sig.params, strict=True):
                                if "&" in type_of_decl(param) and ty.kind not in ("cls", "istream", "ostream"):
                                    raise Unsupported("reference parameter may alias class static data")
                        sig.uses_globals = True
                        changed = True
            self.global_functions = {sig.cpp_name for sig, _ in sigs if sig.uses_globals}
            self.global_constructors = {sig.owner for sig, _ in sigs if sig.uses_globals and sig.is_ctor}
            self.global_methods = {sig.cpp_name for sig, _ in sigs if sig.uses_globals and sig.owner and not sig.is_ctor}
        by_body = {}
        self.function_declarations = {}
        self.raw_declarations = {}
        for sig, _ in sigs:
            key = self.body_key(sig.node)
            if key is not None:
                by_body.setdefault(key, []).append(sig)
            self.function_declarations[sig.node["id"]] = [sig]
        def index_declarations(node):
            if "id" in node:
                self.raw_declarations[node["id"]] = node
            if node.get("kind") in ("FunctionDecl", "CXXMethodDecl"):
                key = self.body_key(node)
                if key in by_body:
                    self.function_declarations[node["id"]] = by_body[key]
            for child in inner(node):
                index_declarations(child)
        for node in self.decls:
            index_declarations(node)
        self.check_recursive_receivers(sigs)
        built = {}
        for sig, info in sigs:
            built[id(sig)] = self.build_function(sig, info)
        # instance requirements of the callees (same type parameter names)
        changed = True
        while changed:
            changed = False
            for sig, info in sigs:
                fn = built[id(sig)]
                for callee in fn.callees:
                    cfn = built.get(id(callee))
                    if cfn is None:
                        continue
                    own = set(info.tparams if info else []) | set(sig.tparams)
                    for bindings, discharged in fn.member_call_bindings.get(id(callee), [({}, set())]):
                        for requirement in cfn.reqs.items:
                            if requirement in discharged:
                                continue
                            # Preserve quoted NumericTraits tags while substituting
                            # the carrier types at this particular call site.
                            r = re.sub(r'"[^"\\]*(?:\\.[^"\\]*)*"|\b[A-Za-z_][A-Za-z_0-9]*\b',
                                       lambda m: lean_type(bindings[m[0]]) if m[0] in bindings and m[0] != "__free__" else m[0],
                                       requirement) if bindings else requirement
                            type_text = " ".join(r.split()[1:])
                            if bindings or r.startswith(("Cpp.SourceStream", "Cpp.ModToUInt32", "Cpp.StaticCall",
                                                         "Cpp.AdlCall2", "Cpp.Method1", "Cpp.Field", "Cpp.WriteField")):
                                type_text = re.sub(r'"[^"\\]*(?:\\.[^"\\]*)*"', '', type_text)
                            if r == "Cpp.StreamWrite Cpp.StreamChar":
                                type_text = ""
                            if r.startswith("Cpp.Conv (Cpp.ConditionalResult.Value "):
                                type_text = re.sub(r"Cpp\.ConditionalResult\.Value|\((?:Left|Right) :=", "", type_text)
                            type_names = set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", type_text))
                            if not type_names <= own | {"Int", "UInt32", "UInt64", "Bool", "Unit", "Ordering", "Array"}:
                                raise Unsupported(f"requirement {r} of {callee.cpp_name} over another type parameter")
                            if bindings.get("__free__") and not type_names & own \
                                    and requirement.split()[0] in ("Inhabited", "Zero", "IntCast", "LT", "LE",
                                                                   "DecidableLT", "DecidableLE", "DecidableEq",
                                                                   "Cpp.Conv"):
                                # Instantiated at concrete types only: Lean finds the instance at the call.
                                continue
                            if r not in fn.reqs.items:
                                fn.reqs.add(r)
                                changed = True
        # definitions after their callees
        order, state = [], {}
        index = {id(sig): (sig, info) for sig, info in sigs}
        def visit(key):
            if state.get(key) == "done":
                return
            if state.get(key) == "active":
                raise Unsupported(f"recursion through {index[key][0].cpp_name}")
            state[key] = "active"
            for callee in built[key].callees:
                if id(callee) == key:
                    # Direct self-recursion: translated with a decreasing fuel argument (docs/translation.md).
                    index[key][0].self_recursive = True
                    continue
                if id(callee) in index:
                    visit(id(callee))
            state[key] = "done"
            order.append(key)
        for sig, info in sigs:
            visit(id(sig))
        out = [f"def cp.{scoped_lean_name(name)} : {lean_type(ty)} := {literal}\n"
               for name, ty, literal in self.constants.values()]
        for kind, item in self.order:
            if kind == "class":
                out.append(self.emit_structure(item))
        for name, ty in self.aliases.items():
            requirements = class_requirements(ty, self.classes)
            head = " ".join(f"[{r}]" for r in requirements)
            model_name = scoped_lean_name(name)
            out.append(f"abbrev cp.{model_name} {head} := {lean_type(ty)}\n")
        if self.globals:
            if any(node.get("name") == self.global_state_name.removeprefix("cp.") for node in self.decls):
                raise Unsupported("global state model name conflicts with a source declaration")
            requirements = sorted({r for _, ty, _ in self.globals.values()
                                   for r in class_requirements(ty, self.classes)})
            state_param = f"({self.static_family[1]} : Type) ({self.static_tag} : String) " if self.static_family else ""
            lines = [f"structure {self.global_state_name} {state_param}" + " ".join(f"[{r}]" for r in requirements) + " where"]
            for name, ty, _ in self.globals.values():
                lines.append(f"  {lean_name(name)} : {lean_type(ty)}")
            lines.append("  deriving Inhabited")
            out.append("\n".join(lines) + "\n")
        for key in order:
            sig, info = index[key]
            out.append(self.emit_header(sig, info, built[key]))
        self.built_functions = built
        return "\n".join(out)

    def emit_structure(self, info: ClassInfo) -> str:
        head = " ".join(f"({lean_name(t)} : {lean_type(info.value_params[t])})" if t in info.value_params else f"({t} : Type)" for t in info.tparams)
        head += "".join(f" [Cpp.TemplateConstraint {c}]" for c in info.constraints)
        lines = [re.sub(r"  +", " ", f"structure cp.{info.name} {head} where")]
        for fname, fty, _ in info.fields:
            lines.append(f"  {lean_name(fname)} : {lean_type(fty)}")
        lines.append("  deriving Inhabited")
        return "\n".join(lines) + "\n"

    def check_recursive_receivers(self, sigs):
        """Allow private recursion to read its receiver while keeping mutable C++ overload resolution.

        Existing translations keep their ABI. Retry only when the conservative receiver writeback
        prevents a range loop. The retry rejects every field assignment or mutating call on this.
        """
        for sig, info in sigs:
            if info is None or sig.public or sig.is_const or sig.is_static or sig.is_ctor:
                continue
            if sum(m.cpp_name == sig.cpp_name for m in info.methods) != 1:
                continue
            try:
                self.build_function(sig, info)
            except RangeMutation:
                sig.preserves_receiver = True
                try:
                    fn = self.build_function(sig, info)
                    sig.preserves_receiver = any(callee is sig for callee in fn.callees)
                except Unsupported:
                    sig.preserves_receiver = False
            except Unsupported:
                pass  # The main build reports unsupported source in the original build order.

    def build_function(self, sig: Sig, info: ClassInfo | None) -> Fn:
        fn = Fn(self, sig, info)
        for condition in sig.constraints:
            for parameter in re.findall(r'Cpp\.TypeTraits\.\w+ \(tag := "(\w+)"\)', condition):
                fn.reqs.add(f'Cpp.TypeTraits "{parameter}" {parameter}')
            fn.reqs.add("Cpp.TemplateConstraint " + condition)
        for ty in [sig.ret, *([class_ty(info)] if info else [])]:
            for requirement in class_requirements(ty, self.classes):
                fn.reqs.add(requirement)
        if any(ty.kind in ("istream", "ostream") for ty in [sig.ret, *[p[1] for p in sig.params]]):
            fn.reqs.add("Cpp.Streams")
        if sig.uses_globals:
            for _, ty, _ in self.globals.values():
                for requirement in class_requirements(ty, self.classes):
                    fn.reqs.add(requirement)
        node = sig.node
        if sig.initializes_globals:
            fn.emit("Cpp.tick")
            for key, (_, ty, size) in self.globals.items():
                element = ty.args[0] if size is not None else ty
                name = fn.global_names[key]
                if element.kind == "cls":
                    pre = []
                    value = fn.construct(element, self.global_initializers[key], pre)
                    if size is not None:
                        fn.emit(f"let mut {name} : {lean_type(ty)} := Array.empty")
                        fn.emit(f"for _ in [:({size} : Nat)] do")
                        fn.indent += 1
                        fn.emit("Cpp.tick")
                        fn.flush(pre)
                        fn.emit(f"{name} := {name}.push {value}")
                        fn.indent -= 1
                    else:
                        fn.flush(pre)
                        fn.emit(f"let {name} := {value}")
                else:
                    if key in self.static_member_literals:
                        value = self.static_member_literals[key]
                    elif key in self.local_statics and ty.kind == "vec":
                        value = "Array.empty"
                    else:
                        value = "false" if element.kind == "bool" else "0"
                    if size is not None:
                        fn.emit(f"Cpp.tickN {size}")
                        value = f"Array.replicate {size} ({value} : {lean_type(element)})"
                    fn.emit(f"let {name} : {lean_type(ty)} := {value}")
            fn.emit("return " + fn.global_value())
            return fn
        params = []
        for name, ty in {**(info.value_params if info else {}), **sig.value_params}.items():
            fn.declare(name, ty)
        for pname, pty, is_ref in sig.params:
            fn.declare(pname, pty)
        cls_ty = None
        if info is not None:
            cls_ty = lean_type(class_ty(info))
            names = {p[0] for p in sig.params} | local_names(node)
            for fname, fty, _ in info.fields:
                fn.field_names[fname] = ("this_" + fname) if fname in names else lean_name(fname)
                fn.used_names.add(fn.field_names[fname])
        if node.get("explicitlyDefaulted"):
            if info is None or sig.cpp_name not in ("operator==", "operator<=>") or not sig.is_const or len(sig.params) != 1:
                raise Unsupported("defaulted member other than const comparison")
            pname, pty, is_ref = sig.params[0]
            expected = class_ty(info)
            equality = sig.cpp_name == "operator=="
            if pty != expected or is_ref or sig.ret != (BOOL if equality else ORDERING):
                raise Unsupported("defaulted comparison signature")
            comparisons = []
            for fname, fty, _ in info.fields:
                if fty.kind not in ("int", "u32", "u64", "bool", "tparam"):
                    raise Unsupported("defaulted comparison of a non-scalar field")
                lhs, rhs = f"self.{lean_name(fname)}", f"{fn.var_name(pname)}.{lean_name(fname)}"
                if equality:
                    fn.need("DecidableEq", fty)
                    comparisons.append(f"({lhs} = {rhs})")
                elif fty.kind == "bool":
                    comparisons.append((f"!{lhs} && {rhs}", f"{lhs} && !{rhs}"))
                else:
                    fn.need("LT", fty)
                    fn.need("DecidableLT", fty)
                    comparisons.append((f"{lhs} < {rhs}", f"{rhs} < {lhs}"))
            fn.emit("Cpp.tick")
            if equality:
                fn.emit("return decide (" + (" ∧ ".join(comparisons) if comparisons else "True") + ")")
            else:
                outcome = "Ordering.eq"
                for lt, gt in reversed(comparisons):
                    outcome = f"if {lt} then Ordering.lt else if {gt} then Ordering.gt else {outcome}"
                fn.emit("return " + outcome)
            return fn
        body = next(x for x in inner(node) if x.get("kind") == "CompoundStmt")
        assigned = fn.assigned_names(body)
        fn.emit("Cpp.tick")
        if sig.uses_globals:
            for key, (name, _, size) in self.globals.items():
                if size is not None:
                    fn.emit(f"Cpp.check (decide ({fn.global_input}.{lean_name(name)}.size = {size}))")
                fn.emit(f"let mut {fn.global_names[key]} := {fn.global_input}.{lean_name(name)}")
        if info is not None and not sig.is_static:
            if sig.is_ctor:
                fn.scopes[0]["__fields__"] = INT
                inits = {}
                delegated = None
                for c in inner(node):
                    if c.get("kind") == "CXXCtorInitializer":
                        member = c.get("anyInit", {}).get("name")
                        if member is None:
                            if len([x for x in inner(node) if x.get("kind") == "CXXCtorInitializer"]) != 1:
                                raise Unsupported("mixed delegating initializers")
                            expected_ty = class_ty(info)
                            target = c.get("delegatingInit", c.get("baseInit", {})).get("qualType", "")
                            if self.ty(target, fn) != expected_ty:
                                raise Unsupported("base initializer")
                            delegate = strip(inner(c)[0])
                            factory_form = (not sig.params and not inner(body) and len(inner(delegate)) == 1
                                            and strip(inner(delegate)[0]).get("kind") == "CallExpr"
                                            and len(inner(strip(inner(delegate)[0]))) == 1)
                            if not factory_form:
                                # A delegating constructor `C(a) : C(b...) { body }`: the target constructor
                                # chosen by overload resolution builds the fields, then the body runs on them.
                                pre = []
                                value = fn.construct(expected_ty, delegate, pre)
                                fn.flush(pre)
                                delegated = value
                                continue
                            # Only the original Group default-constructor form:
                            # an implicit scalar-record copy of one static factory.
                            if sig.params or inner(body):
                                raise Unsupported("delegation requires an empty default constructor")
                            if len([x for x in inner(node) if x.get("kind") == "CXXCtorInitializer"]) != 1:
                                raise Unsupported("mixed delegating initializers")
                            expected_ty = class_ty(info)
                            target = c.get("delegatingInit", c.get("baseInit", {})).get("qualType", "")
                            if self.ty(target, fn) != expected_ty:
                                raise Unsupported("base initializer")
                            args = inner(inner(c)[0])
                            if len(args) != 1:
                                raise Unsupported("delegation other than one record value")
                            factory = strip(args[0])
                            if factory.get("kind") != "CallExpr" or len(inner(factory)) != 1:
                                raise Unsupported("delegation requires a zero-argument static factory")
                            callee = strip(inner(factory)[0])
                            ref = callee.get("referencedDecl", {})
                            if not any(s.is_static and s.node.get("id") == ref.get("id")
                                       and not s.params for s in info.methods):
                                raise Unsupported("delegation factory outside the current class")
                            if any(fty.kind not in ("int", "u32", "u64", "bool", "tparam") for _, fty, _ in info.fields):
                                raise Unsupported("delegating record copy with non-scalar fields")
                            pre = []
                            value, _ = fn.expr(args[0], pre, expected_ty)
                            fn.flush(pre)
                            delegated = value
                            continue
                        inits[member] = inner(c)[0]
                for fname, fty, default_init in info.fields:
                    if delegated is not None:
                        fn.emit(f"let mut {fn.field_names[fname]} : {lean_type(fty)} := {delegated}.{lean_name(fname)}")
                        continue
                    pre = []
                    init = inits.get(fname, default_init)
                    if init is None:
                        value = fn.default_value(fty)
                    else:
                        s = strip(init)
                        if s.get("kind") in ("CXXConstructExpr", "ParenListExpr", "InitListExpr",
                                             "CXXScalarValueInitExpr", "CXXUnresolvedConstructExpr"):
                            value = fn.construct(fty, s, pre)
                        else:
                            value, _ = fn.expr(init, pre, fty)
                    fn.flush(pre)
                    fn.emit(f"let mut {fn.field_names[fname]} : {lean_type(fty)} := {value}")
            else:
                for fname, fty, _ in info.fields:
                    mut = "mut " if not sig.is_const and not sig.preserves_receiver else ""
                    fn.emit(f"let {mut}{fn.field_names[fname]} := self.{lean_name(fname)}")
            for fname, fty, _ in info.fields:
                fn.scopes[0][fname] = fty
            fn.scopes.append({})
        for pname, pty, is_ref in sig.params:
            if (pname in assigned or pname + "[]" in assigned or pname == CONSTRUCT_STATE
                    or pname == node.get("lean_stdout_parameter")):
                fn.emit(f"let mut {lean_name(pname)} := {lean_name(pname)}")
        fn.scopes.append({})
        for s in inner(body):
            fn.stmt(s)
        if sig.is_ctor:
            value = fn.self_value()
            fn.emit("return " + (fn.result(value) if sig.outputs() else value))
        elif sig.ret.kind == "void":
            fn.emit("return " + fn.result(None))
        elif not always_returns(body):
            fn.emit("failure")
        return fn

    def emit_header(self, sig: Sig, info: ClassInfo | None, fn: Fn) -> str:
        cls_ty = None
        if info is not None:
            cls_ty = lean_type(class_ty(info))
        # header
        tps = list(info.tparams if info else []) + list(sig.tparams)
        reqs = list(fn.reqs.items)
        structs = []
        pol_args = []
        for pol, methods in sig.policies.items():
            # a policy parameter is a value: a structure with the static members used
            tps.remove(pol)
            used = []
            for tys, rty in methods.values():
                for t in [*tys, rty]:
                    used += [x for x in sorted(tparams_of(t)) if x not in used]
            used = [t for t in tps if t in used]
            sname = f"{sig.lean_name}.Policy_{pol}"
            lines = [f"/-- The static members of `{pol}` that `{sig.cpp_name}` calls. -/",
                     f"structure {sname} {' '.join(f'({t} : Type)' for t in used)} where"]
            for member, (tys, rty) in methods.items():
                arrow = "".join(f"{lean_type(t)} → " for t in tys)
                lines.append(f"  {lean_name(member)} : {arrow}Cpp.M {lean_type(rty)}")
            structs.append("\n".join(lines) + "\n")
            pol_args.append(f"({pol} : {sname}{''.join(' ' + t for t in used)})")
        for pname, pty, _ in sig.params:
            for t in tparams_of(pty):
                if t not in tps:
                    raise Unsupported(f"unknown type parameter {t}")
        args = list(pol_args)
        if info is not None and not sig.is_static and not sig.is_ctor:
            args.append(f"(self : {cls_ty})")
        for pname, pty, _ in sig.params:
            args.append(f"({lean_name(pname)} : {lean_type(pty)})")
        if sig.uses_globals and not sig.initializes_globals:
            args.append(f"({fn.global_input} : {self.global_state_type()})")
        outs = []
        for o in sig.outputs():
            if o == "ret":
                outs.append(cls_ty if sig.is_ctor else lean_type(sig.ret))
            elif o == "self":
                outs.append(cls_ty)
            elif o == "@globals":
                outs.append(self.global_state_type())
            else:
                outs.append(lean_type(next(p[1] for p in sig.params if p[0] == o)))
        if sig.is_ctor and not sig.outputs():
            rtype = cls_ty
        elif not outs:
            rtype = "Unit"
        else:
            rtype = " × ".join(outs) if len(outs) > 1 else outs[0]
            if len(outs) > 1:
                rtype = f"({rtype})"
        name = sig.lean_name
        bind = binders(tps, reqs, {**(info.value_params if info else {}), **sig.value_params})
        if getattr(sig, "self_recursive", False):
            # `name_rec fuel args` runs the body with the recursive calls on `fuel - 1`; it fails at fuel 0. The
            # function itself starts with `Cpp.fuel`, the bound of every loop (docs/translation.md).
            call = re.compile(rf"(?<![\w.]){re.escape(name)}(?![\w.])")
            lines = [call.sub(f"{name}_rec __fuel", line) for line in fn.lines]
            rec = re.sub(r"  +", " ", f"def {name}_rec {bind} (__fuel : Nat) {' '.join(args)} : Cpp.M {rtype} :=")
            names = [a[1:].split(" : ")[0] for a in args]
            body = [rec, "  match __fuel with", "  | 0 => failure", "  | __fuel + 1 => do",
                    *("    " + line for line in lines)]
            wrapper = re.sub(r"  +", " ", f"def {name} {bind} {' '.join(args)} : Cpp.M {rtype} :=")
            return ("".join(x + "\n" for x in structs) + "\n".join(body) + "\n\n" + wrapper + "\n  "
                    + f"{name}_rec Cpp.fuel {' '.join(names)}" + "\n")
        header = f"def {name} {bind} {' '.join(args)} : Cpp.M {rtype} := do"
        header = re.sub(r"  +", " ", header)
        return "".join(x + "\n" for x in structs) + "\n".join([header] + fn.lines) + "\n"


def type_tag(ty: Ty):
    if ty.kind == "vec":
        return "vec"
    if ty.kind == "tparam":
        return ty.name
    if ty.kind == "cls":
        return ty.name
    return ty.kind


def local_names(node, out=None):
    if out is None:
        out = set()
    if isinstance(node, dict):
        if node.get("kind") == "VarDecl":
            out.add(node["name"])
        for c in node.get("inner", []):
            local_names(c, out)
    return out


# ------------------------------------------------------------------------------------------ driver

def source_decls(source: Path, standard=clang_ast.DEFAULT_STANDARD):
    """Declarations written in `source` directly in cp or a supported child namespace.

    Clang's JSON prints a location's file only when it differs from the previously printed location, so the
    file of a node is tracked by walking the whole dump in order."""
    command = clang_ast.clang_command(standard) + ["-Xclang", "-ast-dump=json", str(source)]
    ast = json.loads(subprocess.check_output(command, text=True, cwd=ROOT, stderr=subprocess.DEVNULL))
    resolved = source.resolve()
    state = {"file": None}
    decls = []

    def visit_loc(loc):
        if not isinstance(loc, dict):
            return
        for key in ("spellingLoc", "expansionLoc"):
            if key in loc:
                visit_loc(loc[key])
        if "file" in loc:
            state["file"] = loc["file"]

    def walk(node, namespace=None, namespace_depth=0):
        if not isinstance(node, dict):
            return
        visit_loc(node.get("loc"))
        here = state["file"]
        rng = node.get("range", {})
        visit_loc(rng.get("begin"))
        visit_loc(rng.get("end"))
        kind, name = node.get("kind"), node.get("name")
        child_namespace = None
        if kind == "NamespaceDecl":
            if namespace_depth == 0 and name == "cp":
                child_namespace = ()
            elif namespace == () and name and not node.get("isInline"):
                child_namespace = (name,)
        if namespace is not None and here is not None and Path(here).resolve() == resolved:
            if child_namespace is None:
                if namespace:
                    is_function = kind == "FunctionDecl" and not name.startswith("operator") and any(
                        c.get("kind") == "CompoundStmt" for c in inner(node))
                    is_constant = kind == "VarDecl" and re.search(r"\bconst\b", type_of_decl(node))
                    if not (is_function or is_constant or kind in ("TypeAliasDecl", "TypeAliasTemplateDecl")):
                        raise Unsupported("child namespaces require free functions, constants or type aliases")
                    node["lean_cpp_name"] = "::".join((*namespace, name))
                decls.append(node)
        for c in node.get("inner", []):
            walk(c, child_namespace, namespace_depth + (kind == "NamespaceDecl"))

    walk(ast)
    return decls


HEADER = """-- Generated by verifier/lean_translate.py from {source}; do not edit.
-- The translation rules are in docs/translation.md.
{imports}
set_option linter.unusedVariables false

namespace Proofs.Cpp.Gen
"""


def drop_unverified(decls, names):
    """Remove the functions named in `unverified_functions` of the component (stream operators only, by the user
    decision recorded in docs/translation.md): top-level functions and hidden friends of classes."""
    names = set(names)
    if not names:
        return decls
    if not names <= {"operator<<", "operator>>"}:
        raise Unsupported(f"only stream operators may be left unverified: {sorted(names)}")
    def keep(node):
        kind = node.get("kind")
        if kind in ("FunctionDecl", "FunctionTemplateDecl") and node.get("name") in names:
            return False
        if kind == "FriendDecl" and any(c.get("kind") in ("FunctionDecl", "FunctionTemplateDecl")
                                        and c.get("name") in names for c in inner(node)):
            return False
        return True
    def walk(node):
        if node.get("kind") in ("ClassTemplateDecl", "CXXRecordDecl"):
            node["inner"] = [walk(c) if isinstance(c, dict) else c for c in node.get("inner", [])
                             if not isinstance(c, dict) or keep(c)]
        return node
    return [walk(d) for d in decls if keep(d)]


def translate_file(source: Path, imports: list[str], deps=(), standard=clang_ast.DEFAULT_STANDARD, unverified=()) -> str:
    decls = drop_unverified(source_decls(source, standard), unverified)
    tr = Translator(decls, source.read_bytes(), [(source_decls(Path(d), standard), Path(d).read_bytes()) for d in deps])
    body = tr.translate()
    dependent = {"Cpp.ReadField", "Cpp.AddResult", "Cpp.MulResult", "Cpp.AssignResult", "Cpp.ConditionalResult",
                 "Cpp.StaticCall", "Cpp.AdlCall2", "Cpp.Invoke1", "Cpp.Method1", "Cpp.ShiftInt",
                 "Cpp.Field", "Cpp.WriteField", "Cpp.ConstructState", "Cpp.Construct"}
    if any(requirement.split()[0] in dependent
           for fn in tr.built_functions.values() for requirement in fn.reqs.items):
        imports = [*imports, "Proofs.Cpp.Lib.DependentOperations"]
    if "Cpp.UMap" in body or "Cpp.umap" in body:
        imports = [*imports, "Proofs.Cpp.Lib.UMap"]
    if re.search(r"Cpp\.(PQ|pq|Stack|stack|pairLt)", body):
        imports = [*imports, "Proofs.Cpp.Lib.PQ"]
    if re.search(r"Cpp\.(Queue|queue)", body):
        imports = [*imports, "Proofs.Cpp.Lib.Queue"]
    if re.search(r"Cpp\.(OrderedSet|orderedSet)", body):
        imports = [*imports, "Proofs.Cpp.Lib.OrderedSet"]
    if "Cpp.optionalValue" in body:
        imports = [*imports, "Proofs.Cpp.Lib.Optional"]
    if "Cpp.bitWidth " in body:
        imports = [*imports, "Proofs.Cpp.Lib.Basic"]
    if "Cpp.countrZero " in body:
        imports = [*imports, "Proofs.Cpp.Lib.BitOperations"]
    imp = "\n".join(f"import {m}" for m in ["Proofs.Cpp.Prelude", *imports])
    rel = source.resolve().relative_to(ROOT).as_posix() if source.resolve().is_relative_to(ROOT) else source.name
    return HEADER.format(source=rel, imports=imp) + "\n" + body + "\nend Proofs.Cpp.Gen\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source")
    parser.add_argument("--import", dest="imports", action="append", default=[])
    parser.add_argument("--dep", dest="deps", action="append", default=[], help="header of a dependency")
    parser.add_argument("--output")
    parser.add_argument("--standard", choices=clang_ast.STANDARDS, default=clang_ast.DEFAULT_STANDARD)
    parser.add_argument("--unverified", action="append", default=[], help="stream operator left out of the model")
    args = parser.parse_args()
    text = translate_file(Path(args.source), args.imports, args.deps, args.standard, args.unverified)
    if args.output:
        Path(args.output).write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
