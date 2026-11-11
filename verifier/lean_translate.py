"""Translate the restricted C++ subset of a public header into Lean functions in `Cpp.M`.

The rules are documented in docs/translation.md. The translation reads Clang's JSON AST of the
template definitions (not of their instantiations), so a class or function template over `T` becomes
a Lean definition over a type variable `T` whose required operations are instance arguments.

Anything outside the subset raises `Unsupported`; the translator never guesses.
"""

from __future__ import annotations

import argparse
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


# --------------------------------------------------------------------------------------------- types

@dataclass(frozen=True)
class Ty:
    kind: str                 # int, u32, u64, bool, tparam, vec, pair, cls, void
    name: str = ""            # tparam/cls name
    args: tuple = ()          # vec: (elem,), pair: (a, b), cls: template arguments
    width: int = field(default=64, compare=False)   # int: the C++ width (32, 64, 128); not part of the Lean type

    def __str__(self):
        return lean_type(self)


INT = Ty("int")
INT32 = Ty("int", width=32)
U32 = Ty("u32")
U64 = Ty("u64")
BOOL = Ty("bool")
VOID = Ty("void")

# Signed integers are mathematical integers (Int) under the stated precondition; the width only decides the
# usual arithmetic conversions with unsigned operands. Unsigned 32/64 bit integers wrap around (UInt32/UInt64).
SIGNED_WIDTHS = {
    "int": 32, "short": 32, "signed char": 32, "char": 32, "short int": 32, "std::int32_t": 32, "int32_t": 32,
    "long": 64, "long long": 64, "long int": 64, "long long int": 64, "difference_type": 64, "std::int64_t": 64,
    "int64_t": 64, "ll": 64, "size_type": 64, "__int128": 128, "__int128_t": 128,
    # 128 bit unsigned values are used only below 2^127 (precondition), so they are integers as well.
    "unsigned __int128": 128, "__uint128_t": 128,
}
INTEGER_NAMES = set(SIGNED_WIDTHS)
UNSIGNED_NAMES = {
    "unsigned": U32, "unsigned int": U32, "std::uint32_t": U32, "uint32_t": U32,
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


def parse_type(text: str, tparams: set[str], classes: set[str]) -> Ty:
    s = text.strip()
    s = re.sub(r"\bconst\b|\bvolatile\b|\btypename\b|\bstruct\b|\bclass\b", " ", s)
    s = s.replace("&", " ").strip()
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"^cp::", "", s)
    if s in SIGNED_WIDTHS:
        return Ty("int", width=SIGNED_WIDTHS[s])
    if s in UNSIGNED_NAMES:
        return UNSIGNED_NAMES[s]
    if s in ("unsigned char", "unsigned short", "unsigned short int"):
        raise Unsupported(f"type {text!r}")
    if s == "bool":
        return BOOL
    if s == "void":
        return VOID
    if s in tparams:
        return Ty("tparam", s)
    m = re.fullmatch(r"(?:std::)?vector<(.*)>", s)
    if m:
        args = split_args(m.group(1))
        return Ty("vec", args=(parse_type(args[0], tparams, classes),))
    m = re.fullmatch(r"(?:std::)?pair<(.*)>", s)
    if m:
        a, b = split_args(m.group(1))
        return Ty("pair", args=(parse_type(a, tparams, classes), parse_type(b, tparams, classes)))
    m = re.fullmatch(r"([A-Za-z_][A-Za-z_0-9]*)(?:<(.*)>)?", s)
    if m and m.group(1) in classes:
        args = tuple(parse_type(a, tparams, classes) for a in split_args(m.group(2))) if m.group(2) else ()
        return Ty("cls", m.group(1), args)
    raise Unsupported(f"type {text!r}")


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
    if ty.kind == "void":
        return "Unit"
    if ty.kind == "tparam":
        return ty.name
    if ty.kind == "vec":
        return f"(Array {lean_type(ty.args[0])})"
    if ty.kind == "pair":
        return f"({lean_type(ty.args[0])} × {lean_type(ty.args[1])})"
    if ty.kind == "cls":
        if ty.args:
            return "(" + " ".join(["cp." + ty.name] + [lean_type(a) for a in ty.args]) + ")"
        return "cp." + ty.name
    raise Unsupported(f"type {ty}")


def tparams_of(ty: Ty) -> set[str]:
    if ty.kind == "tparam":
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
}


def lean_name(name: str) -> str:
    return name + "_" if name in LEAN_KEYWORDS else name


# ---------------------------------------------------------------------------------------------- AST

def inner(node):
    return [c for c in node.get("inner", []) if isinstance(c, dict)]


def unsigned_type(node) -> bool:
    qual = node.get("type", {}).get("qualType", "")
    qual = re.sub(r"\bconst\b", "", qual).strip()
    return qual in UNSIGNED_NAMES


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


# ------------------------------------------------------------------------------------------ context

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

    @property
    def mut_refs(self):
        return [p for p in self.params if p[2]]

    def outputs(self):
        out = []
        if self.is_ctor:
            return out
        if self.ret.kind != "void":
            out.append("ret")
        out += [p[0] for p in self.mut_refs]
        if self.owner and not self.is_const and not self.is_static:
            out.append("self")
        return out


@dataclass
class ClassInfo:
    name: str
    tparams: list
    fields: list              # [(name, Ty, init_node or None)]
    methods: list             # [Sig]


class Requirements:
    def __init__(self):
        self.items: list[str] = []

    def add(self, item: str):
        if item not in self.items:
            self.items.append(item)


ORDER = ["Inhabited", "Zero", "One", "NatCast", "IntCast", "Add", "Sub", "Mul", "Neg", "Div", "Mod", "LT", "LE",
         "DecidableLT", "DecidableLE", "DecidableEq", "Min", "Max"]


def binders(tparams, reqs: list[str]) -> str:
    out = []
    for t in tparams:
        out.append(f"{{{t} : Type}}")
    def key(r):
        cls = r.split()[0]
        return (ORDER.index(cls) if cls in ORDER else len(ORDER), r)
    for r in sorted(reqs, key=key):
        out.append(f"[{r}]")
    return " ".join(out)


class Fn:
    """Translation state of one function body."""

    def __init__(self, tr: "Translator", sig: Sig, cls: ClassInfo | None):
        self.tr = tr
        self.sig = sig
        self.cls = cls
        self.scopes: list[dict] = [{}]
        self.lines: list[str] = []
        self.indent = 1
        self.tmp = 0
        self.reqs = Requirements()
        self.field_names = {}
        self.continue_prefix: list[list[str]] = []
        self.callees: list[Sig] = []
        self.used_names: set[str] = set()

    # scopes
    def declare(self, name, ty):
        """Declare a C++ variable; a name already used in the function gets a fresh Lean name, since Lean's
        `do` notation does not let a mutable variable be shadowed (even by a later sibling block)."""
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
        text, ty = self._expr(node, pre, expected)
        if expected is not None:
            text, ty = self.convert(text, ty, expected, node)
        return text, ty

    def convert(self, text, ty, expected, node=None):
        if expected is None or ty == expected:
            return text, (expected if expected is not None and ty.kind == expected.kind == "int" else ty)
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
                # unsigned to signed: the value must fit the signed type (precondition)
                return f"({text}.toNat : Int)", expected
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
        if ty.kind == "unknown":
            return text, expected
        if ty.kind == "tparam" and expected.kind == "int":
            raise Unsupported(f"conversion from {ty.name} to an integer")
        if ty.kind == "vec" and expected.kind == "vec":
            if ty.args[0].kind == "unknown" or ty.args[0] == expected.args[0]:
                return text, expected
        raise Unsupported(f"conversion from {ty} to {expected}")

    def _expr(self, node, pre, expected):
        n = strip(node)
        kind = n.get("kind")
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
            ty = self.lookup(name)
            if ty is None:
                raise Unsupported(f"unknown variable {name}")
            return self.var_name(name), ty
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
            if member in ("first", "second") and inner(n):
                t, bty = self.expr(inner(n)[0], pre)
                if bty.kind == "pair":
                    i = 0 if member == "first" else 1
                    return f"{t}.{i + 1}", bty.args[i]
            raise Unsupported("member access without call")
        if kind == "ArraySubscriptExpr" or (kind == "CXXOperatorCallExpr" and self.operator_name(n) == "[]"):
            base, index = self.subscript_parts(n)
            bt, bty = self.expr(base, pre)
            it, _ = self.expr(index, pre, INT)
            if bty.kind != "vec":
                raise Unsupported(f"subscript of {bty}")
            elem = bty.args[0]
            self.need("Inhabited", elem)
            return f"(Cpp.get {bt} {it})", elem
        if kind == "UnaryOperator":
            op = n["opcode"]
            sub = inner(n)[0]
            if op in ("++", "--"):
                raise Unsupported("increment inside an expression")
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
        if kind == "BinaryOperator":
            return self.binary(n, pre)
        if kind == "CXXOperatorCallExpr":
            op = self.operator_name(n)
            args = inner(n)[1:]
            if op in ("+", "-", "*", "/", "%", "<", ">", "<=", ">=", "==", "!=", "&&", "||") and len(args) == 2:
                return self.binary_parts(op, args[0], args[1], pre)
            if op == "-" and len(args) == 1:
                t, ty = self.expr(args[0], pre)
                if ty.kind == "tparam":
                    self.need("Neg", ty)
                return f"(-{t})", ty
            raise Unsupported(f"operator {op}")
        if kind == "ConditionalOperator":
            c, t, e = inner(n)
            sub_pre_t, sub_pre_e = [], []
            ct, _ = self.expr(c, pre, BOOL)
            tt, tty = self.expr(t, sub_pre_t)
            et, ety = self.expr(e, sub_pre_e, tty if tty.kind != "int" else None)
            if sub_pre_t or sub_pre_e:
                raise Unsupported("a call inside a conditional operator branch")
            if tty != ety:
                tt, tty = self.convert(tt, tty, ety, t)
            return f"(if {ct} then {tt} else {et})", tty
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            return self.call(n, pre)
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

    def binary_parts(self, op, a, b, pre):
        if op in ("&&", "||"):
            at, _ = self.expr(a, pre, BOOL)
            rpre = []
            bt, _ = self.expr(b, rpre, BOOL)
            if rpre:
                raise Unsupported("a call on the right of && or ||")
            return f"({at} {op} {bt})", BOOL
        at, aty = self.expr(a, pre)
        bt, bty = self.expr(b, pre)
        return self.arith(op, at, aty, a, bt, bty, b)

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
            if ty.kind != "int":
                raise Unsupported(f"shift of {ty}")
            bt, _ = self.convert(bt, bty, INT, b)
            return f"(Cpp.{'shl' if op == '<<' else 'shr'} {at} {bt})", ty
        if aty.kind == bty.kind == "bool" and op in ("==", "!="):
            ty = BOOL
        else:
            ty = self.common_type(aty, bty)
        at, _ = self.convert(at, aty, ty, a)
        bt, _ = self.convert(bt, bty, ty, b)
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
        return lean_type(Ty("cls", self.cls.name, tuple(Ty("tparam", t) for t in self.cls.tparams)))

    # ------------------------------------------------------------------ construction
    def construct(self, ty: Ty, n, pre):
        kind = n.get("kind")
        args = [a for a in inner(n) if strip(a).get("kind") not in ("CXXDefaultArgExpr",)]
        if kind == "InitListExpr":
            if ty.kind == "vec":
                items = [self.expr(a, pre, ty.args[0])[0] for a in args]
                return "#[" + ", ".join(items) + "]"
            if ty.kind == "pair" and len(args) == 2:
                a = self.expr(args[0], pre, ty.args[0])[0]
                b = self.expr(args[1], pre, ty.args[1])[0]
                return f"({a}, {b})"
            raise Unsupported(f"initializer list for {ty}")
        if kind == "CXXScalarValueInitExpr":
            return self.default_value(ty)
        if len(args) == 1 and kind in ("ParenListExpr",) and strip(args[0]).get("kind") == "ParenListExpr":
            args = inner(strip(args[0]))
        if ty.kind == "vec":
            if not args:
                return "#[]"
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
            sigs = [s for s in self.tr.classes[ty.name].methods if s.is_ctor]
            return self.call_sig(self.pick(sigs, args, f"constructor of {ty.name}"), None, args, pre, ty)
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
        if ty.kind == "vec":
            return f"(#[] : {lean_type(ty)})"
        if ty.kind == "pair":
            return f"({self.default_value(ty.args[0])}, {self.default_value(ty.args[1])})"
        raise Unsupported(f"default value of {ty}")

    # ------------------------------------------------------------------ calls
    def pick(self, sigs, args, what):
        cands = [s for s in sigs if len(s.params) == len(args)]
        if len(cands) != 1:
            cands2 = [s for s in sigs if len(s.params) >= len(args)
                      and all(self.has_default(s, i) for i in range(len(args), len(s.params)))]
            if len(cands2) == 1:
                return cands2[0]
            raise Unsupported(f"cannot resolve {what} with {len(args)} argument(s)")
        return cands[0]

    def has_default(self, sig, i):
        return False

    def call(self, n, pre):
        kids = inner(n)
        callee = strip(kids[0])
        args = [a for a in kids[1:] if strip(a).get("kind") != "CXXDefaultArgExpr"]
        ck = callee.get("kind")
        # method calls: obj.f(args) / this->f(args)
        if ck in ("MemberExpr", "CXXDependentScopeMemberExpr"):
            name = callee.get("name") or callee.get("member")
            base = strip(inner(callee)[0]) if inner(callee) else None
            if base is None or base.get("kind") == "CXXThisExpr":
                return self.self_call(name, args, pre)
            return self.method_call(base, name, args, pre)
        if ck in ("DeclRefExpr", "UnresolvedLookupExpr", "UnresolvedMemberExpr"):
            name = callee.get("referencedDecl", {}).get("name") if ck == "DeclRefExpr" else callee.get("name")
            if not name:
                name = self.tr.token(callee)
            if ck == "UnresolvedMemberExpr":
                return self.self_call(name, args, pre)
            qualifier = ""
            if ck == "UnresolvedLookupExpr":
                pass
            return self.free_call(name, args, pre, callee)
        if ck == "DependentScopeDeclRefExpr":
            raise Unsupported("call through a dependent scope")
        raise Unsupported(f"call {ck}")

    def self_call(self, name, args, pre):
        if self.cls is None:
            raise Unsupported(f"member call {name} outside a class")
        sigs = [s for s in self.cls.methods if s.cpp_name == name and not s.is_ctor]
        sig = self.pick(sigs, args, name)
        if sig.is_static:
            return self.call_sig(sig, None, args, pre)
        if not self.sig.is_const and not sig.is_const:
            return self.call_sig(sig, "self", args, pre)
        if sig.is_const:
            return self.call_sig(sig, self.self_value(), args, pre)
        raise Unsupported(f"non-const member {name} from a const member")

    def method_call(self, base, name, args, pre):
        bt, bty = self.expr(base, pre)
        if bty.kind == "vec":
            return self.vector_call(base, bt, bty, name, args, pre)
        if bty.kind == "cls":
            info = self.tr.classes[bty.name]
            sigs = [s for s in info.methods if s.cpp_name == name and not s.is_ctor]
            sig = self.pick(sigs, args, f"{bty.name}::{name}")
            if sig.is_const:
                return self.call_sig(sig, bt, args, pre)
            target = self.lvalue(base)
            return self.call_sig(sig, ("obj", target, bt), args, pre)
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

    def free_call(self, name, args, pre, callee):
        if name in ("min", "max") and len(args) == 2:
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
        return self.call_sig(sig, None, args, pre)

    def call_sig(self, sig: Sig, receiver, args, pre, expected=None):
        """Emit `let t ← f receiver args` into pre and write back mutable outputs. Returns (value, Ty)."""
        texts = []
        writes = []
        for (pname, pty, is_ref), arg in zip(sig.params, args):
            if is_ref:
                target = self.lvalue(arg)
                texts.append(self.read_lvalue(target))
                writes.append(target)
            else:
                t, _ = self.expr(arg, pre, self.instantiate_param(pty, sig))
                texts.append(t)
        self.callees.append(sig)
        parts = [sig.lean_name]
        if receiver == "self":
            parts.append(self.self_value())
        elif isinstance(receiver, tuple):
            parts.append(receiver[2])
        elif receiver is not None:
            parts.append(receiver)
        parts += texts
        tmp = self.fresh()
        pre.append(f"let {tmp} ← {' '.join(parts)}")
        outputs = sig.outputs()
        ret_ty = sig.ret if not sig.is_ctor else expected
        if sig.is_ctor:
            return tmp, expected
        values = {}
        if len(outputs) == 1:
            values[outputs[0]] = tmp
        else:
            for i, o in enumerate(outputs):
                values[o] = tmp + "".join([".2"] * i) + (".1" if i < len(outputs) - 1 else "")
        for target, (pname, _, _) in zip(writes, sig.mut_refs):
            pre.extend(self.assign_lines(target, values[pname]))
        if receiver == "self":
            for f, _, _ in self.cls.fields:
                pre.append(f"{self.field_names[f]} := {values['self']}.{lean_name(f)}")
        elif isinstance(receiver, tuple):
            pre.extend(self.assign_lines(receiver[1], values["self"]))
        if sig.ret.kind == "void":
            return "()", VOID
        return values["ret"], self.instantiate_param(sig.ret, sig)

    def instantiate_param(self, ty, sig):
        return ty

    # ------------------------------------------------------------------ lvalues
    def lvalue(self, node):
        """An lvalue path: (root lean name, [index texts], Ty of the whole)."""
        n = strip(node)
        kind = n.get("kind")
        if kind == "DeclRefExpr":
            name = n["referencedDecl"]["name"]
            ty = self.lookup(name)
            if ty is None:
                raise Unsupported(f"unknown variable {name}")
            return (self.var_name(name), [], ty, ty)
        if kind == "CXXDependentScopeMemberExpr" and n.get("member") in ("first", "second") and inner(n):
            root, path, rty, bty = self.lvalue(inner(n)[0])
            if bty.kind != "pair":
                raise Unsupported("member of a non-pair")
            i = 0 if n["member"] == "first" else 1
            return (root, path + [("pair", i)], rty, bty.args[i])
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
            if bty.kind != "vec":
                raise Unsupported("subscript of a non-vector")
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
        return f"{text}.{arg}"

    def assign_lines(self, target, value):
        root, path, _, _ = target
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

    def stmt(self, node):
        kind = node.get("kind")
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
            value = None
            if inner(node):
                value, _ = self.expr(inner(node)[0], pre, self.sig.ret)
            self.flush(pre)
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
            else:
                outs.append(lean_name(o))
        if not outs:
            return "()"
        if len(outs) == 1:
            return outs[0]
        return "(" + ", ".join(outs) + ")"

    def decl(self, d):
        if d.get("kind") != "VarDecl":
            raise Unsupported(f"declaration {d.get('kind')}")
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
        self.block_or_unit(then)
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

    def expr_stmt(self, node):
        n = strip(node)
        kind = n.get("kind")
        pre = []
        if kind == "BinaryOperator" and n["opcode"] == "=":
            lhs, rhs = inner(n)
            target = self.lvalue(lhs)
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
            target = self.lvalue(lhs)
            current = self.read_lvalue(target)
            value, _ = self.binary_parts_text(op, current, target[3], rhs, pre)
            self.flush(pre)
            for line in self.assign_lines(target, value):
                self.emit(line)
            return
        if kind == "UnaryOperator" and n["opcode"] in ("++", "--"):
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
        if callee.get("kind") not in ("MemberExpr", "CXXDependentScopeMemberExpr"):
            return False
        name = callee.get("name") or callee.get("member")
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
        if bty.kind != "vec":
            return False
        args = [a for a in kids[1:] if strip(a).get("kind") != "CXXDefaultArgExpr"]
        target = self.lvalue(base)
        cur = self.read_lvalue(target)
        elem = bty.args[0]
        pre = []
        if name in ("push_back", "emplace_back"):
            if name == "emplace_back" and len(args) != 1:
                if elem.kind == "pair" and len(args) == 2:
                    a = self.expr(args[0], pre, elem.args[0])[0]
                    b = self.expr(args[1], pre, elem.args[1])[0]
                    value = f"({a}, {b})"
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
            for line in self.assign_lines(target, f"(#[] : {lean_type(bty)})"):
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
        raise Unsupported(f"vector::{name}")

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
        return False

    # ------------------------------------------------------------------ loops
    def assigned_names(self, node, out=None):
        """Variables (and fields) a statement may change."""
        if out is None:
            out = set()
        if not isinstance(node, dict):
            return out
        kind = node.get("kind")
        def root(n):
            """The changed variable; `v[]` when only elements of `v` change (its size does not)."""
            n = strip_casts(n)
            element = False
            while True:
                k = n.get("kind")
                if k == "DeclRefExpr":
                    return n["referencedDecl"]["name"] + ("[]" if element else "")
                if k == "MemberExpr":
                    b = strip(inner(n)[0])
                    if b.get("kind") == "CXXThisExpr":
                        return "this." + n["name"] + ("[]" if element else "")
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
        if kind in ("BinaryOperator",) and node.get("opcode") == "=":
            out.add(root(inner(node)[0]))
        if kind == "CompoundAssignOperator":
            out.add(root(inner(node)[0]))
        if kind == "UnaryOperator" and node.get("opcode") in ("++", "--"):
            out.add(root(inner(node)[0]))
        if kind == "CXXOperatorCallExpr" and self.operator_name(node).endswith("=") and \
                self.operator_name(node) not in ("==", "!=", "<=", ">="):
            out.add(root(inner(node)[1]))
        if kind in ("CallExpr", "CXXMemberCallExpr"):
            callee = strip(inner(node)[0])
            if callee.get("kind") in ("MemberExpr", "CXXDependentScopeMemberExpr") and inner(callee):
                name = callee.get("name") or callee.get("member")
                if name not in ("size", "empty", "back", "front"):
                    out.add(root(inner(callee)[0]))
                    if strip(inner(callee)[0]).get("kind") == "CXXThisExpr":
                        out.add("this.*")
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
        var = next(k for k in kids if k.get("kind") == "VarDecl" and k.get("name") not in ("__range1", "__begin1", "__end1"))
        rng = next(k for k in kids if k.get("kind") == "DeclStmt")
        rng_init = inner(inner(rng)[0])[0]
        body = kids[-1]
        pre = []
        rt, rty = self.expr(rng_init, pre)
        if rty.kind != "vec":
            raise Unsupported("range for over a non-vector")
        qual = type_of_decl(var)
        if "&" in qual and "const" not in qual:
            raise Unsupported("range for by mutable reference")
        changed = self.assigned_names(body)
        read = {r.removesuffix(".size") for r in self.read_names(rng_init)}
        if self.conflicts(read, changed):
            raise Unsupported("range for over a vector the body changes")
        self.flush(pre)
        self.scopes.append({})
        self.declare(var["name"], rty.args[0])
        self.emit(f"for {self.var_name(var['name'])} in {rt} do")
        self.indent += 1
        self.emit("Cpp.tick")
        self.continue_prefix.append([])
        self.block(body)
        self.continue_prefix.pop()
        self.indent -= 1
        self.scopes.pop()


def subst(ty: Ty, names, args):
    if ty.kind == "tparam" and ty.name in names:
        i = names.index(ty.name)
        return args[i] if i < len(args) else ty
    if ty.args:
        return Ty(ty.kind, ty.name, tuple(subst(a, names, args) for a in ty.args))
    return ty


# ------------------------------------------------------------------------------------------ translator

class Translator:
    def __init__(self, decls, source_bytes=b""):
        self.decls = decls
        self.source_bytes = source_bytes          # list of top-level AST nodes in source order
        self.classes: dict[str, ClassInfo] = {}
        self.functions: dict[str, list[Sig]] = {}
        self.order: list = []       # ("class", ClassInfo) / ("fn", Sig)
        self.tparams_stack: list[set] = []

    def token(self, node):
        """The first token of a node (Clang's JSON omits the name of some unresolved expressions)."""
        begin = node.get("range", {}).get("begin", {})
        begin = begin.get("spellingLoc", begin)
        if "offset" not in begin or "tokLen" not in begin:
            raise Unsupported(f"no source location for {node.get('kind')}")
        return self.source_bytes[begin["offset"]:begin["offset"] + begin["tokLen"]].decode()

    def ty(self, text, fn: Fn | None = None):
        tps = set()
        if fn is not None:
            tps = set(fn.sig.tparams) | (set(fn.cls.tparams) if fn.cls else set())
            text = container_text(text, fn.sig.containers)
        return parse_type(text, tps, set(self.classes))

    def collect(self):
        for node in self.decls:
            kind = node.get("kind")
            if kind == "ClassTemplateDecl":
                tps = [c["name"] for c in inner(node) if c.get("kind") == "TemplateTypeParmDecl"]
                rec = next((c for c in inner(node) if c.get("kind") == "CXXRecordDecl" and c.get("completeDefinition")), None)
                if rec is not None:
                    self.collect_class(rec, tps)
            elif kind == "CXXRecordDecl" and node.get("completeDefinition"):
                self.collect_class(node, [])
            elif kind == "FunctionTemplateDecl":
                tps = [c["name"] for c in inner(node) if c.get("kind") == "TemplateTypeParmDecl"]
                fn = next((c for c in inner(node) if c.get("kind") == "FunctionDecl"
                           and any(x.get("kind") == "CompoundStmt" for x in inner(c))), None)
                if fn is not None:
                    self.collect_function(fn, tps)
            elif kind == "FunctionDecl":
                if any(x.get("kind") == "CompoundStmt" for x in inner(node)):
                    self.collect_function(node, [])
            elif kind in ("ClassTemplateSpecializationDecl", "TypeAliasTemplateDecl", "TypeAliasDecl"):
                pass
            else:
                raise Unsupported(f"top-level {kind}")
        for name, sigs in self.functions.items():
            if len(sigs) > 1:
                tags = set()
                for sig in sigs:
                    tag = "_".join(type_tag(p[1]) for p in sig.params) if sig.params else "0"
                    if tag in tags:
                        raise Unsupported(f"overloads of {name} with the same parameter kinds")
                    tags.add(tag)
                    sig.lean_name = f"cp.{lean_name(name)}_{tag}"

    def param_list(self, node, tps, containers=()):
        params = []
        for p in inner(node):
            if p.get("kind") == "ParmVarDecl":
                qual = container_text(type_of_decl(p), containers)
                is_ref = "&" in qual and not re.search(r"\bconst\b", qual)
                params.append((p.get("name") or f"arg{len(params)}", parse_type(qual, set(tps), set(self.classes)), is_ref))
        return params

    def collect_function(self, node, tps):
        name = node["name"]
        # A template parameter used as `T::value_type` is a random-access container (modelled by std::vector)
        text = json.dumps(node)
        containers = [t for t in tps if f"{t}::value_type" in text]
        tps = [f"{t}_value_type" if t in containers else t for t in tps]
        ret_text = container_text(node["type"]["qualType"].split("(")[0].strip(), containers)
        ret = parse_type(ret_text, set(tps), set(self.classes))
        sig = Sig(name, f"cp.{name}", self.param_list(node, tps, containers), ret, node=node, tparams=tps)
        sig.containers = containers
        self.functions.setdefault(name, []).append(sig)
        self.order.append(("fn", sig))

    def collect_class(self, rec, tps):
        name = rec["name"]
        info = ClassInfo(name, tps, [], [])
        self.classes[name] = info
        tset = set(tps)
        access = "public" if rec.get("tagUsed") == "struct" else "private"
        for c in inner(rec):
            kind = c.get("kind")
            if kind == "AccessSpecDecl":
                access = c.get("access", access)
            if kind == "FieldDecl":
                init = inner(c)[0] if inner(c) else None
                info.fields.append((c["name"], parse_type(type_of_decl(c), tset, set(self.classes)), init))
            elif kind in ("CXXMethodDecl", "CXXConstructorDecl"):
                if c.get("isImplicit"):
                    continue
                if not any(x.get("kind") == "CompoundStmt" for x in inner(c)):
                    if c.get("explicitlyDefaulted") or c.get("explicitlyDeleted"):
                        continue
                    raise Unsupported(f"member without a body: {c['name']}")
                is_ctor = kind == "CXXConstructorDecl"
                qual = c["type"]["qualType"]
                ret = VOID if is_ctor else parse_type(qual.split("(")[0].strip(), tset, set(self.classes))
                sig = Sig(c["name"].split("<")[0], "", self.param_list(c, tps), ret, owner=name,
                          is_const=qual.rstrip().endswith("const") or is_ctor, is_static=c.get("storageClass") == "static",
                          is_ctor=is_ctor, node=c, tparams=[], public=access == "public")
                info.methods.append(sig)
            elif kind == "CXXDestructorDecl" and c.get("isImplicit"):
                continue
            elif kind in ("CXXRecordDecl", "AccessSpecDecl", "TypeAliasDecl", "TypedefDecl"):
                if kind == "CXXRecordDecl" and c.get("completeDefinition"):
                    raise Unsupported("nested class")
            elif kind == "FriendDecl":
                raise Unsupported("friend")
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
                s.lean_name = f"cp.{name}.{lean_name(base)}{suffix}"
        self.order.append(("class", info))

    # --------------------------------------------------------------- emission
    def translate(self) -> str:
        self.collect()
        sigs = []
        for kind, item in self.order:
            if kind == "class":
                sigs += [(sig, item) for sig in item.methods]
            else:
                sigs.append((item, None))
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
                    for r in cfn.reqs.items:
                        if not (set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", r)) - {r.split()[0]}) <= own:
                            raise Unsupported(f"requirement {r} of {callee.cpp_name} over another type parameter")
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
                if id(callee) in index:
                    visit(id(callee))
            state[key] = "done"
            order.append(key)
        for sig, info in sigs:
            visit(id(sig))
        out = []
        for kind, item in self.order:
            if kind == "class":
                out.append(self.emit_structure(item))
        for key in order:
            sig, info = index[key]
            out.append(self.emit_header(sig, info, built[key]))
        return "\n".join(out)

    def emit_structure(self, info: ClassInfo) -> str:
        head = " ".join(f"({t} : Type)" for t in info.tparams)
        lines = [re.sub(r"  +", " ", f"structure cp.{info.name} {head} where")]
        for fname, fty, _ in info.fields:
            lines.append(f"  {lean_name(fname)} : {lean_type(fty)}")
        lines.append("  deriving Inhabited")
        return "\n".join(lines) + "\n"

    def build_function(self, sig: Sig, info: ClassInfo | None) -> Fn:
        fn = Fn(self, sig, info)
        node = sig.node
        params = []
        for pname, pty, is_ref in sig.params:
            fn.declare(pname, pty)
        cls_ty = None
        if info is not None:
            cls_ty = lean_type(Ty("cls", info.name, tuple(Ty("tparam", t) for t in info.tparams)))
            names = {p[0] for p in sig.params} | local_names(node)
            for fname, fty, _ in info.fields:
                fn.field_names[fname] = ("this_" + fname) if fname in names else lean_name(fname)
                fn.used_names.add(fn.field_names[fname])
        body = next(x for x in inner(node) if x.get("kind") == "CompoundStmt")
        assigned = fn.assigned_names(body)
        fn.emit("Cpp.tick")
        if info is not None and not sig.is_static:
            if sig.is_ctor:
                fn.scopes[0]["__fields__"] = INT
                inits = {}
                for c in inner(node):
                    if c.get("kind") == "CXXCtorInitializer":
                        member = c.get("anyInit", {}).get("name")
                        if member is None:
                            raise Unsupported("delegating or base initializer")
                        inits[member] = inner(c)[0]
                for fname, fty, default_init in info.fields:
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
                    mut = "mut " if not sig.is_const else ""
                    fn.emit(f"let {mut}{fn.field_names[fname]} := self.{lean_name(fname)}")
            for fname, fty, _ in info.fields:
                fn.scopes[0][fname] = fty
            fn.scopes.append({})
        for pname, pty, is_ref in sig.params:
            if pname in assigned or pname + "[]" in assigned:
                fn.emit(f"let mut {lean_name(pname)} := {lean_name(pname)}")
        fn.scopes.append({})
        for s in inner(body):
            fn.stmt(s)
        if sig.is_ctor:
            fn.emit("return " + fn.self_value())
        elif sig.ret.kind == "void":
            fn.emit("return " + fn.result(None))
        elif not inner(body) or inner(body)[-1].get("kind") != "ReturnStmt":
            fn.emit("failure")
        return fn

    def emit_header(self, sig: Sig, info: ClassInfo | None, fn: Fn) -> str:
        cls_ty = None
        if info is not None:
            cls_ty = lean_type(Ty("cls", info.name, tuple(Ty("tparam", t) for t in info.tparams)))
        # header
        tps = list(info.tparams if info else []) + list(sig.tparams)
        reqs = list(fn.reqs.items)
        for pname, pty, _ in sig.params:
            for t in tparams_of(pty):
                if t not in tps:
                    raise Unsupported(f"unknown type parameter {t}")
        args = []
        if info is not None and not sig.is_static and not sig.is_ctor:
            args.append(f"(self : {cls_ty})")
        for pname, pty, _ in sig.params:
            args.append(f"({lean_name(pname)} : {lean_type(pty)})")
        outs = []
        for o in sig.outputs():
            if o == "ret":
                outs.append(lean_type(sig.ret))
            elif o == "self":
                outs.append(cls_ty)
            else:
                outs.append(lean_type(next(p[1] for p in sig.params if p[0] == o)))
        if sig.is_ctor:
            rtype = cls_ty
        elif not outs:
            rtype = "Unit"
        else:
            rtype = " × ".join(outs) if len(outs) > 1 else outs[0]
            if len(outs) > 1:
                rtype = f"({rtype})"
        name = sig.lean_name
        header = f"def {name} {binders(tps, reqs)} {' '.join(args)} : Cpp.M {rtype} := do"
        header = re.sub(r"  +", " ", header)
        return "\n".join([header] + fn.lines) + "\n"


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

def source_decls(source: Path):
    """The top-level declarations of namespace cp written in `source`, in source order (template definitions).

    Clang's JSON prints a location's file only when it differs from the previously printed location, so the
    file of a node is tracked by walking the whole dump in order."""
    command = clang_ast.clang_command() + ["-Xclang", "-ast-dump=json", str(source)]
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

    def walk(node, collect):
        if not isinstance(node, dict):
            return
        visit_loc(node.get("loc"))
        here = state["file"]
        rng = node.get("range", {})
        visit_loc(rng.get("begin"))
        visit_loc(rng.get("end"))
        if collect and here is not None and Path(here).resolve() == resolved:
            decls.append(node)
        is_cp = node.get("kind") == "NamespaceDecl" and node.get("name") == "cp"
        for c in node.get("inner", []):
            walk(c, is_cp)

    walk(ast, False)
    return decls


HEADER = """-- Generated by verifier/lean_translate.py from {source}; do not edit.
-- The translation rules are in docs/translation.md.
{imports}
set_option linter.unusedVariables false

namespace Proofs.Cpp.Gen
"""


def translate_file(source: Path, imports: list[str]) -> str:
    decls = source_decls(source)
    tr = Translator(decls, source.read_bytes())
    body = tr.translate()
    imp = "\n".join(f"import {m}" for m in ["Proofs.Cpp.Prelude", *imports])
    rel = source.resolve().relative_to(ROOT).as_posix()
    return HEADER.format(source=rel, imports=imp) + "\n" + body + "\nend Proofs.Cpp.Gen\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source")
    parser.add_argument("--import", dest="imports", action="append", default=[])
    parser.add_argument("--output")
    args = parser.parse_args()
    text = translate_file(Path(args.source), args.imports)
    if args.output:
        Path(args.output).write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
