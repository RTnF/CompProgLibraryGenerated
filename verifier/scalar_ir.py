"""Syntax-directed lowering for a first, deliberately restricted C++ subset.

No function name or source fingerprint selects a translation rule. Unsupported
declarations, attributes, expressions and statements are rejected.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from clang_ast import ROOT, clang_command
from ast_stream import direct_functions

sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network

TYPES = {
    "bool": (1, False, True), "int": (32, True, False),
    "unsigned int": (32, False, False), "long": (64, True, False),
    "unsigned long": (64, False, False), "long long": (64, True, False),
    "unsigned long long": (64, False, False),
}
BINARY = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "rem", "<": "lt", "<=": "le",
          ">": "gt", ">=": "ge", "==": "eq", "!=": "ne",
          "&": "band", "|": "bor", "^": "bxor", "<<": "shl", ">>": "shr"}
BITWISE = {"band", "bor", "bxor", "shl", "shr"}
UNARY = {"+": "plus", "-": "neg", "!": "not"}
SIGNED_CONVERSIONS = ("checked", "gcc13.3-lp64-twos-complement")


def validate_conversion_target():
    version = subprocess.check_output(["g++", "-dumpfullversion"], text=True).strip()
    target = subprocess.check_output(["g++", "-dumpmachine"], text=True).strip()
    if version != "13.3.0" or target != "x86_64-linux-gnu":
        raise ValueError("unsupported target for signed conversion contract")
    macros = subprocess.check_output(["g++", "-std=c++17", "-dM", "-E", "-x", "c++", "/dev/null"], text=True)
    for name, value in (("__INT_WIDTH__", "32"), ("__LONG_WIDTH__", "64"),
                        ("__LONG_LONG_WIDTH__", "64"), ("__SIZEOF_POINTER__", "8"),
                        ("__CHAR_BIT__", "8"), ("__cplusplus", "201703L")):
        if f"#define {name} {value}\n" not in macros:
            raise ValueError("unsupported ABI for signed conversion contract")


def integer_cast(ty, operand, signed_conversion="checked"):
    source = operand["type"]
    represents_source = (source["boolean"] or
        (source["signed"] and source["width"] <= ty["width"]) or
        (not source["signed"] and source["width"] < ty["width"]))
    target = (signed_conversion == SIGNED_CONVERSIONS[1] and ty["signed"]
              and not ty["boolean"] and not represents_source)
    return {"kind": "target_cast" if target else "cast", "type": ty, "operand": operand}


def apply_conversion_policy(nodes, signed_conversion):
    if signed_conversion not in SIGNED_CONVERSIONS:
        raise ValueError("unsupported signed conversion contract")
    if signed_conversion == "checked":
        return
    validate_conversion_target()
    def mark(node):
        if node.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr", "CXXStaticCastExpr", "CXXFunctionalCastExpr", "CompoundAssignOperator"):
            node["targetSignedConversion"] = signed_conversion
        for child in node.get("inner", []):
            mark(child)
    for node in nodes:
        mark(node)


def scalar_type(node):
    info = node["type"]
    spelling = info.get("desugaredQualType", info["qualType"])
    spelling = re.sub(r"\bconst\s+", "", spelling)
    if spelling not in TYPES:
        raise ValueError(f"unsupported scalar type: {spelling}")
    width, signed, boolean = TYPES[spelling]
    return {"width": width, "signed": signed, "boolean": boolean}


def function_return_type(node):
    info = node["type"]
    spelling = info.get("desugaredQualType", info["qualType"]).split("(", 1)[0].strip()
    # Clang omits the canonical return type for some alias-based signatures.
    # Resolve only aliases whose canonical scalar type is supplied by Clang
    # for a parameter in that same signature. Never guess from alias names.
    for child in node.get("inner", []):
        if child["kind"] == "ParmVarDecl":
            parameter = child["type"]
            if parameter["qualType"] == spelling and "desugaredQualType" in parameter:
                return scalar_type({"type": parameter})
    return scalar_type({"type": {"qualType": spelling}})


def expression(node, slots, call_lowerer=None, node_lowerer=None):
    if node_lowerer is not None:
        lowered = node_lowerer(node, slots)
        if lowered is not None:
            return lowered
    kind = node["kind"]
    children = node.get("inner", [])
    ty = scalar_type(node)
    if kind == "CallExpr" and "verifiedNumericLimit" in node:
        return {"kind": "literal", "type": ty, "value": node["verifiedNumericLimit"]}
    if kind == "CallExpr" and call_lowerer is not None:
        return call_lowerer(node, slots, ty)
    if (kind == "BinaryOperator" and node.get("opcode") == "<<" and len(children) == 2 and
            all(c.get("kind") == "IntegerLiteral" for c in children)):
        left, amount = (int(c["value"]) for c in children)
        if not 0 <= amount < ty["width"] or left < 0:
            raise ValueError("invalid constant left shift")
        power = 1 << amount
        if ty["signed"] and (power >= 1 << (ty["width"]-1) or left*power >= 1 << (ty["width"]-1)):
            raise ValueError("implementation-defined signed constant shift is unsupported")
        return {"kind": "binary", "type": ty, "operation": "mul",
                "left": expression(children[0], slots, call_lowerer, node_lowerer),
                "right": {"kind": "literal", "type": ty, "value": power}}
    if kind in {"IntegerLiteral", "CXXBoolLiteralExpr"} and not children:
        literal = {"kind": "literal", "type": ty, "value": int(node["value"])}
        if "templateParameter" in node:
            literal["param"] = node["templateParameter"]
        return literal
    if kind == "DeclRefExpr" and not children:
        reference = node["referencedDecl"]
        if reference["id"] not in slots:
            raise ValueError("reference to a nonlocal declaration")
        return {"kind": "variable", "type": ty, "slot": slots[reference["id"]]}
    if kind == "ParenExpr" and len(children) == 1:
        return expression(children[0], slots, call_lowerer, node_lowerer)
    if kind == "ImplicitCastExpr" and len(children) == 1:
        if node["castKind"] == "LValueToRValue":
            return expression(children[0], slots, call_lowerer, node_lowerer)
        if node["castKind"] in {"IntegralCast", "IntegralToBoolean"}:
            return integer_cast(ty, expression(children[0], slots, call_lowerer, node_lowerer), node.get("targetSignedConversion", "checked"))
        raise ValueError(f"unsupported implicit cast: {node['castKind']}")
    if kind in {"CStyleCastExpr", "CXXStaticCastExpr", "CXXFunctionalCastExpr"} and len(children) == 1:
        if node.get("valueCategory") != "prvalue":
            raise ValueError("explicit reference/lvalue casts are unsupported")
        operand = expression(children[0], slots, call_lowerer, node_lowerer)
        if node["castKind"] == "NoOp":
            if operand["type"] != ty:
                raise ValueError("no-op explicit cast changed scalar type")
            # Clang has already inserted any real conversion in the operand.
            return operand
        if node["castKind"] in {"IntegralCast", "IntegralToBoolean"}:
            return integer_cast(ty, operand, node.get("targetSignedConversion", "checked"))
        raise ValueError(f"unsupported explicit cast: {node['castKind']}")
    if kind == "BinaryOperator" and node.get("opcode") in BINARY and len(children) == 2:
        if BINARY[node["opcode"]] in BITWISE:
            check_bitwise(node, ty, children)
        return {"kind": "binary", "type": ty, "operation": BINARY[node["opcode"]],
                "left": expression(children[0], slots, call_lowerer, node_lowerer), "right": expression(children[1], slots, call_lowerer, node_lowerer)}
    if kind == "UnaryOperator" and node.get("opcode") in UNARY and len(children) == 1:
        return {"kind": "unary", "type": ty, "operation": UNARY[node["opcode"]],
                "operand": expression(children[0], slots, call_lowerer, node_lowerer)}
    raise ValueError(f"unsupported expression: {kind} {node.get('opcode', '')}")


def check_bitwise(node, ty, children):
    """Bitwise operators are modelled for unsigned types; shift counts must be in-range literals."""
    if ty["signed"] or ty.get("boolean") or ty["width"] < 32:
        raise ValueError("bitwise operators are supported for unsigned 32 and 64 bit types only")
    for child in children:
        if scalar_type(child) != ty and BINARY[node["opcode"]] not in {"shl", "shr"}:
            raise ValueError("bitwise operand type mismatch")
    if BINARY[node["opcode"]] in {"shl", "shr"}:
        if scalar_type(children[0]) != ty:
            raise ValueError("shift left operand type mismatch")
        amount = children[1]
        while amount["kind"] in {"ImplicitCastExpr", "ConstantExpr"} and len(amount.get("inner", [])) == 1:
            amount = amount["inner"][0]
        if amount["kind"] != "IntegerLiteral":
            raise ValueError("shift counts must be integer literals")
        if not 0 <= int(amount["value"]) < ty["width"]:
            raise ValueError("shift count out of range")


def lower_function(node):
    if node["kind"] != "FunctionDecl" or node.get("variadic") or node.get("storageClass"):
        raise ValueError("only ordinary nonvariadic function definitions are supported")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", node["name"]):
        raise ValueError("unsupported function name")
    return_type = function_return_type(node)
    children = node.get("inner", [])
    parameters = []
    slots = {}
    body = None
    for child in children:
        if child["kind"] == "ParmVarDecl" and body is None:
            if child.get("inner"):
                raise ValueError("parameter defaults or attributes are unsupported")
            slots[child["id"]] = len(parameters)
            parameters.append(scalar_type(child))
        elif child["kind"] == "CompoundStmt" and body is None:
            body = child
        else:
            raise ValueError(f"unsupported function child: {child['kind']}")
    if body is None:
        raise ValueError("function definition required")
    locals_ = []
    result = None
    for statement in body.get("inner", []):
        if result is not None:
            raise ValueError("statements after return are unsupported")
        if statement["kind"] == "DeclStmt":
            for declaration in statement.get("inner", []):
                if (declaration["kind"] != "VarDecl" or declaration.get("storageClass")
                        or declaration.get("init") != "c" or len(declaration.get("inner", [])) != 1):
                    raise ValueError("only initialized scalar automatic locals are supported")
                value = expression(declaration["inner"][0], slots)
                ty = scalar_type(declaration)
                if value["type"] != ty:
                    raise ValueError("local initializer type mismatch")
                locals_.append(value)
                slots[declaration["id"]] = len(parameters) + len(locals_) - 1
        elif statement["kind"] == "ReturnStmt" and len(statement.get("inner", [])) == 1:
            result = expression(statement["inner"][0], slots)
        else:
            raise ValueError(f"unsupported statement: {statement['kind']}")
    if result is None:
        raise ValueError("one final return is required")
    if result["type"] != return_type:
        raise ValueError("return type mismatch")
    # The return expression includes Clang's conversion to the declared type.
    return {"name": node["name"], "parameters": parameters, "locals": locals_, "result": result}


def source_ast(source, declaration_filter="cp::", include_dirs=()):
    command = clang_command()
    for directory in include_dirs:
        directory = Path(directory).resolve(strict=True)
        if not directory.is_dir():
            raise ValueError("include path must be a directory")
        command += ["-I", str(directory)]
    definitions = subprocess.check_output(
        [arg for arg in command if arg != "-fsyntax-only"] + ["-dM", "-E", "/dev/null"],
        cwd=ROOT, text=True)
    for macro, width in (("__INT_WIDTH__", 32), ("__LONG_WIDTH__", 64), ("__LLONG_WIDTH__", 64)):
        if f"#define {macro} {width}\n" not in definitions:
            raise ValueError(f"unsupported C++ ABI: {macro} must be {width}")
    if declaration_filter is None:
        with tempfile.TemporaryFile() as output:
            subprocess.run(command + ["-Xclang", "-ast-dump=json", str(source)],
                           cwd=ROOT, stdout=output, check=True)
            output.seek(0)
            return direct_functions(output, source)
    output = subprocess.check_output(command + [
        "-Xclang", "-ast-dump=json", "-Xclang", f"-ast-dump-filter={declaration_filter}", str(source)],
        cwd=ROOT, text=True)
    decoder = json.JSONDecoder()
    position = 0
    declarations = []
    while position < len(output):
        while position < len(output) and output[position].isspace():
            position += 1
        if position == len(output):
            break
        node, position = decoder.raw_decode(output, position)
        declarations.append(node)
    return declarations


def lower_source(source, signed_conversion="checked"):
    nodes = source_ast(source)
    apply_conversion_policy(nodes, signed_conversion)
    functions = [lower_function(node) for node in nodes]
    if not functions or len({f["name"] for f in functions}) != len(functions):
        raise ValueError("nonempty, uniquely named definitions are required")
    ir = {"abi": "LP64: int32, long64, long-long64", "functions": functions}
    if signed_conversion != "checked":
        ir["signed_conversion"] = signed_conversion
    return ir


# While true, literals that came from a template parameter are rendered as the Lean variable of that parameter.
PARAMETRIC = False


def lean_type(ty):
    return f"⟨{ty['width']}, {str(ty['signed']).lower()}, {str(ty['boolean']).lower()}⟩"


def lean_expression(expr, node_renderer=None):
    if node_renderer is not None:
        rendered = node_renderer(expr)
        if rendered is not None:
            return rendered
    ty = lean_type(expr["type"])
    kind = expr["kind"]
    if kind == "literal":
        if PARAMETRIC and "param" in expr:
            return f"(.literal {ty} ({expr['param']}))"
        return f"(.literal {ty} ({expr['value']}))"
    if kind == "variable":
        return f"(.variable {ty} {expr['slot']})"
    if kind in ("cast", "target_cast"):
        constructor = "targetCast" if kind == "target_cast" else "cast"
        return f"(.{constructor} {ty} {lean_expression(expr['operand'], node_renderer)})"
    if kind == "unary":
        return f"(.unary {ty} .{expr['operation']} {lean_expression(expr['operand'], node_renderer)})"
    if kind == "binary":
        if expr['operation'] in {'div', 'rem'}:
            remainder = str(expr['operation'] == 'rem').lower()
            return (f"(.divrem {ty} {remainder} {lean_expression(expr['left'], node_renderer)} "
                    f"{lean_expression(expr['right'], node_renderer)})")
        return (f"(.binary {ty} .{expr['operation']} {lean_expression(expr['left'], node_renderer)} "
                f"{lean_expression(expr['right'], node_renderer)})")
    raise ValueError(f"unknown IR expression: {kind}")


def emit_lean(ir, namespace):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", namespace):
        raise ValueError("invalid Lean namespace")
    lines = ["-- Generated by verifier/scalar_ir.py; syntax-directed scalar subset.",
             "import Proofs.CppScalar", "", f"namespace {namespace}", "open Proofs.CppScalar", ""]
    if "signed_conversion" in ir:
        lines.insert(1, "-- Signed conversion contract: " + ir["signed_conversion"])
    for function in ir["functions"]:
        params = ", ".join(lean_type(p) for p in function["parameters"])
        locals_ = ", ".join(lean_expression(e) for e in function["locals"])
        # Quoted Lean identifiers prevent C++ names such as `match` colliding.
        lines += [f"def «{function['name']}» : Program :=", f"  ⟨[{params}], [{locals_}],",
                  f"   {lean_expression(function['result'])}⟩", ""]
    return "\n".join(lines + [f"end {namespace}", ""])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--ir", type=Path, required=True)
    parser.add_argument("--namespace", default="Proofs.Generated.Scalar")
    parser.add_argument("--signed-conversion", choices=SIGNED_CONVERSIONS, default="checked")
    args = parser.parse_args()
    disable_network()
    ir = lower_source(args.source, args.signed_conversion)
    lean = emit_lean(ir, args.namespace)
    args.ir.write_text(json.dumps(ir, indent=2) + "\n")
    args.lean.write_text(lean)


if __name__ == "__main__":
    main()
