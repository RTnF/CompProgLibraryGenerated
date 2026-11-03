"""Shared scalar statements and lvalue-reference lowering, with aliasing."""

import argparse
import json
from pathlib import Path
import re

from scalar_ir import expression, scalar_type, source_ast, lean_expression, lean_type, BINARY, function_return_type
from offline import disable_network
from scalar_stl import verify_scalar_swaps
from scalar_assert import verify_scalar_asserts
from scalar_assert import direct_callee
from scalar_ir import apply_conversion_policy, integer_cast, SIGNED_CONVERSIONS


def concrete_template_instances(node):
    """Validate and select the actual Clang type-template instantiations."""
    primary = None
    instances = []
    parameter_count = 0
    for child in node.get("inner", []):
        if (child["kind"] == "TemplateTypeParmDecl" and primary is None
                and not child.get("inner") and not child.get("isParameterPack")):
            parameter_count += 1
            continue
        if child["kind"] != "FunctionDecl":
            raise ValueError("only type-parameter function templates are supported")
        args = [c for c in child.get("inner", []) if c["kind"] == "TemplateArgument"]
        if primary is None:
            if args or not parameter_count:
                raise ValueError("type-template primary declaration required")
            primary = child["id"]
            continue
        if child.get("TemplateInstantiationPattern") != primary:
            raise ValueError("explicit specializations are unsupported")
        if len(args) != parameter_count:
            raise ValueError("concrete template arguments required")
        for argument in args:
            scalar_type(argument)
        instances.append(child)
    if not instances:
        raise ValueError("template has no concrete instantiations to verify")
    return instances


class ValueCalls:
    """Resolve scalar callees by declaration identity within one AST dump."""

    def __init__(self, nodes):
        self.definitions = {}
        self.aliases = {}
        self.previous = {}
        self.completed = {}
        self.active = set()
        self.template_instances = {}
        declarations = []
        for node in nodes:
            if node.get("kind") == "FunctionTemplateDecl":
                instances = concrete_template_instances(node)
                self.template_instances[node["id"]] = instances
                declarations.extend(instances)
            else:
                if any(c.get("kind") == "TemplateArgument" for c in node.get("inner", [])):
                    raise ValueError("explicit specializations are unsupported")
                declarations.append(node)
        for node in declarations:
            if node.get("kind") != "FunctionDecl":
                continue
            if node.get("previousDecl"):
                self.aliases[node["previousDecl"]] = node["id"]
                self.previous[node["id"]] = node["previousDecl"]
            if any(c.get("kind") == "CompoundStmt" for c in node.get("inner", [])):
                self.definitions[node["id"]] = node

    def resolve(self, identity):
        visited = set()
        pending = [identity]
        while pending:
            identity = pending.pop()
            if identity in visited:
                continue
            visited.add(identity)
            pending.extend(mapping[identity] for mapping in (self.aliases, self.previous) if identity in mapping)
        definitions = visited & self.definitions.keys()
        if len(definitions) != 1:
            raise ValueError("call requires a definition in the selected AST")
        identity = next(iter(definitions))
        if identity in self.active:
            raise ValueError("recursive calls are unsupported")
        if identity not in self.completed:
            self.active.add(identity)
            try:
                self.completed[identity] = lower_function(self.definitions[identity], self)
            finally:
                self.active.remove(identity)
        return self.completed[identity]


def contains_kind(value, kind):
    if isinstance(value, dict):
        return value.get("kind") == kind or any(contains_kind(v, kind) for v in value.values())
    if isinstance(value, list):
        return any(contains_kind(v, kind) for v in value)
    return False


def call_expression(node, slots, bindings, calls):
    """ANF calls; effectful reference calls require a whole expression."""
    prelude = []

    def lower(call, caller_slots, ty):
        callee = direct_callee(call)
        reference = callee.get("referencedDecl", {}) if callee is not None else {}
        if reference.get("kind") != "FunctionDecl":
            raise ValueError("only direct ordinary function calls are supported")
        function = calls.resolve(reference["id"])
        parameters = function["parameters"]
        if ty != function["result_type"]:
            raise ValueError("call return type mismatch")
        children = call.get("inner", [])[1:]
        if len(children) != len(parameters):
            raise ValueError("call argument types or count mismatch")
        extended = any(p["reference"] for p in parameters) or contains_kind(function["body"], "reference_invoke")
        arguments = []
        for child, parameter in zip(children, parameters):
            if parameter["reference"]:
                target = child
                while target["kind"] == "ParenExpr" or (target["kind"] == "ImplicitCastExpr" and target.get("castKind") == "NoOp"):
                    target = target["inner"][0]
                if target["kind"] != "DeclRefExpr":
                    raise ValueError("reference arguments require direct lvalue bindings")
                slot = caller_slots.get(target["referencedDecl"]["id"])
                if slot is None or bindings[slot]["type"] != parameter["type"]:
                    raise ValueError("reference argument binding or type mismatch")
                if parameter["writable"] and not bindings[slot]["writable"]:
                    raise ValueError("reference argument requires a writable binding")
                arguments.append({"kind": "reference", "slot": slot})
            else:
                value = expression(child, caller_slots, lower)
                if value["type"] != parameter["type"]:
                    raise ValueError("call argument types or count mismatch")
                arguments.append({"kind": "value", "value": value} if extended else value)
        prelude.append({"kind": "reference_invoke" if extended else "invoke", "parameters": parameters,
                        "result_type": ty, "arguments": arguments, "body": function["body"]})
        slot = len(bindings)
        bindings.append({"type": ty, "reference": False, "writable": False})
        return {"kind": "variable", "type": ty, "slot": slot}

    value = expression(node, slots, lower if calls is not None else None)
    reference_calls = [p for p in prelude if p["kind"] == "reference_invoke"]
    if reference_calls:
        outer = node
        while outer["kind"] == "ParenExpr" or outer["kind"] in {"ImplicitCastExpr", "CStyleCastExpr", "CXXStaticCastExpr", "CXXFunctionalCastExpr"}:
            outer = outer["inner"][0]
        if outer["kind"] != "CallExpr" or len(reference_calls) != 1 or prelude[-1] is not reference_calls[0]:
            raise ValueError("reference calls require a standalone expression; nested or compound effects are unsupported")
    return prelude, value


def with_calls(prelude, result):
    return {"kind": "scope", "body": sequence([*prelude, result])} if prelude else result


def loop_with_calls(prelude, condition, body):
    """Evaluate condition calls on every test, discarding their private slots.

    A false test breaks this loop; an existing body break skips any for update.
    Without calls preserve the original IR and its observation/resource costs.
    """
    if not prelude:
        return {"kind": "while", "condition": condition, "body": body}
    return {"kind": "while", "condition": {
        "kind": "literal", "type": {"width": 1, "signed": False, "boolean": True}, "value": 1},
        "body": with_calls(prelude, {"kind": "branch", "condition": condition,
            "yes": body, "no": {"kind": "break"}})}


def parameter_type(node):
    spelling = node["type"].get("desugaredQualType", node["type"]["qualType"])
    reference = spelling.endswith(" &")
    if "&&" in spelling:
        raise ValueError("rvalue references are unsupported")
    base = spelling[:-2] if reference else spelling
    ty = scalar_type({"type": {"qualType": base}})
    return {"type": ty, "reference": reference, "writable": "const" not in base.split()}


def sequence(statements):
    result = {"kind": "skip"}
    for statement in reversed(statements):
        result = {"kind": "sequence", "first": statement, "rest": result}
    return result


def assertion_condition(node, slots, yes=None, no=None):
    """Short circuit pure predicates; failed assertions never become assumptions."""
    yes = {"kind": "skip"} if yes is None else yes
    no = {"kind": "check", "condition": {"kind": "literal",
          "type": {"width": 1, "signed": False, "boolean": True}, "value": 0}} if no is None else no
    while node["kind"] == "ParenExpr" or (node["kind"] == "CXXStaticCastExpr" and node.get("castKind") == "NoOp"):
        node = node["inner"][0]
    children = node.get("inner", [])
    if node["kind"] == "BinaryOperator" and node.get("opcode") in ("&&", "||") and len(children) == 2:
        right = assertion_condition(children[1], slots, yes, no)
        first = assertion_condition(children[0], slots, right if node["opcode"] == "&&" else yes,
                                     no if node["opcode"] == "&&" else right)
        # Charge an extra successful check per logical connective. This keeps
        # the short-circuit lowering conservative even for deep Boolean trees.
        return sequence([first, {"kind": "check", "condition": {"kind": "literal",
                         "type": {"width": 1, "signed": False, "boolean": True}, "value": 1}}])
    return {"kind": "branch", "condition": expression(node, slots), "yes": yes, "no": no}


def statement(node, slots, bindings, loop_depth=0, calls=None):
    kind = node["kind"]
    children = node.get("inner", [])
    if kind == "ParenExpr" and len(children) == 1:
        return statement(children[0], slots, bindings, loop_depth, calls)
    if kind == "ConditionalOperator" and node.get("verifiedScalarAssert"):
        return assertion_condition(children[0], slots)
    if kind == "CompoundStmt":
        local_slots, local_bindings = dict(slots), list(bindings)
        body = [statement(child, local_slots, local_bindings, loop_depth, calls) for child in children]
        return {"kind": "scope", "body": sequence(body)}
    if kind == "DeclStmt" and children:
        declarations = []
        for child in children:
            if (child["kind"] != "VarDecl" or child.get("storageClass")
                    or child.get("init") != "c" or len(child.get("inner", [])) != 1):
                raise ValueError("only initialized automatic scalar locals are supported")
            descriptor = parameter_type(child)
            if descriptor["reference"]:
                raise ValueError("local references are unsupported")
            prelude, value = call_expression(child["inner"][0], slots, bindings, calls)
            if value["type"] != descriptor["type"]:
                raise ValueError("initializer type mismatch")
            declarations.extend(prelude)
            declarations.append({"kind": "declare", **descriptor, "value": value})
            slots[child["id"]] = len(bindings)
            bindings.append(descriptor)
        return sequence(declarations)
    assignment = kind == "BinaryOperator" and node.get("opcode") == "="
    compound = kind == "CompoundAssignOperator" and node.get("opcode") in {"+=", "-=", "*=", "/=", "%="}
    if (assignment or compound) and len(children) == 2:
        target = children[0]
        while target["kind"] == "ParenExpr":
            target = target["inner"][0]
        if target["kind"] != "DeclRefExpr":
            raise ValueError("only direct scalar binding assignment is supported")
        slot = slots.get(target["referencedDecl"]["id"])
        if slot is None or not bindings[slot]["writable"]:
            raise ValueError("assignment requires a writable local binding")
        prelude, value = call_expression(children[1], slots, list(bindings), calls)
        if compound:
            lhs_type = scalar_type({"type": node["computeLHSType"]})
            compute_type = scalar_type({"type": node["computeResultType"]})
            target_type = bindings[slot]["type"]
            if lhs_type != compute_type or value["type"] != compute_type or scalar_type(node) != target_type:
                raise ValueError("unsupported compound assignment computation types")
            left = expression(target, slots)
            if left["type"] != lhs_type:
                left = integer_cast(lhs_type, left, node.get("targetSignedConversion", "checked"))
            value = {"kind": "binary", "type": compute_type,
                     "operation": BINARY[node["opcode"][:-1]], "left": left, "right": value}
            if compute_type != target_type:
                value = integer_cast(target_type, value, node.get("targetSignedConversion", "checked"))
        if value["type"] != bindings[slot]["type"]:
            raise ValueError("assignment conversion mismatch")
        return with_calls(prelude, {"kind": "assign", "slot": slot, "value": value})
    if kind == "ReturnStmt" and len(children) == 1:
        prelude, value = call_expression(children[0], slots, list(bindings), calls)
        return with_calls(prelude, {"kind": "return", "value": value})
    if kind == "IfStmt" and len(children) in (2, 3):
        if node.get("hasInit") or node.get("hasVar") or node.get("isConstexpr"):
            raise ValueError("if initializers, declarations and constexpr conditions are unsupported")
        condition_bindings = list(bindings)
        prelude, condition = call_expression(children[0], slots, condition_bindings, calls)
        # Statement-local declarations cannot escape either branch.
        yes = {"kind": "scope", "body": statement(children[1], dict(slots), list(condition_bindings), loop_depth, calls)}
        no = {"kind": "scope", "body": statement(children[2], dict(slots), list(condition_bindings), loop_depth, calls)} if len(children) == 3 else {"kind": "skip"}
        return with_calls(prelude, {"kind": "branch", "condition": condition, "yes": yes, "no": no})
    if kind == "NullStmt":
        return {"kind": "skip"}
    if kind == "CallExpr" and node.get("verifiedScalarSwap"):
        addresses = []
        for target in children[1:]:
            while target["kind"] == "ParenExpr":
                target = target["inner"][0]
            if target["kind"] != "DeclRefExpr":
                raise ValueError("scalar std::swap requires direct bindings")
            slot = slots.get(target["referencedDecl"]["id"])
            if slot is None or not bindings[slot]["writable"]:
                raise ValueError("scalar std::swap requires writable bindings")
            addresses.append(slot)
        if len(addresses) != 2 or bindings[addresses[0]]["type"] != bindings[addresses[1]]["type"]:
            raise ValueError("scalar std::swap requires two bindings of the same type")
        return {"kind":"swap","left":addresses[0],"right":addresses[1]}
    if kind == "BreakStmt" and not children:
        if loop_depth == 0:
            raise ValueError("break requires an enclosing supported loop")
        return {"kind": "break"}
    if kind == "CallExpr":
        prelude, _ = call_expression(node, slots, list(bindings), calls)
        return with_calls(prelude, {"kind": "skip"})
    if kind == "UnaryOperator" and node.get("opcode") in ("++", "--") and len(children) == 1:
        target = children[0]
        if target["kind"] != "DeclRefExpr":
            raise ValueError("increment/decrement requires a direct scalar binding")
        slot = slots.get(target["referencedDecl"]["id"])
        if slot is None or not bindings[slot]["writable"] or bindings[slot]["type"]["boolean"]:
            raise ValueError("increment/decrement requires a writable integer binding")
        ty = bindings[slot]["type"]
        value = {"kind": "binary", "type": ty,
                 "operation": "add" if node["opcode"] == "++" else "sub",
                 "left": expression(target, slots), "right": {"kind": "literal", "type": ty, "value": 1}}
        return {"kind": "assign", "slot": slot, "value": value}
    if kind == "WhileStmt" and len(children) == 2 and not node.get("hasVar"):
        condition_bindings = list(bindings)
        prelude, condition = call_expression(children[0], slots, condition_bindings, calls)
        body = {"kind": "scope", "body": statement(children[1], dict(slots), condition_bindings, loop_depth + 1, calls)}
        return loop_with_calls(prelude, condition, body)
    if kind == "ForStmt" and len(children) == 5:
        initial, condition_variable, condition, increment, body = children
        if condition_variable:
            raise ValueError("for condition declarations are unsupported")
        loop_slots, loop_bindings = dict(slots), list(bindings)
        start = statement(initial, loop_slots, loop_bindings, loop_depth, calls) if initial else {"kind": "skip"}
        condition_bindings = list(loop_bindings)
        prelude, test = call_expression(condition, loop_slots, condition_bindings, calls) if condition else ([], {
            "kind": "literal", "type": {"width": 1, "signed": False, "boolean": True}, "value": 1})
        iteration = {"kind": "scope", "body": statement(body, dict(loop_slots), list(condition_bindings), loop_depth + 1, calls)}
        update = statement(increment, dict(loop_slots), list(condition_bindings), loop_depth, calls) if increment else {"kind": "skip"}
        return {"kind": "scope", "body": sequence([start,
            loop_with_calls(prelude, test, sequence([iteration, update]))])}
    raise ValueError(f"unsupported state statement: {kind}")


def lower_function(node, calls=None):
    if (node["kind"] != "FunctionDecl" or node.get("variadic") or node.get("storageClass")
            or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", node.get("name", ""))):
        raise ValueError("ordinary nonvariadic function definitions required")
    result_type = function_return_type(node)
    parameters, slots = [], {}
    body = None
    for child in node.get("inner", []):
        if child["kind"] == "TemplateArgument" and body is None:
            scalar_type(child)
        elif child["kind"] == "ParmVarDecl" and body is None and not child.get("inner"):
            slots[child["id"]] = len(parameters)
            parameters.append(parameter_type(child))
        elif child["kind"] == "CompoundStmt" and body is None:
            body = statement(child, slots, list(parameters), calls=calls)
        else:
            raise ValueError(f"unsupported function child: {child['kind']}")
    if body is None:
        raise ValueError("function definition required")
    return {"name": node["name"], "parameters": parameters, "result_type": result_type, "body": body}


def lower_source(source, declaration_filter="cp::", include_dirs=(), signed_conversion="checked"):
    functions, templates = [], []
    nodes = source_ast(source, declaration_filter, include_dirs)
    verify_scalar_swaps(source, nodes, include_dirs)
    verify_scalar_asserts(source, nodes, include_dirs)
    apply_conversion_policy(nodes, signed_conversion)
    calls = ValueCalls(nodes)
    for node in nodes:
        if node["kind"] != "FunctionTemplateDecl":
            if not any(c.get("kind") == "CompoundStmt" for c in node.get("inner", [])):
                if node.get("kind") != "FunctionDecl":
                    raise ValueError("ordinary function declarations required")
                function = calls.resolve(node["id"])
                if (node.get("variadic") or node.get("storageClass")
                        or any(c.get("kind") != "ParmVarDecl" or c.get("inner") for c in node.get("inner", []))
                        or function_return_type(node) != function["result_type"]
                        or [parameter_type(c) for c in node.get("inner", [])] != function["parameters"]):
                    raise ValueError("unsupported function redeclaration")
                continue
            functions.append(calls.resolve(node["id"]))
            continue
        instances = []
        for child in calls.template_instances[node["id"]]:
            args = [c for c in child.get("inner", []) if c["kind"] == "TemplateArgument"]
            # Keep cached callee IR unrenamed; exported instances receive a
            # distinct root name, but calls carry their actual body and types.
            instance = dict(calls.resolve(child["id"]))
            spellings = [arg["type"]["qualType"] for arg in args]
            instance["template_arguments"] = spellings
            instance["cpp_name"] = instance["name"]
            instance["name"] += "__" + "__".join(s.replace(" ", "_") for s in spellings)
            functions.append(instance)
            instances.append(instance["name"])
        templates.append({"name": node["name"], "coverage": "concrete_instances_only", "instances": instances})
    if not functions or len({f["name"] for f in functions}) != len(functions):
        raise ValueError("nonempty, uniquely named definitions required")
    ir = {"abi": "LP64: int32, long64, long-long64", "templates": templates, "functions": functions}
    if signed_conversion != "checked":
        ir["signed_conversion"] = signed_conversion
    return ir


def lean_statement(stmt):
    kind = stmt["kind"]
    if kind == "skip":
        return ".skip"
    if kind == "check":
        return f"(.check {lean_expression(stmt['condition'])})"
    if kind == "break":
        return ".breakLoop"
    if kind == "swap":
        return f"(.swap {stmt['left']} {stmt['right']})"
    if kind == "scope":
        return f"(.scope {lean_statement(stmt['body'])})"
    if kind == "sequence":
        return f"(.sequence {lean_statement(stmt['first'])} {lean_statement(stmt['rest'])})"
    if kind == "declare":
        return f"(.declare {lean_type(stmt['type'])} {str(stmt['writable']).lower()} {lean_expression(stmt['value'])})"
    if kind == "assign":
        return f"(.assign {stmt['slot']} {lean_expression(stmt['value'])})"
    if kind == "return":
        return f"(.ret {lean_expression(stmt['value'])})"
    if kind == "branch":
        return (f"(.branch {lean_expression(stmt['condition'])} "
                f"{lean_statement(stmt['yes'])} {lean_statement(stmt['no'])})")
    if kind == "while":
        return f"(.whileLoop {lean_expression(stmt['condition'])} {lean_statement(stmt['body'])})"
    if kind == "invoke":
        parameters = ", ".join(f"({lean_type(p['type'])}, {str(p['writable']).lower()})" for p in stmt["parameters"])
        arguments = ", ".join(lean_expression(a) for a in stmt["arguments"])
        return f"(.invoke [{parameters}] {lean_type(stmt['result_type'])} [{arguments}] {lean_statement(stmt['body'])})"
    raise ValueError(f"unknown statement: {kind}")


def lean_reference_statement(stmt):
    if not contains_kind(stmt, "reference_invoke"):
        return f"(.legacy {lean_statement(stmt)})"
    kind = stmt["kind"]
    if kind == "reference_invoke":
        parameters = ", ".join(f"⟨{lean_type(p['type'])}, {str(p['reference']).lower()}, {str(p['writable']).lower()}⟩" for p in stmt["parameters"])
        arguments = ", ".join(f"(.reference {a['slot']})" if a["kind"] == "reference" else f"(.value {lean_expression(a['value'])})" for a in stmt["arguments"])
        return f"(.invoke [{parameters}] {lean_type(stmt['result_type'])} [{arguments}] {lean_reference_statement(stmt['body'])})"
    if kind == "scope":
        return f"(.scope {lean_reference_statement(stmt['body'])})"
    if kind == "sequence":
        return f"(.sequence {lean_reference_statement(stmt['first'])} {lean_reference_statement(stmt['rest'])})"
    if kind == "branch":
        return f"(.branch {lean_expression(stmt['condition'])} {lean_reference_statement(stmt['yes'])} {lean_reference_statement(stmt['no'])})"
    if kind == "while":
        return f"(.whileLoop {lean_expression(stmt['condition'])} {lean_reference_statement(stmt['body'])})"
    raise ValueError(f"unknown reference command: {kind}")


def emit_lean(ir, namespace="Proofs.Generated.State"):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", namespace):
        raise ValueError("invalid Lean namespace")
    def has_loop(value):
        if isinstance(value, dict):
            return value.get("kind") == "while" or any(has_loop(v) for v in value.values())
        if isinstance(value, list):
            return any(has_loop(v) for v in value)
        return False
    any_loops = any(has_loop(f["body"]) for f in ir["functions"])
    lines = ["-- Generated syntax-directed scalar state IR.",
             "import Proofs.CppReferenceCommands" if contains_kind(ir, "reference_invoke") else ("import Proofs.CppLoop" if any_loops else "import Proofs.CppState"), "",
             f"namespace {namespace}", "open Proofs.CppScalar Proofs.CppState", ""]
    if "signed_conversion" in ir:
        lines.insert(1, "-- Signed conversion contract: " + ir["signed_conversion"])
    if any_loops:
        lines += ["open Proofs.CppLoop", ""]
    for function in ir["functions"]:
        params = ", ".join(f"⟨{lean_type(p['type'])}, {str(p['reference']).lower()}, {str(p['writable']).lower()}⟩"
                           for p in function["parameters"])
        extended = contains_kind(function["body"], "reference_invoke")
        program_type = "Proofs.CppReferenceCommands.Program" if extended else ("LoopProgram" if has_loop(function["body"]) else "StateProgram")
        body = lean_reference_statement(function["body"]) if extended else lean_statement(function["body"])
        lines += [f"def «{function['name']}» : {program_type} :=", f"  ⟨[{params}], {lean_type(function['result_type'])},",
                  f"   {body}⟩", ""]
    return "\n".join(lines + [f"end {namespace}", ""])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--ir", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--namespace", default="Proofs.Generated.State")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--declaration-filter", default="cp::")
    selection.add_argument("--direct-file", action="store_true")
    parser.add_argument("--signed-conversion", choices=SIGNED_CONVERSIONS, default="checked")
    parser.add_argument("--include-dir", type=Path, action="append", default=[])
    args = parser.parse_args()
    disable_network()
    ir = lower_source(args.source, None if args.direct_file else args.declaration_filter, args.include_dir, args.signed_conversion)
    args.ir.write_text(json.dumps(ir, indent=2) + "\n")
    args.lean.write_text(emit_lean(ir, args.namespace))


if __name__ == "__main__":
    main()
