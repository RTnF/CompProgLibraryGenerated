"""Public registration gate for nested programs and Context class generation."""

import argparse
import sys

from clang_ast import ROOT, check_source_contract
from nested_ir import lower_source, emit_lean

sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network


def check_source(source, metadata, actual_model):
    check_source_contract(source, metadata)
    translation = metadata.get("translation", "nested_ir")
    if translation == "context_class_ir":
        from context_class_ir import emit_context_class
        expected = emit_context_class(source, metadata["qualified_class"],
            metadata["lean_namespace"], [source.parent])
    elif translation == "nested_ir":
        ir = lower_source(source, [source.parent])
        expected = emit_lean(ir, metadata["lean_namespace"])
    else:
        raise ValueError("unsupported nested or Context class translation")
    if actual_model != expected:
        raise ValueError("C++/common nested IR/generated Lean mismatch; regenerate and reprove")


def check_component(name):
    # Loading the registry verifies every path, declaration manifest and import.
    from public import component, repo_file
    metadata = component(name)
    if metadata.get("translation") not in ("nested_ir", "context_class_ir"):
        raise ValueError("component is not registered for common nested translation")
    source = repo_file(f"library/{metadata['source']}")
    check_source(source, metadata, repo_file(metadata["model"]).read_text())
    print(f"common C++ nested generator and Lean model match: {name}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--component", required=True)
    args = parser.parse_args()
    disable_network()
    check_component(args.component)


if __name__ == "__main__":
    main()
