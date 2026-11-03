"""Public registration gate for the common syntax-directed state generator."""

import argparse
import sys

from clang_ast import ROOT, check_source_contract
from state_ir import lower_source, emit_lean
from scalar_ir import SIGNED_CONVERSIONS

sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network


def check_source(source, metadata, actual_model):
    check_source_contract(source, metadata)
    signed_conversion = metadata.get("signed_conversion", "checked")
    if signed_conversion not in SIGNED_CONVERSIONS:
        raise ValueError("unsupported signed conversion contract")
    ir = lower_source(source, signed_conversion=signed_conversion)
    if ir["templates"]:
        raise ValueError("public template coverage requires a primary-template proof; concrete instances alone are insufficient")
    expected = emit_lean(ir, metadata["lean_namespace"])
    if actual_model != expected:
        raise ValueError("C++/common IR/generated Lean mismatch; regenerate and reprove")


def check_component(name):
    # Loading the registry verifies every path, declaration manifest and import.
    from public import component, repo_file
    metadata = component(name)
    if metadata.get("translation") != "state_ir":
        raise ValueError("component is not registered for common state translation")
    source = repo_file(f"library/{metadata['source']}")
    check_source(source, metadata, repo_file(metadata["model"]).read_text())
    print(f"common C++ state generator and Lean model match: {name}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--component", required=True)
    args = parser.parse_args()
    disable_network()
    check_component(args.component)


if __name__ == "__main__":
    main()
