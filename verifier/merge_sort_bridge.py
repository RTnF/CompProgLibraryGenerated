"""Trusted, source-specific Clang AST to Lean bridge for cp::merge_sort.

The reviewed AST fingerprint binds the generated model to one C++ function body.
Changing the C++ function requires reviewing the translation and fingerprint.
This bridge is part of the explicitly trusted verification boundary.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import tomllib

from clang_ast import ROOT, check_source_contract, filtered_ast, normalized


SOURCE = ROOT / "library/merge_sort.hpp"
OUTPUT = ROOT / "Proofs/Generated/MergeSort.lean"
EXPECTED_AST_SHA256 = "3b974b797c64324bdf136445551d1a6b3fe62ab5a93605fabd5d2b5f2ddf60d4"
EXPECTED_SOURCE_SHA256 = "73f8cd80af2c8ce4cc9c5933bdef72998380761252ec8b3edb1151b55293e305"
REVIEWED_DECLARATIONS = ["FunctionDecl:merge_sort"]


def ast_digest():
    ast = filtered_ast(SOURCE, "merge_sort")
    if ast.get("kind") != "FunctionDecl" or ast.get("name") != "merge_sort":
        raise RuntimeError("expected one cp::merge_sort function AST")
    encoded = json.dumps(normalized(ast), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def generated_lean():
    return f"""-- Emitted by verifier/merge_sort_bridge.py after matching the reviewed Clang AST.
-- Reviewed normalized AST SHA-256: {EXPECTED_AST_SHA256}
-- Trusted mapping: std::vector<int> ↔ List Int, range copies ↔ take/drop,
-- recursive split/merge ↔ the recursive model below with the same <= comparison.
-- The work and slots recurrences count linear split/merge phases and live
-- integer elements using the recorded STL contracts.
import Init.Data.List.Sort.Lemmas
import Init.Data.Nat.Lemmas
import Init.Omega

namespace Proofs.MergeSort

def intLe (a b : Int) : Bool := decide (a ≤ b)

def model : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      let xs := x :: y :: rest
      let mid := xs.length / 2 + xs.length % 2
      List.merge (model (xs.take mid)) (model (xs.drop mid)) intLe
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_wf
    omega

def work : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      work ((n + 2) / 2 + (n + 2) % 2) + work ((n + 2) / 2) + (n + 2)
termination_by n => n
decreasing_by
  all_goals
    first
    | omega
    | exact Nat.div_lt_self (by omega) (by decide)

def calls : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      1 + calls ((n + 2) / 2 + (n + 2) % 2) + calls ((n + 2) / 2)
termination_by n => n
decreasing_by
  all_goals
    first
    | omega
    | exact Nat.div_lt_self (by omega) (by decide)

def slots : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let size := n + 2
      let left := size / 2 + size % 2
      let right := size / 2
      max (size + slots left) (max (size + left + slots right) (3 * size))
termination_by n => n
decreasing_by
  all_goals
    first
    | omega
    | exact Nat.div_lt_self (by omega) (by decide)

end Proofs.MergeSort
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="write the reviewed Lean model")
    args = parser.parse_args()
    metadata = tomllib.loads((ROOT / "library/merge_sort.toml").read_text())
    if metadata.get("source_sha256") != EXPECTED_SOURCE_SHA256:
        raise RuntimeError("library metadata and reviewed source digest differ")
    check_source_contract(SOURCE, metadata)
    if sorted(metadata["public_declarations"]) != REVIEWED_DECLARATIONS:
        raise RuntimeError("public declarations require a source-to-Lean mapping review")
    if metadata.get("reviewed_ast_sha256") != EXPECTED_AST_SHA256:
        raise RuntimeError("library metadata and reviewed AST digest differ")
    digest = ast_digest()
    if digest != EXPECTED_AST_SHA256:
        raise RuntimeError(
            f"C++ AST changed: {digest}; review the source-to-Lean mapping before updating it"
        )
    expected = generated_lean()
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(expected)
    elif not OUTPUT.is_file() or OUTPUT.read_text() != expected:
        raise RuntimeError("generated Lean model is missing or differs from the reviewed mapping")
    print(f"reviewed C++ AST and Lean model match: {digest}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
