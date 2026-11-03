/-!
# Contracts of the C++ standard library (reviewed axioms)

Only facts that cannot be derived from a definition are stated here, and each is registered in
`verification/stl_contracts.json` with the clause of the C++17 standard it comes from. The results of library
operations (for example the sorted order produced by `std::sort`) are *defined* by the model, not postulated; only
the cost bounds, which the standard states asymptotically, are axioms. A theorem that depends on a contract is
reported by `tools/check_proof_security.py` as proved *under an STL contract*.
-/

namespace Proofs.StlContracts

/-- The number of comparisons `std::sort` makes on a range of `n` elements in the worst case (unspecified function). -/
opaque sortComparisons : Nat → Nat

/-- C++17 [alg.sort]/1 (`std::sort`): O(N log N) comparisons. The constant is not fixed by the standard. -/
axiom sort_comparisons_bound : ∃ c : Nat, ∀ n : Nat, sortComparisons n ≤ c * n * (Nat.log2 n + 1)

end Proofs.StlContracts
