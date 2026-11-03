namespace ConstructorRetirementExamples
open Proofs.CppConstructorRetirement Proofs.CppVectorOwnership
open ConstructorRootsExamples

-- The selected nested root keeps every root-buffer metadata field, not just
-- its child IDs. Its child payload was independently checked by roots tests.
example : result.state.storage.lookup 16 = frame.state.storage.lookup 16 :=
  finished_buffer frame roots 3 2 (by decide) models (by decide) (16,nested) (by decide)
example : result.state.storage.lookup 1 = frame.state.storage.lookup 1 :=
  finished_buffer frame roots 3 2 (by decide) models (by decide) (1,.flat i32 3 [1]) (by decide)

-- Retirement keeps an unrelated root even when its scope is greater than
-- the target; the generic context theorem does not assume a caller bound.
example : frame.state.forest.context 19 = some 8 ∧ 8 ≠ 3 :=
  retired_context_some frame.state.forest (by decide +kernel) 3 19 8 (by decide +kernel)
example : frame.state.forest.context 0 = some 2 ∧ 2 ≠ 3 :=
  retired_context_some frame.state.forest (by decide +kernel) 3 0 2 (by decide +kernel)

example (f : Proofs.CppNestedVectorBindings.Frame) (rs : List Proofs.CppConstructorRoots.Root) (sc : Nat)
    (valid : f.state.wellFormed = true) (distinct : (rs.map Prod.fst).Nodup)
    (models : Proofs.CppConstructorRoots.HaveModels f rs (sc+1))
    (bound : ∀ owner c, f.state.forest.context owner = some c → c ≤ sc+1) :=
  finished_scope_le f rs sc valid distinct models bound
end ConstructorRetirementExamples
