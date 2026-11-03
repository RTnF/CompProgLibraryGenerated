import Proofs.DynamicResultRuns

namespace Proofs.DynamicFinishFamily
open Proofs.CppNestedVectorBindings Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicTransfer

-- Only the caller's registered roots need to retain their type and scope.
-- New owned roots may coexist and may be returned without a binding yet.
def compatible (params : List Parameter) (h : ContentsHeap) : Bool := params.all fun p =>
  (h p.owner).any (fun v => decide (v.element = p.element ∧ v.scope = p.scope))

theorem views (params : List Parameter) (h : Heap) (checked : compatible params (eraseHeap h) = true) :
    ∀ p ∈ params, ∃ v, h p.owner = some v ∧ v.element = p.element ∧ v.scope = p.scope := by
  intro p member
  have accepted := List.all_eq_true.mp checked p member
  cases found : h p.owner with
  | none => simp [eraseHeap,found] at accepted
  | some v =>
    have same : v.element = p.element ∧ v.scope = p.scope := by
      have e : (erase v).element = v.element := by cases v <;> rfl
      have sc : (erase v).scope = v.scope := by cases v <;> rfl
      simpa [eraseHeap,found,e,sc] using accepted
    exact ⟨v,rfl,same⟩

theorem Family.restrict {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (kept : List Parameter) (subset : ∀ p ∈ kept, p ∈ params) :
    Family kept h f m :=
  ⟨family.valid,family.models,family.lengths,fun p h => family.bindings p (subset p h),
    fun p h => family.flags p (subset p h),fun p h => family.permissions p (subset p h),
    fun p h => family.views p (subset p h),family.measured⟩

-- Callee bindings may use an entirely different order and contain fewer
-- entries. Rebuild from the caller rather than requiring a parameter subset.
theorem rebound {params innerParams : List Parameter} {old current : Heap} {caller next : Frame} {m0 m : Resources}
    (before : Family params old caller m0) (after : Family innerParams current next m)
    (checked : compatible params (eraseHeap current) = true)
    (flags : ∃ extra, next.rootWritable = caller.rootWritable ++ extra) :
    Family params current {next with bindings := caller.bindings} (resources next) := by
  obtain ⟨extra,flags⟩ := flags
  refine ⟨after.valid,after.models,after.lengths,before.bindings,?_,before.permissions,views params current checked,?_⟩
  · intro p member
    change next.rootWritable[p.owner]? = _
    rw [flags,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (before.flags p member)).1]
    exact before.flags p member
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Proofs.DynamicFinishFamily
