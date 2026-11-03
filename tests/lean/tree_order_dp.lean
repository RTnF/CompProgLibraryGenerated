namespace TreeOrderToDpExamples
open Proofs.TreeOrderMath Proofs.TreeDpMath Proofs.TreeDpSpec

def heads : List Nat := [0,2,4,6]
def targets : List Nat := [1,2,0,2,0,1]
def parents : List Int := [0,0,0]

-- The order generator only follows parent-to-child arcs. Extra arcs need not
-- prevent it from generating a complete order, but they invalidate tree DP.
theorem triangle_order : TO heads targets parents 3 0 := by
  refine ⟨by decide +kernel,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have cases : w=0 ∨ w=1 ∨ w=2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel
  · intro v hv p hp
    have cases : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases cases with rfl | rfl | rfl <;> simp [arcs,heads,List.range'_succ] at hp <;>
      rcases hp with rfl | rfl <;> decide +kernel
  · intro v hv p hp
    have cases : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases cases with rfl | rfl | rfl <;> simp [arcs,heads,List.range'_succ] at hp <;>
      rcases hp with rfl | rfl <;> decide +kernel
  · intro v hv
    have cases : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel
  · intro w hw different
    have cases : w=1 ∨ w=2 := by omega
    rcases cases with rfl | rfl
    · exact ⟨0,by decide +kernel,rfl⟩
    · exact ⟨1,by decide +kernel,rfl⟩
  · refine ⟨id,?_⟩
    intro w hw different
    have cases : w=1 ∨ w=2 := by omega
    rcases cases with rfl | rfl <;> decide +kernel

#guard qrun heads targets parents [0] 3 == [0,1,2]

theorem triangle_not_dp : ¬TS heads targets parents [0,1,2] 3 0 := by
  intro tree
  have classification := tree.cls 1 (by decide +kernel) 3 (by decide +kernel)
  rcases classification with child | back
  · have invalid := child.2
    exact (by decide +kernel : ¬(parents.getD (tgt targets 3) 0 = (1 : Int))) invalid
  · have invalid := back.2
    exact (by decide +kernel : ¬(tgt targets 3 = par parents 1)) invalid

end TreeOrderToDpExamples

namespace TreeOrderToDpPositive
open Proofs.TreeOrderMath Proofs.TreeDpMath Proofs.TreeDpSpec

def heads : List Nat := [0,1,2]
def targets : List Nat := [1,0]
def parents : List Int := [0,0]

theorem input : TO heads targets parents 2 0 := by
  refine ⟨by decide +kernel,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have cases : w=0 ∨ w=1 := by omega
    rcases cases with rfl | rfl <;> decide +kernel
  · intro v hv p hp
    have cases : v=0 ∨ v=1 := by omega
    rcases cases with rfl | rfl <;> simp [arcs,heads,List.range'_succ] at hp <;>
      subst p <;> decide +kernel
  · intro v hv p hp
    have cases : v=0 ∨ v=1 := by omega
    rcases cases with rfl | rfl <;> simp [arcs,heads,List.range'_succ] at hp <;>
      subst p <;> decide +kernel
  · intro v hv
    have cases : v=0 ∨ v=1 := by omega
    rcases cases with rfl | rfl <;> decide +kernel
  · intro w hw nonroot
    have equal : w=1 := by omega
    subst w
    exact ⟨0,by decide +kernel,rfl⟩
  · refine ⟨id,?_⟩
    intro w hw nonroot
    have equal : w=1 := by omega
    subst w
    decide +kernel

theorem classification : ∀ v, v < 2 → ∀ p ∈ arcs heads v,
    (tgt targets p ≠ 0 ∧ parents.getD (tgt targets p) 0 = (v : Int)) ∨
      (v ≠ 0 ∧ tgt targets p = par parents v) := by
  intro v hv p hp
  have cases : v=0 ∨ v=1 := by omega
  rcases cases with rfl | rfl <;> simp [arcs,heads,List.range'_succ] at hp <;> subst p
  · exact Or.inl ⟨by decide +kernel,rfl⟩
  · exact Or.inr ⟨by decide +kernel,rfl⟩

theorem reverse_arc : ∀ v, v < 2 → v ≠ 0 → par parents v ∈ nbs heads targets v := by
  intro v hv nonroot
  have equal : v=1 := by omega
  subst v
  decide +kernel

-- Use exactly the order properties returned by the verified order generator.
example : TS heads targets parents (qrun heads targets parents [0] 2) 2 0 := by
  obtain ⟨length,nd,upper,first,before⟩ := order_spec input
  exact input.toTS _ classification reverse_arc length nd upper first before
end TreeOrderToDpPositive
