namespace BeatsCapacityExamples
open Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsModel
open Proofs.CppScalar Proofs.MultiVec Proofs.CppState Proofs.ForLoop
open Proofs.DoublingNested (i32)
open Proofs.IntSim (s64)

-- These are the lengths and contents reserved by the C++ constructor.
def initial (n : Nat) : BS :=
  let z := List.replicate (8*n+8) (0 : Int)
  ⟨z,z,z,z,z,z,z,z,List.replicate (8*n+8) INF,z,z,
    List.replicate 256 0,List.replicate 256 0,List.replicate 256 0,z⟩

theorem actual_capacities (n : Nat) : Capacities (initial n) (8*n+8) 256 := by
  constructor <;> simp only [initial, List.length_replicate, Nat.le_refl]

theorem old_condition_excludes_32 : ¬Lens (initial 32) 264 :=
  uniform_not_actual_stack (n := 32) (by decide) (by decide) (by simp only [initial, List.length_replicate])

theorem initial_valid (n : Nat) : ValidOK (initial n) := by
  constructor <;> intro w hw <;> simp only [initial, List.mem_replicate] at hw <;>
    rcases hw with ⟨_,rfl⟩ <;> decide +kernel

-- Obtain the postcondition from actual generated execution, without assuming
-- a successful constructor run or using the impossible old Lens premise.
theorem construct_32 (mv : MV) (hnv : mv.nv = 16)
    (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (hty15 : mv.ty 15 = s64) (P : List Cell) :
    ∃ bf Hf, BRepS 32 264 256 (List.replicate 32 0) bf
      (buildBT (List.replicate 32 0) 0 32) Hf := by
  have zero : ∀ j, (List.replicate 264 (0 : Int)).getD j 0 = 0 := by
    intro j
    simp only [List.getD, List.getElem?_replicate]
    split <;> rfl
  have in_range : InRange (List.replicate 32 0) := by
    intro w hw
    have : w = 0 := (List.mem_replicate.mp hw).2
    subst w
    decide +kernel
  obtain ⟨bf,Hf,_,_,_,_,_,_,_,_,_,rep⟩ :=
    ctor_rep_separate (S := 256) mv hnv hty hty32 hty15 P
      (List.replicate 32 0) 32 264 (by decide) (by decide) (by decide)
      (by exact List.length_replicate) in_range (by decide) (initial 32) (initial_valid 32)
      (actual_capacities 32) (by simp only [initial, List.length_replicate, Nat.le_refl]) (by simp only [initial, List.length_replicate, Nat.le_refl])
      zero zero zero zero zero zero zero zero
      (by
        intro j hj
        change j < (List.replicate 264 INF).length at hj
        rw [List.length_replicate] at hj
        change (List.replicate 264 INF).getD j 0 = INF
        simp only [List.getD, List.getElem?_replicate_of_lt hj, Option.getD_some])
      zero zero
  exact ⟨bf,Hf,rep⟩

-- The new public constructor premise also accepts these actual capacities.
theorem fresh_32 : Proofs.BeatsSeparate.BFreshS 264 256 (initial 32) := by
  have zero : ∀ j, (List.replicate 264 (0 : Int)).getD j 0 = 0 := by
    intro j
    simp only [List.getD, List.getElem?_replicate]
    split <;> rfl
  refine ⟨initial_valid 32, actual_capacities 32, ?_, ?_,
    zero,zero,zero,zero,zero,zero,zero,zero,?_,zero,zero⟩
  · simp only [initial, List.length_replicate, Nat.le_refl]
  · simp only [initial, List.length_replicate, Nat.le_refl]
  · intro j hj
    change j < (List.replicate 264 INF).length at hj
    rw [List.length_replicate] at hj
    change (List.replicate 264 INF).getD j 0 = INF
    simp only [List.getD, List.getElem?_replicate_of_lt hj, Option.getD_some]

-- This is an arithmetic witness; no enormous input vector is allocated.
-- At this power-of-two size the original n0 equals n.
theorem allocation_range_regression :
    i32.valid (4 * (268435456 : Int)) = true ∧
    i32.valid (2 * (268435456 : Int)) = true ∧
    i32.valid (8 * (268435456 : Int) + 8) = false := by
  decide +kernel

end BeatsCapacityExamples
