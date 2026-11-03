namespace BeatsWideExecExamples
open Proofs.BeatsExec Proofs.CppScalar Proofs.CppNestedProgram Proofs.DoublingNested

-- A scanned unused node whose children exceed INT_MAX. No allocation is performed.
example (env : Nat → Ty → Option Int) (h : env 19 i32 = some 2147483643) :
    (wideChild 19 2).denote env = some 4294967288 ∧
    4294967288 < (4294967296 : Nat) := by
  exact den_wide_child_original_range env 19 536870911 2147483643 2 h
    (by decide) (by decide) (by decide)

-- The constructor's first scanned node and both child offsets.
example (env : Nat → Ty → Option Int) (h : env 19 i32 = some 0) (d : Nat) (hd : d ≤ 2) :
    (wideChild 19 d).denote env = some (d : Int) := by
  simpa using den_wide_child env 19 0 d h (by decide) hd

-- The largest original signed-int size yields a 2^32 allocation count.
-- The vector family remains abstract; the test creates no large vector.
example (mv : Proofs.MultiVec.MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (slot : Nat) (hslot : slot < mv.nv) (hty : mv.ty slot = Proofs.IntSim.s64)
    (length : (vv slot).length = 536870911) :
    Proofs.MultiVec.vdenM mv vv env (wideCount slot) = some 4294967296 := by
  have range : 4*(vv slot).length < Proofs.BellmanFordExec.M31 := by
    rw [length]
    decide
  simpa [length] using vden_wide_count mv vv env slot hslot hty range

end BeatsWideExecExamples

namespace BeatsWideConstructionExamples
open Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsModel Proofs.MultiVec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppState Proofs.IntSim

-- Match the candidate's actual node and stack capacities symbolically.
def initial (n : Nat) : BS :=
  let z := List.replicate (8*n+8) (0 : Int)
  ⟨z,z,z,z,z,z,z,z,List.replicate (8*n+8) INF,z,z,
    List.replicate 256 0,List.replicate 256 0,List.replicate 256 0,z⟩

theorem capacities (n : Nat) : Capacities (initial n) (8*n+8) 256 := by
  constructor <;> simp only [initial, List.length_replicate, Nat.le_refl]

theorem valid (n : Nat) : ValidOK (initial n) := by
  constructor <;> intro w hw <;> simp only [initial, List.mem_replicate] at hw <;>
    rcases hw with ⟨_,rfl⟩ <;> decide

theorem construct_original_range (mv : MV) (hnv : mv.nv = 16)
    (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = Proofs.DoublingNested.i32)
    (hty15 : mv.ty 15 = s64) (P : List Cell) (n : Nat)
    (hn : 1 ≤ n) (range : 4*n < Proofs.BellmanFordExec.M31) :
    ∃ bf Hf, BRepS n (8*n+8) 256 (List.replicate n 0) bf
      (buildBT (List.replicate n 0) 0 n) Hf := by
  have zero : ∀ j, (List.replicate (8*n+8) (0 : Int)).getD j 0 = 0 := by
    intro j
    simp only [List.getD, List.getElem?_replicate]
    split <;> rfl
  have in_range : InRange (List.replicate n 0) := by
    intro w hw
    have : w = 0 := (List.mem_replicate.mp hw).2
    subst w
    decide
  obtain ⟨bf,Hf,_,_,_,_,_,_,_,_,_,rep⟩ :=
    ctor_rep_wide (S := 256) mv hnv hty hty32 hty15 P (List.replicate n 0)
      n (8*n+8) hn (Nat.le_refl _) range (List.length_replicate) in_range
      (by decide) (initial n) (valid n) (capacities n)
      (by simp only [initial, List.length_replicate, Nat.le_refl])
      (by simp only [initial, List.length_replicate, Nat.le_refl])
      zero zero zero zero zero zero zero zero
      (by
        intro j hj
        change j < (List.replicate (8*n+8) INF).length at hj
        rw [List.length_replicate] at hj
        change (List.replicate (8*n+8) INF).getD j 0 = INF
        simp only [List.getD, List.getElem?_replicate_of_lt hj, Option.getD_some])
      zero zero
  exact ⟨bf,Hf,rep⟩

-- A logical boundary witness, without constructing huge data during the test.
example (mv : MV) (hnv : mv.nv = 16)
    (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = Proofs.DoublingNested.i32)
    (hty15 : mv.ty 15 = s64) (P : List Cell) :
    ∃ bf Hf, BRepS 268435456 2147483656 256 (List.replicate 268435456 0) bf
      (buildBT (List.replicate 268435456 0) 0 268435456) Hf :=
  construct_original_range mv hnv hty hty32 hty15 P 268435456 (by decide) (by decide)

end BeatsWideConstructionExamples
