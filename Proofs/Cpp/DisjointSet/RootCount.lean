import Proofs.Cpp.DisjointSet.RootMass

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

def isRootCount (parents : Array Int) (i : Nat) : Nat := if parents[i]! < 0 then 1 else 0

def rootCount (parents : Array Int) : Nat := weightSum (isRootCount parents) parents.size

theorem rootCount_compress {parents after : Array Int} (sameRoots : Comp parents after) :
    rootCount after = rootCount parents := by
  unfold rootCount
  rw [sameRoots.size]
  apply weightSum_equal
  intro i within
  have sameSign : after[i]! < 0 ↔ parents[i]! < 0 := by
    constructor
    · intro sign
      have inside : i < after.size := by rwa [sameRoots.size]
      exact ((sameRoots.root_iff i).mp ⟨inside, sign⟩).2
    · intro sign
      exact ((sameRoots.root_iff i).mpr ⟨within, sign⟩).2
  simp [isRootCount, sameSign]

theorem rootCount_link {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) (first second : Int)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (firstRoot : IsRoot parents first.toNat) (secondRoot : IsRoot parents second.toNat)
    (distinct : first ≠ second) :
    rootCount (UnionFind.link parents first second) + 1 = rootCount parents := by
  have data := link_get parents first second firstNonnegative secondNonnegative firstRoot.1 secondRoot.1 distinct
  have sameSize := (link_forest parents (heightRank parents.size sizeAtLink) certificate.forest
    first second firstNonnegative secondNonnegative firstRoot secondRoot distinct).2
  have equals (i : Nat) : isRootCount (UnionFind.link parents first second) i =
      replaceWeight (isRootCount parents) second.toNat 0 i := by
    unfold isRootCount
    rw [data]
    by_cases atSecond : i = second.toNat
    · have nonnegative : ¬ first < 0 := by omega
      simp [replaceWeight, atSecond, nonnegative]
    · rw [ite_eq_right atSecond]
      by_cases atFirst : i = first.toNat
      · subst i
        have pairNegative : parents[first.toNat]! + parents[second.toNat]! < 0 :=
          by have left := firstRoot.2; have right := secondRoot.2; omega
        simp [replaceWeight, atSecond, firstRoot.2, pairNegative]
      · simp [replaceWeight, atSecond, atFirst]
  unfold rootCount
  rw [sameSize, weightSum_equal (left := isRootCount (UnionFind.link parents first second))
    (right := replaceWeight (isRootCount parents) second.toNat 0) (fun i _ => equals i)]
  have removed := weightSum_replace (weight := isRootCount parents) secondRoot.1 0
  simpa [isRootCount, secondRoot.2] using removed

end Proofs.Cpp.DisjointSet
