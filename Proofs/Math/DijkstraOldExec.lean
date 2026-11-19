import Proofs.Math.EnumerateQuotientsMath
import Proofs.Math.FenwickMath
import Proofs.Math.FenwickBuildMath
import Proofs.Math.DijkstraMath
import Proofs.Math.BellmanFordExec
import Proofs.Math.TopoSortMath

namespace Proofs.DijkstraOldExec

open Proofs.BellmanFordMath (Edge relax foldl_le)
open Proofs.DijkstraMath (relax_fold_cases relaxOut)

/-- The out-edges of vertex `b` in CSR order. -/
def outEdges (H T : List Nat) (C : List Int) (b : Nat) : List Edge :=
  (List.range (H.getD (b + 1) 0 - H.getD b 0)).map (fun d => (b, T.getD (H.getD b 0 + d) 0, C.getD (H.getD b 0 + d) 0))

theorem outEdges_length (H T : List Nat) (C : List Int) (b : Nat) :
    (outEdges H T C b).length = H.getD (b + 1) 0 - H.getD b 0 := by simp [outEdges]

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 8000000 in

/-- The `done` vector for the set `D` of finalized vertices. -/
def doneOf (n : Nat) (D : List Nat) : List Nat := (List.range n).map (fun v => if v ∈ D then 1 else 0)

theorem doneOf_getD (n : Nat) (D : List Nat) (v : Nat) (hv : v < n) : (doneOf n D).getD v 0 = if v ∈ D then 1 else 0 := by
  simp [doneOf, List.getD_eq_getElem?_getD, hv]

theorem doneOf_push (n : Nat) (D : List Nat) (b : Nat) (hb : b < n) : (doneOf n D).set b 1 = doneOf n (D ++ [b]) := by
  apply List.ext_getElem
  · simp [doneOf]
  · intro j h1 h2
    have hj : j < n := by simpa [doneOf] using h1
    rw [List.getElem_set]
    simp only [doneOf, List.getElem_map, List.getElem_range]
    by_cases h : b = j
    · subst h; simp
    · simp [h, Ne.symm h]

open Proofs.DijkstraMath (scanStep scanRes)

open Proofs.DijkstraMath (djStep scan_inv PickInv)

open Proofs.DijkstraMath (djIter djIter_succ)

end Proofs.DijkstraOldExec
