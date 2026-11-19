import Proofs.Math.DijkstraOldExec
import Proofs.Math.PrimMath
import Proofs.Math.PrimRelax
import Proofs.Math.PrimStep

namespace Proofs.PrimExec
open Proofs.DijkstraOldExec
open Proofs.BellmanFordMath (Edge)
open Proofs.PrimStep (PInv PInv_step PInv_init degSum degSum_push doneOf_ne doneOf_eq perm_sum_int pk_bounds D_perm_range)
open Proofs.DijkstraMath (Eall mem_Eall mem_Eall_inv)
open Proofs.PrimRelax (relaxL relaxL_length relaxL_getD foldl_length foldl_le foldl_done foldl_cases foldl_cover)

/-! ### The program (nv = 5: `head`, `target`, `cost`, `dist`, `done`; variables 5 = n, 6 = inf, 7 = it, 8 = best, 9 = bd, 10 = v) -/

/-! ### The fallback loop: the first unvisited vertex starts a new component -/

/-! ### One iteration -/

/-! ### A loop lemma with a cost potential -/

/-! ### The final sum -/

/-- `∑_{v < t} dist[v]`. -/
def pS (Dd : List Int) (t : Nat) : Int := ((List.range t).map (fun v => Dd.getD v 0)).sum

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 8000000 in

theorem pS_eq {n : Nat} {inf : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {pk : List Int}
    (I : PInv n inf Ed Dd Dn D pk) (hlen : D.length = n) : pS Dd n = pk.sum := by
  have hperm := D_perm_range I.nodup I.lt hlen
  have e : D.map (fun v => Dd.getD v 0) = pk := by
    apply List.ext_getElem
    · simp [I.len]
    · intro j h1 h2
      have hjD : j < D.length := by simpa using h1
      simp only [List.getElem_map]
      have := I.cl3 j hjD
      rw [this]
      simp [List.getD_eq_getElem?_getD, h2]
  unfold pS
  rw [← e]
  exact (perm_sum_int ((List.Perm.map (fun v => Dd.getD v 0) hperm).symm))

end Proofs.PrimExec
