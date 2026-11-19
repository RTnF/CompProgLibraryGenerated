import Proofs.Math.BellmanFordPExec
import Proofs.Math.BellmanFordExec

namespace Proofs.BellmanFordParent
open Proofs.BellmanFordExec Proofs.BellmanFordPExec

/-- A distance list is stable when no edge from a reached vertex can still relax. -/
def Stable (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D : List Int) : Prop :=
  ∀ e, e < m → D.getD (F.getD e 0) 0 ≠ inf → D.getD (T.getD e 0) 0 ≤ D.getD (F.getD e 0) 0 + Cc.getD e 0

theorem markEdge_id (inf : Int) (F T : List Nat) (Cc : List Int) (m e : Nat) (D P : List Int) (he : e < m)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) (hu : F.getD e 0 < D.length) :
    markEdge inf F T Cc e (D, P) = (D, P) := by
  have h1 : D.getD (F.getD e 0) 0 ≠ -inf := hneg _ (Proofs.BellmanFordExec.getD_mem D _ hu)
  show (if D.getD (F.getD e 0) 0 ≠ inf then markIn inf F T Cc e (D, P) else (D, P)) = (D, P)
  by_cases h0 : D.getD (F.getD e 0) 0 = inf
  · rw [if_neg (fun h => h h0)]
  · have h2 := hst e he h0
    rw [if_pos h0]
    show (if D.getD (F.getD e 0) 0 = -inf then (D.set (T.getD e 0) (-inf), P.set (T.getD e 0) (-1))
      else if D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0 then (D.set (T.getD e 0) (-inf), P.set (T.getD e 0) (-1))
      else (D, P)) = (D, P)
    rw [if_neg h1, if_neg (not_lt.mpr h2)]

theorem markPrefix_id (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D P : List Int)
    (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n) (hDl : D.length = n)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) :
    ∀ t, t ≤ m → markPrefix inf F T Cc t (D, P) = (D, P) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hu : F.getD t 0 < D.length := by
      have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, show t < m by omega]
      rw [this, hDl]; exact hFn _ (List.getElem_mem _)
    rw [markPrefix_succ, ih (by omega)]
    exact markEdge_id inf F T Cc m t D P (by omega) hst hneg hu

theorem markRounds_id (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D P : List Int)
    (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n) (hDl : D.length = n)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) :
    ∀ r, markRounds inf F T Cc m r (D, P) = (D, P) := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [markRounds]
    rw [ih]
    exact markPrefix_id inf F T Cc m n D P hFl hFn hDl hst hneg m (Nat.le_refl _)

end Proofs.BellmanFordParent
