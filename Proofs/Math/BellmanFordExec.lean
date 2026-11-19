import Proofs.Math.EnumerateQuotientsMath
import Proofs.Math.FenwickMath
import Proofs.Math.FenwickBuildMath
import Proofs.Math.BellmanFordMath

namespace Proofs.BellmanFordExec

/-- The relaxation of edge `e` on the distance list `D`. -/
def relaxL (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) : List Int :=
  if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  then D.set (T.getD e 0) (D.getD (F.getD e 0) 0 + Cc.getD e 0) else D

/-! ### The program (variable `nv + c` is the scalar cell `c`: 0 = n, 1 = inf, 2 = m, 3 = rounds, 4 = i, 5 = e, 6 = u, 7 = v, 8 = nd) -/

theorem getD_mem (D : List Int) (j : Nat) (h : j < D.length) : D.getD j 0 ∈ D := by
  have : D.getD j 0 = D[j] := by simp [List.getD_eq_getElem?_getD, h]
  rw [this]; exact List.getElem_mem _

/-- The distance list after relaxing the edges `0 .. t-1` in order. -/
def passPrefix (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 : List Int) : List Int :=
  (List.range t).foldl (fun d e => relaxL inf F T Cc e d) D0

theorem passPrefix_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 : List Int) :
    passPrefix inf F T Cc (t + 1) D0 = relaxL inf F T Cc t (passPrefix inf F T Cc t D0) := by
  unfold passPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem relaxL_length (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) :
    (relaxL inf F T Cc e D).length = D.length := by
  unfold relaxL
  split <;> simp

theorem passPrefix_length (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) :
    ∀ t, (passPrefix inf F T Cc t D0).length = D0.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [passPrefix_succ, relaxL_length, ih]

/-- One full pass over all `m` edges. -/
def passL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D : List Int) : List Int := passPrefix inf F T Cc m D

/-- `r` full passes. -/
def roundsL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int → List Int
  | 0, D => D
  | r + 1, D => passL inf F T Cc m (roundsL inf F T Cc m r D)

theorem roundsL_length (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D0 : List Int) :
    ∀ r, (roundsL inf F T Cc m r D0).length = D0.length := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [roundsL, passL]; rw [passPrefix_length, ih]

end Proofs.BellmanFordExec
