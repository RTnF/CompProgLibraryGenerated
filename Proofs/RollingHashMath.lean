import Proofs.RollingHashBuild
import Proofs.Mod61Call

namespace Proofs.RollingHashMath
open Proofs.Mod61Body (M61)
open Proofs.Mul61Body (retOf)
open Proofs.RollingHashBuild (HF PF HF_lt PF_lt)

theorem M61_val : M61 = 2305843009213693951 := rfl

/-- The polynomial hash of a list: `h ← (h * b + x) mod (2^61 - 1)` from left to right, starting at 0. -/
def stepH (b h x : Nat) : Nat := (h * b + x) % M61
def polyHash (b : Nat) (S : List Nat) : Nat := S.foldl (stepH b) 0

theorem fold_cg (b : Nat) (T : List Nat) :
    ∀ h, T.foldl (stepH b) h % M61 = (h * b ^ T.length + T.foldl (stepH b) 0) % M61 := by
  induction T with
  | nil => intro h; simp
  | cons x T ih =>
    intro h
    have i1 := ih (stepH b h x)
    have i2 := ih (stepH b 0 x)
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    simp only [stepH] at i1 i2 ⊢
    have e1 : ((h * b + x) % M61 * b ^ T.length) % M61 = ((h * b + x) * b ^ T.length) % M61 := Nat.mod_mul_mod _ _ _
    have e2 : ((0 * b + x) % M61 * b ^ T.length) % M61 = ((0 * b + x) * b ^ T.length) % M61 := Nat.mod_mul_mod _ _ _
    have e3 : (h * b + x) * b ^ T.length = h * b * b ^ T.length + x * b ^ T.length := Nat.add_mul _ _ _
    have e4 : (0 * b + x) * b ^ T.length = x * b ^ T.length := by simp
    have e5 : h * (b ^ T.length * b) = h * b * b ^ T.length := by
      rw [Nat.mul_comm (b ^ T.length) b, ← Nat.mul_assoc]
    rw [e5]
    rw [e3] at e1
    rw [e4] at e2
    unfold M61 at *
    omega

theorem polyHash_lt (b : Nat) (S : List Nat) : polyHash b S < M61 := by
  unfold polyHash
  have : ∀ (T : List Nat) (h : Nat), h < M61 → T.foldl (stepH b) h < M61 := by
    intro T
    induction T with
    | nil => intro h hh; simpa using hh
    | cons x T ih =>
      intro h hh
      simp only [List.foldl_cons]
      exact ih _ (Nat.mod_lt _ (by unfold M61; omega))
  exact this S 0 (by unfold M61; omega)

theorem HF_eq (b : Nat) (S : List Nat) (hb : b < 2^61) :
    ∀ t, t ≤ S.length → HF b S t = polyHash b (S.take t) := by
  intro t
  induction t with
  | zero => intro _; simp [HF, polyHash]
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hS : (S.take (t + 1)) = S.take t ++ [S[t]'(by omega)] := by
      rw [List.take_succ]; simp [List.getElem?_eq_getElem (show t < S.length by omega)]
    have hp : polyHash b (S.take (t + 1)) = stepH b (polyHash b (S.take t)) (S[t]'(by omega)) := by
      rw [hS]; unfold polyHash; rw [List.foldl_append]; rfl
    rw [hp, ← ih']
    show (retOf (HF b S t) b + S.getD t 0) % M61 = (HF b S t * b + S[t]'(by omega)) % M61
    have hget : S.getD t 0 = S[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, show t < S.length by omega]
    rw [hget]
    have m := (Proofs.Mod61Call.mul61_spec (HF b S t) b (HF_lt b S t) hb).2
    unfold M61 at *
    omega

theorem PF_eq (b : Nat) (hb : b < 2^61) : ∀ t, PF b t = b ^ t % M61 := by
  intro t
  induction t with
  | zero => simp [PF, M61]
  | succ t ih =>
    show retOf (PF b t) b % M61 = b ^ (t + 1) % M61
    have m := (Proofs.Mod61Call.mul61_spec (PF b t) b (PF_lt b t) hb).2
    rw [m, ih, pow_succ]
    exact Nat.mod_mul_mod _ _ _

/-- The hash of `S[l, r)` computed from the two lists: `(H r + 4 * M - retOf (H l) (P (r - l))) mod M`. -/
theorem sub_hash (b : Nat) (S : List Nat) (hb : b < 2^61) (l r : Nat) (hl : l ≤ r) (hr : r ≤ S.length) :
    (HF b S r + 4 * M61 - retOf (HF b S l) (PF b (r - l))) % M61 = polyHash b ((S.drop l).take (r - l)) := by
  have hr' := HF_eq b S hb r hr
  have hl' := HF_eq b S hb l (by omega)
  have htake : S.take r = S.take l ++ (S.drop l).take (r - l) := by
    have := @List.take_add _ S l (r - l)
    rw [show l + (r - l) = r by omega] at this
    exact this
  have hlen : ((S.drop l).take (r - l)).length = r - l := by simp; omega
  have f := fold_cg b ((S.drop l).take (r - l)) (polyHash b (S.take l))
  rw [hlen] at f
  have hpoly : polyHash b (S.take r) = ((S.drop l).take (r - l)).foldl (stepH b) (HF b S l) := by
    rw [hl', htake]; unfold polyHash; rw [List.foldl_append]
  rw [← hl'] at f
  have m := (Proofs.Mod61Call.mul61_spec (HF b S l) (PF b (r - l)) (HF_lt b S l) (PF_lt b (r - l))).2
  have hX := Proofs.RollingHashCore.retOf_small (HF b S l) (PF b (r - l)) (HF_lt b S l) (PF_lt b (r - l))
  have hP : (HF b S l * (b ^ (r - l) % M61)) % M61 = (HF b S l * b ^ (r - l)) % M61 := Nat.mul_mod_mod _ _ _
  rw [PF_eq b hb (r - l)] at m hX ⊢
  have hG := polyHash_lt b ((S.drop l).take (r - l))
  have hF : HF b S r % M61 = (HF b S l * b ^ (r - l) + polyHash b ((S.drop l).take (r - l))) % M61 := by
    rw [hr', hpoly]; exact f
  unfold M61 at *
  omega

end Proofs.RollingHashMath
