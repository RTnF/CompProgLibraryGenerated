import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace Proofs.InvGcdMath

/-- The invariant of the loop of `inv_gcd` for the modulus `b` and the normalized `a` (`0 ≤ a < b`). -/
structure Inv (b a s t : Nat) (m0 m1 : Int) : Prop where
  h1 : (b : Int) ∣ (s : Int) - m0 * (a : Int)
  h2 : (b : Int) ∣ (t : Int) - m1 * (a : Int)
  h3 : s * m1.natAbs + t * m0.natAbs ≤ b
  h4 : s * m0.natAbs < b
  h5 : t < s
  h6 : Nat.gcd s t = Nat.gcd b a
  h7 : s ≤ b

theorem inv_init (b a : Nat) (hb : 0 < b) (ha : a < b) : Inv b a b a 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ha, rfl, Nat.le_refl _⟩
  · simp
  · simp
  · simp
  · simp; exact hb

theorem natAbs_step (m0 m1 : Int) (u : Nat) : (m0 - m1 * (u : Int)).natAbs ≤ m0.natAbs + m1.natAbs * u := by
  have h := Int.natAbs_sub_le m0 (m1 * (u : Int))
  rw [Int.natAbs_mul, Int.natAbs_natCast] at h
  exact h

/-- One iteration keeps the invariant. -/
theorem inv_step (b a s t : Nat) (m0 m1 : Int) (hb : 0 < b) (I : Inv b a s t m0 m1) (ht : t ≠ 0) :
    Inv b a t (s % t) m1 (m0 - m1 * ((s / t : Nat) : Int)) := by
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  have hdm : s = t * (s / t) + s % t := (Nat.div_add_mod s t).symm
  have hmod : s % t < t := Nat.mod_lt _ htpos
  have hu : (s : Int) = (t : Int) * ((s / t : Nat) : Int) + ((s % t : Nat) : Int) := by exact_mod_cast hdm
  refine ⟨I.h2, ?_, ?_, ?_, hmod, ?_, by have := I.h7; have := I.h5; omega⟩
  · have e : ((s % t : Nat) : Int) - (m0 - m1 * ((s / t : Nat) : Int)) * (a : Int) =
        ((s : Int) - m0 * (a : Int)) - ((s / t : Nat) : Int) * ((t : Int) - m1 * (a : Int)) := by
      have : ((s % t : Nat) : Int) = (s : Int) - (t : Int) * ((s / t : Nat) : Int) := by
        generalize s / t = q at *
        generalize s % t = r at *
        omega
      rw [this]; ring
    rw [e]
    exact Int.dvd_sub I.h1 (Dvd.dvd.mul_left I.h2 _)
  · -- t |m0 - m1 u| + (s % t) |m1| ≤ t |m0| + s |m1| ≤ b
    have hab := natAbs_step m0 m1 (s / t)
    have hm := Nat.mul_le_mul_left t hab
    have e : t * (m0.natAbs + m1.natAbs * (s / t)) + s % t * m1.natAbs = t * m0.natAbs + s * m1.natAbs := by
      have : s * m1.natAbs = (t * (s / t) + s % t) * m1.natAbs := by rw [← hdm]
      rw [this]; ring
    have := I.h3
    omega
  · -- t |m1| < b
    have h3 := I.h3
    by_cases h : m1.natAbs = 0
    · rw [h]; simpa using hb
    · have hp : 0 < m1.natAbs := Nat.pos_of_ne_zero h
      have : t * m1.natAbs < s * m1.natAbs := Nat.mul_lt_mul_of_pos_right I.h5 hp
      omega
  · rw [← I.h6]
    exact ((Nat.gcd_comm s t).trans ((Nat.gcd_rec t s).trans (Nat.gcd_comm _ _))).symm

/-- The bounds that keep every intermediate value of an iteration inside `b`. -/
theorem inv_bounds (b a s t : Nat) (m0 m1 : Int) (hb : 0 < b) (I : Inv b a s t m0 m1) (ht : t ≠ 0) :
    m0.natAbs ≤ b ∧ m1.natAbs ≤ b ∧ (m1 * ((s / t : Nat) : Int)).natAbs ≤ b ∧
    (m0 - m1 * ((s / t : Nat) : Int)).natAbs ≤ b := by
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  have hs1 : 1 ≤ s := by have := I.h5; omega
  have h3 := I.h3
  have h4 := I.h4
  have e1 : m1.natAbs ≤ s * m1.natAbs := Nat.le_mul_of_pos_left _ hs1
  have e0 : m0.natAbs ≤ s * m0.natAbs := Nat.le_mul_of_pos_left _ hs1
  have hu : s / t ≤ s := Nat.div_le_self s t
  have e2 : m1.natAbs * (s / t) ≤ m1.natAbs * s := Nat.mul_le_mul_left _ hu
  have e3 : m1.natAbs * s = s * m1.natAbs := Nat.mul_comm _ _
  have I' := inv_step b a s t m0 m1 hb I ht
  have h3' := I'.h3
  have e4 : (m0 - m1 * ((s / t : Nat) : Int)).natAbs ≤ t * (m0 - m1 * ((s / t : Nat) : Int)).natAbs :=
    Nat.le_mul_of_pos_left _ htpos
  refine ⟨by omega, by omega, ?_, by omega⟩
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  omega

/-- What the loop leaves when it stops (`t = 0`). -/
theorem inv_final (b a s : Nat) (m0 m1 : Int) (hb : 0 < b) (I : Inv b a s 0 m0 m1) :
    s = Nat.gcd b a ∧ s ∣ b ∧ 0 < s ∧ m0.natAbs < b / s ∧ (b : Int) ∣ (s : Int) - m0 * (a : Int) := by
  have hg : s = Nat.gcd b a := by rw [← I.h6]; simp
  have hs : 0 < s := by have := I.h5; omega
  have hsb : s ∣ b := by rw [hg]; exact Nat.gcd_dvd_left b a
  obtain ⟨k, hk⟩ := hsb
  have hkd : b / s = k := by rw [hk]; exact Nat.mul_div_cancel_left k hs
  have h4 := I.h4
  rw [hk] at h4
  have hlt : m0.natAbs < k := Nat.lt_of_mul_lt_mul_left h4
  exact ⟨hg, ⟨k, hk⟩, hs, by rw [hkd]; exact hlt, I.h1⟩

/-- The value returned in `out[1]`. -/
theorem inv_out (b a s : Nat) (m0 : Int) (m1 : Int) (hb : 0 < b) (I : Inv b a s 0 m0 m1) :
    let x := if m0 < 0 then m0 + ((b / s : Nat) : Int) else m0
    0 ≤ x ∧ x < ((b / s : Nat) : Int) ∧ (b : Int) ∣ x * (a : Int) - (s : Int) := by
  obtain ⟨hg, hsb, hs, hlt, hd⟩ := inv_final b a s m0 m1 hb I
  intro x
  have hlt' : m0.natAbs < b / s := hlt
  have hsa : s ∣ a := by rw [hg]; exact Nat.gcd_dvd_right b a
  obtain ⟨c, hc⟩ := hsa
  obtain ⟨k, hk⟩ := hsb
  have hkd : b / s = k := by rw [hk]; exact Nat.mul_div_cancel_left k hs
  rw [hkd] at hlt' ⊢
  by_cases hneg : m0 < 0
  · have hx : x = m0 + (k : Int) := by
      show (if m0 < 0 then m0 + ((b / s : Nat) : Int) else m0) = _
      rw [if_pos hneg, hkd]
    rw [hx]
    refine ⟨by omega, by omega, ?_⟩
    have e : (m0 + (k : Int)) * (a : Int) - (s : Int) = (m0 * (a : Int) - (s : Int)) + (b : Int) * (c : Int) := by
      have hb' : (b : Int) = (s : Int) * (k : Int) := by exact_mod_cast hk
      have ha' : (a : Int) = (s : Int) * (c : Int) := by exact_mod_cast hc
      rw [hb']
      have : (k : Int) * (a : Int) = (s : Int) * (k : Int) * (c : Int) := by rw [ha']; ring
      calc (m0 + (k : Int)) * (a : Int) - (s : Int) = (m0 * (a : Int) - (s : Int)) + (k : Int) * (a : Int) := by ring
        _ = _ := by rw [this]
    rw [e]
    have h1 : (b : Int) ∣ m0 * (a : Int) - (s : Int) := by
      have := Int.dvd_neg.mpr hd
      have e2 : -((s : Int) - m0 * (a : Int)) = m0 * (a : Int) - (s : Int) := by ring
      rwa [e2] at this
    exact Int.dvd_add h1 (Int.dvd_mul_right _ _)
  · have hx : x = m0 := by
      show (if m0 < 0 then m0 + ((b / s : Nat) : Int) else m0) = _
      rw [if_neg hneg]
    rw [hx]
    refine ⟨by omega, by omega, ?_⟩
    have := Int.dvd_neg.mpr hd
    have e2 : -((s : Int) - m0 * (a : Int)) = m0 * (a : Int) - (s : Int) := by ring
    rwa [e2] at this

end Proofs.InvGcdMath
