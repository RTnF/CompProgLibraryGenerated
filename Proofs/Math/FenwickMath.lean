import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
namespace Proofs.FenwickMath

def lowb : Nat → Nat
  | 0 => 0
  | k+1 => if (k+1) % 2 = 1 then 1 else 2 * lowb ((k+1)/2)
termination_by k => k
decreasing_by omega

theorem lowb_odd (k : Nat) (h : k % 2 = 1) : lowb k = 1 := by
  cases k with
  | zero => simp at h
  | succ k => rw [lowb]; simp [h]

theorem lowb_even (k : Nat) (hk : 0 < k) (h : k % 2 = 0) : lowb k = 2 * lowb (k/2) := by
  cases k with
  | zero => omega
  | succ k => rw [lowb]; simp [h]

theorem lowb_pos : ∀ k, 0 < k → 0 < lowb k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : k % 2 = 1
    · rw [lowb_odd k h]; omega
    · rw [lowb_even k hk (by omega)]
      have := ih (k/2) (by omega) (by omega)
      omega

theorem lowb_form : ∀ k, 0 < k → ∃ s c, lowb k = 2^s ∧ k = 2^s * (2*c+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : k % 2 = 1
    · refine ⟨0, k/2, ?_, ?_⟩
      · rw [lowb_odd k h]; simp
      · simp; omega
    · obtain ⟨s, c, h1, h2⟩ := ih (k/2) (by omega) (by omega)
      refine ⟨s+1, c, ?_, ?_⟩
      · rw [lowb_even k hk (by omega), h1, Nat.pow_succ]; omega
      · rw [Nat.pow_succ]
        have : k = 2 * (k/2) := by omega
        rw [this, h2]; ring

theorem lowb_dvd (k : Nat) (hk : 0 < k) : lowb k ∣ k := by
  obtain ⟨s, c, h1, h2⟩ := lowb_form k hk
  rw [h1]; exact ⟨2*c+1, h2⟩

theorem lowb_le (k : Nat) (hk : 0 < k) : lowb k ≤ k := Nat.le_of_dvd hk (lowb_dvd k hk)

theorem lowb_max : ∀ (k s : Nat), 0 < k → 2^s ∣ k → 2^s ≤ lowb k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hk hd
    by_cases h : k % 2 = 1
    · rw [lowb_odd k h]
      cases s with
      | zero => simp
      | succ s =>
        exfalso
        have : 2 ∣ k := Nat.dvd_trans ⟨2^s, by rw [Nat.pow_succ]; ring⟩ hd
        omega
    · rw [lowb_even k hk (by omega)]
      cases s with
      | zero => have := lowb_pos (k/2) (by omega); simp; omega
      | succ s =>
        have hk2 : 2^s ∣ k/2 := by
          obtain ⟨m, hm⟩ := hd
          refine ⟨m, ?_⟩
          rw [Nat.pow_succ] at hm
          have : k = 2 * (2^s * m) := by rw [hm]; ring
          omega
        have := ih (k/2) (by omega) s (by omega) hk2
        rw [Nat.pow_succ]; omega

theorem lowb_next (k : Nat) (hk : 0 < k) : 2 * lowb k ≤ lowb (k + lowb k) := by
  obtain ⟨s, c, h1, h2⟩ := lowb_form k hk
  have hx : 0 < k + lowb k := by omega
  have hd : 2^(s+1) ∣ k + lowb k := by
    refine ⟨c+1, ?_⟩
    rw [h1, Nat.pow_succ]
    have : k = 2^s * (2*c+1) := h2
    rw [this]; ring
  have := lowb_max (k + lowb k) (s+1) hx hd
  rw [h1, Nat.pow_succ] at this
  rw [h1]
  omega

theorem lowb_between (k d : Nat) (hk : 0 < k) (hd : 0 < d) (hdl : d < lowb k) : lowb (k + d) ≤ d := by
  obtain ⟨s, c, h1, h2⟩ := lowb_form k hk
  have hx : 0 < k + d := by omega
  obtain ⟨t, c', h1', h2'⟩ := lowb_form (k + d) hx
  by_contra hcon
  have hdt : d < 2^t := by rw [← h1']; omega
  have dk : 2^s ∣ k := ⟨2*c+1, h2⟩
  have dx : 2^t ∣ k + d := ⟨2*c'+1, h2'⟩
  rcases Nat.lt_or_ge t s with hts | hts
  · have h2t : 2^t ∣ 2^s := Nat.pow_dvd_pow 2 (by omega)
    have h3 : 2^t ∣ k := Nat.dvd_trans h2t dk
    have h4 : 2^t ∣ d := by
      have := Nat.dvd_sub dx h3
      simpa using this
    have := Nat.le_of_dvd hd h4
    omega
  · have h2t : 2^s ∣ 2^t := Nat.pow_dvd_pow 2 hts
    have h3 : 2^s ∣ k + d := Nat.dvd_trans h2t dx
    have h4 : 2^s ∣ d := by
      have := Nat.dvd_sub h3 dk
      simpa using this
    have := Nat.le_of_dvd hd h4
    rw [h1] at hdl
    omega

-- Prefix sums and the Fenwick node sums over a list `A`.

-- tree[k] = sum of A over [k - lowbit k, k)

-- Adding `val` at the 1-based position `k0` and then along `k := k + lowbit k`.

theorem log2_mono (a b : Nat) (ha : 0 < a) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  have hb : b ≠ 0 := by omega
  rw [Nat.le_log2 hb]
  exact Nat.le_trans (Nat.log2_self_le (by omega)) h

-- The number of loop iterations of the update loop (index k, vector length len).
def stepsA (len : Nat) (k : Nat) : Nat :=
  if h : 0 < k ∧ k < len then 1 + stepsA len (k + lowb k) else 0
termination_by len - k
decreasing_by have := lowb_pos k h.1; omega

theorem lowb_clear (r : Nat) (hr : 0 < r) (h : r - lowb r ≠ 0) : 2 * lowb r ≤ lowb (r - lowb r) := by
  obtain ⟨s, c, h1, h2⟩ := lowb_form r hr
  have hx : 0 < r - lowb r := by omega
  have hd : 2^(s+1) ∣ r - lowb r := by
    refine ⟨c, ?_⟩
    rw [h1, Nat.pow_succ]
    have : r = 2^s * (2*c+1) := h2
    have e : r - 2^s = 2^s * (2*c) := by rw [this]; ring_nf; omega
    rw [e]; ring
  have := lowb_max (r - lowb r) (s+1) hx hd
  rw [h1, Nat.pow_succ] at this
  rw [h1]
  omega

theorem log_lowb_clear (r : Nat) (hr : 0 < r) (h : r - lowb r ≠ 0) :
    Nat.log2 (lowb r) + 1 ≤ Nat.log2 (lowb (r - lowb r)) := by
  have hn := lowb_clear r hr h
  have hL := lowb_pos r hr
  have h1 : Nat.log2 (2 * lowb r) = Nat.log2 (lowb r) + 1 := Nat.log2_two_mul (by omega)
  rw [← h1]
  exact log2_mono _ _ (by omega) hn

-- The number of loop iterations of the query loop.
def stepsS : Nat → Nat
  | 0 => 0
  | r+1 => 1 + stepsS (r + 1 - lowb (r+1))
termination_by r => r
decreasing_by have := lowb_pos (r+1) (by omega); omega

theorem stepsS_le : ∀ r, 0 < r → stepsS r + Nat.log2 (lowb r) ≤ Nat.log2 r + 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have hL := lowb_pos r hr
    have hL' := lowb_le r hr
    have hlogk : Nat.log2 (lowb r) ≤ Nat.log2 r := log2_mono _ _ hL hL'
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [stepsS]
    by_cases h : r' + 1 - lowb (r'+1) = 0
    · have : stepsS (r' + 1 - lowb (r'+1)) = 0 := by rw [h]; simp [stepsS]
      omega
    · have hn := log_lowb_clear (r'+1) hr h
      have := ih (r' + 1 - lowb (r'+1)) (by omega) (by omega)
      have hmono : Nat.log2 (r' + 1 - lowb (r'+1)) ≤ Nat.log2 (r'+1) := log2_mono _ _ (by omega) (by omega)
      omega

-- The value of `i & -i` on 32 bit unsigned operands.

end Proofs.FenwickMath