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


theorem land_odd (n j : Nat) (hj : 2*j+1 < 2^(n+1)) : (2*j+1) &&& (2^(n+1) - (2*j+1)) = 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h2 : 2*j < 2^(n+1) := by omega
  have e : 2^(n+1) - (2*j+1) = 2^(n+1) - (2*j+1) := rfl
  rw [Nat.testBit_two_pow_sub_succ h2]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have a1 : (2*j+1)/2 = j := by omega
    have a2 : (2*j)/2 = j := by omega
    rw [a1, a2]
    have : Nat.testBit 1 (i+1) = false := by simp [Nat.testBit_succ]
    rw [this]
    cases h : j.testBit i <;> simp

theorem land_even (n j : Nat) (hj : 2*j < 2^(n+1)) : (2*j) &&& (2^(n+1) - 2*j) = 2 * (j &&& (2^n - j)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have e : 2^(n+1) - 2*j = 2 * (2^n - j) := by rw [Nat.pow_succ]; omega
  rw [e]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have a2 : (2*j)/2 = j := by omega
    have a3 : (2*(2^n - j))/2 = 2^n - j := by omega
    have a4 : (2*(j &&& (2^n - j)))/2 = (j &&& (2^n - j)) := by omega
    rw [a2, a3, a4, Nat.testBit_and]

theorem land_lowb : ∀ (n k : Nat), 0 < k → k < 2^n → k &&& (2^n - k) = lowb k := by
  intro n
  induction n with
  | zero => intro k h1 h2; simp at h2; omega
  | succ n ih =>
    intro k h1 h2
    by_cases hodd : k % 2 = 1
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2*j+1 := ⟨k/2, by omega⟩
      rw [lowb_odd _ hodd]
      exact land_odd n j h2
    · have hev : k % 2 = 0 := by omega
      obtain ⟨j, rfl⟩ : ∃ j, k = 2*j := ⟨k/2, by omega⟩
      rw [land_even n j h2, lowb_even _ h1 hev]
      have hj1 : 0 < j := by omega
      have hj2 : j < 2^n := by rw [Nat.pow_succ] at h2; omega
      have a : (2*j)/2 = j := by omega
      rw [a, ih j hj1 hj2]


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
def pre (A : List Int) (r : Nat) : Int := (A.take r).sum

def seg (A : List Int) (k : Nat) : Int := pre A k - pre A (k - lowb k)

-- tree[k] = sum of A over [k - lowbit k, k)
def FInv (tree A : List Int) : Prop :=
  tree.length = A.length + 1 ∧ ∀ k, 1 ≤ k → k < tree.length → tree[k]? = some (seg A k)

def fsumR (tree : List Int) : Nat → Int
  | 0 => 0
  | r+1 => tree.getD (r+1) 0 + fsumR tree (r + 1 - lowb (r+1))
termination_by r => r
decreasing_by have := lowb_pos (r+1) (by omega); omega

theorem fsumR_correct (tree A : List Int) (h : FInv tree A) : ∀ r, r < tree.length → fsumR tree r = pre A r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    cases r with
    | zero => simp [fsumR, pre]
    | succ r =>
      rw [fsumR]
      have hp := lowb_pos (r+1) (by omega)
      have hk := h.2 (r+1) (by omega) hr
      have hget : tree.getD (r+1) 0 = seg A (r+1) := by
        simp [List.getD_eq_getElem?_getD, hk]
      rw [hget, ih (r + 1 - lowb (r+1)) (by omega) (by omega)]
      simp [seg]


theorem pre_set : ∀ (A : List Int) (i : Nat) (x : Int) (r : Nat) (hi : i < A.length),
    pre (A.set i x) r = pre A r + (if i < r then x - A[i] else 0) := by
  intro A
  induction A with
  | nil => intro i x r hi; simp at hi
  | cons a t ih =>
    intro i x r hi
    cases r with
    | zero => simp [pre]
    | succ r =>
      cases i with
      | zero => simp [pre]; omega
      | succ i =>
        have hi' : i < t.length := by simpa using hi
        have := ih i x r hi'
        simp only [pre] at this ⊢
        simp [List.take_succ_cons, this]
        omega

-- Adding `val` at the 1-based position `k0` and then along `k := k + lowbit k`.
def fadd (val : Int) (tree : List Int) (k0 : Nat) : List Int :=
  if h : 0 < k0 ∧ k0 < tree.length then
    fadd val (tree.set k0 (tree[k0] + val)) (k0 + lowb k0)
  else tree
termination_by tree.length - k0
decreasing_by
  have := lowb_pos k0 h.1
  simp
  omega


theorem fadd_spec (val : Int) (p : Nat) : ∀ (tree : List Int) (k0 : Nat), 0 < k0 → k0 - lowb k0 < p → p ≤ k0 →
    ∀ k, (fadd val tree k0)[k]? =
      (tree[k]?).map (fun t => t + (if k0 ≤ k ∧ k - lowb k < p ∧ p ≤ k then val else 0)) := by
  intro tree k0
  induction tree, k0 using fadd.induct val with
  | case1 tree k0 h ih =>
    intro hk0 hp0 hp1 k
    rw [fadd]
    rw [dif_pos h]
    have hL := lowb_pos k0 hk0
    have hL' := lowb_le k0 hk0
    have hk1 : 0 < k0 + lowb k0 := by omega
    have hn := lowb_next k0 hk0
    have hq0 : k0 + lowb k0 - lowb (k0 + lowb k0) < p := by omega
    have hq1 : p ≤ k0 + lowb k0 := by omega
    rw [ih hk1 hq0 hq1 k]
    by_cases hk : k = k0
    · subst hk
      have hlt : k < tree.length := h.2
      have e1 : (tree.set k (tree[k] + val))[k]? = some (tree[k] + val) := by
        rw [List.getElem?_set_self hlt]
      have e2 : tree[k]? = some tree[k] := by simp [hlt]
      rw [e1, e2]
      have c1 : ¬ (k + lowb k ≤ k) := by omega
      simp [c1, hp0, hp1]
    · rw [List.getElem?_set_ne (Ne.symm hk)]
      have hc : (if k0 + lowb k0 ≤ k ∧ k - lowb k < p ∧ p ≤ k then val else 0) =
          (if k0 ≤ k ∧ k - lowb k < p ∧ p ≤ k then val else 0) := by
        by_cases hlt : k < k0
        · have a1 : ¬ (k0 + lowb k0 ≤ k) := by omega
          have a2 : ¬ (k0 ≤ k) := by omega
          simp [a1, a2]
        · by_cases hge : k0 + lowb k0 ≤ k
          · have a2 : k0 ≤ k := by omega
            simp [hge, a2]
          · have hk0k : k0 < k := by omega
            have hd := lowb_between k0 (k - k0) hk0 (by omega) (by omega)
            have e : k0 + (k - k0) = k := by omega
            rw [e] at hd
            have a3 : ¬ (k - lowb k < p) := by omega
            simp [a3]
      simp only [hc]
  | case2 tree k0 h =>
    intro hk0 hp0 hp1 k
    rw [fadd, dif_neg h]
    by_cases hk : k0 ≤ k
    · have hlen : tree.length ≤ k := by omega
      have : tree[k]? = none := by simp [hlen]
      rw [this]; simp
    · simp [hk]


theorem fadd_length (val : Int) : ∀ (tree : List Int) (k0 : Nat), (fadd val tree k0).length = tree.length := by
  intro tree k0
  induction tree, k0 using fadd.induct val with
  | case1 tree k0 h ih =>
    rw [fadd, dif_pos h, ih]
    simp
  | case2 tree k0 h => rw [fadd, dif_neg h]

theorem fadd_inv (val : Int) (tree A : List Int) (i : Nat) (hi : i < A.length) (h : FInv tree A) :
    FInv (fadd val tree (i+1)) (A.set i (A[i] + val)) := by
  have hlen := fadd_length val tree (i+1)
  refine ⟨by rw [hlen, h.1]; simp, ?_⟩
  intro k hk1 hk
  rw [hlen] at hk
  have hLi := lowb_pos (i+1) (by omega)
  have hLi' := lowb_le (i+1) (by omega)
  have hspec := fadd_spec val (i+1) tree (i+1) (by omega) (by omega) (le_refl _) k
  have hget := h.2 k hk1 hk
  rw [hget] at hspec
  rw [hspec]
  have hL := lowb_pos k hk1
  have hL' := lowb_le k hk1
  have e1 := pre_set A i (A[i]+val) k hi
  have e2 := pre_set A i (A[i]+val) (k - lowb k) hi
  simp only [Option.map_some]
  congr 1
  simp only [seg]
  rw [e1, e2]
  by_cases a : i < k - lowb k
  · have b : i < k := by omega
    have c1 : ¬ (k - lowb k < i + 1) := by omega
    simp [a, b, c1]
  · by_cases b : i < k
    · have c1 : k - lowb k < i + 1 := by omega
      have c2 : i + 1 ≤ k := by omega
      simp [a, b, c1, c2]
      ring
    · have c2 : ¬ (i + 1 ≤ k) := by omega
      simp [a, b, c2]


theorem log2_mono (a b : Nat) (ha : 0 < a) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  have hb : b ≠ 0 := by omega
  rw [Nat.le_log2 hb]
  exact Nat.le_trans (Nat.log2_self_le (by omega)) h

theorem log_lowb_next (k : Nat) (hk : 0 < k) : Nat.log2 (lowb k) + 1 ≤ Nat.log2 (lowb (k + lowb k)) := by
  have hn := lowb_next k hk
  have hL := lowb_pos k hk
  have h1 : Nat.log2 (2 * lowb k) = Nat.log2 (lowb k) + 1 := Nat.log2_two_mul (by omega)
  rw [← h1]
  exact log2_mono _ _ (by omega) hn

-- The number of loop iterations of the update loop (index k, vector length len).
def stepsA (len : Nat) (k : Nat) : Nat :=
  if h : 0 < k ∧ k < len then 1 + stepsA len (k + lowb k) else 0
termination_by len - k
decreasing_by have := lowb_pos k h.1; omega

theorem stepsA_le (len : Nat) : ∀ (m k : Nat), len - k = m → 0 < k → k < len →
    stepsA len k + Nat.log2 (lowb k) ≤ Nat.log2 len + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm hk hlt
    have hL := lowb_pos k hk
    have hL' := lowb_le k hk
    have hnext := log_lowb_next k hk
    have hlogk : Nat.log2 (lowb k) ≤ Nat.log2 len := log2_mono _ _ hL (by omega)
    rw [stepsA, dif_pos ⟨hk, hlt⟩]
    by_cases h1 : k + lowb k < len
    · have := ih (len - (k + lowb k)) (by omega) (k + lowb k) rfl (by omega) h1
      omega
    · have : stepsA len (k + lowb k) = 0 := by
        rw [stepsA, dif_neg (by omega)]
      omega


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
theorem lowbit_eval (k : Nat) (hk : 0 < k) (hk2 : k < 2^31) : k &&& (2^32 - k) = lowb k :=
  land_lowb 32 k hk (by omega)

end Proofs.FenwickMath