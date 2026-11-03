import Proofs.FenwickMath

namespace Proofs.FenwickBuildMath
open Proofs.FenwickMath

-- The smallest power of two strictly above `d`.
def spow : Nat → Nat
  | 0 => 1
  | d+1 => 2 * spow ((d+1)/2)
termination_by d => d
decreasing_by omega

theorem spow_form : ∀ d, ∃ m, spow d = 2^m := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => exact ⟨0, by simp [spow]⟩
    | succ d =>
      obtain ⟨m, hm⟩ := ih ((d+1)/2) (by omega)
      refine ⟨m+1, ?_⟩
      rw [spow, hm, Nat.pow_succ]; omega

theorem spow_gt : ∀ d, d < spow d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => simp [spow]
    | succ d =>
      have := ih ((d+1)/2) (by omega)
      rw [spow]; omega

-- Minimality: every power of two above `d` is at least `spow d`.
theorem spow_min : ∀ (d m : Nat), d < 2^m → spow d ≤ 2^m := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m hm
    cases d with
    | zero => simp [spow]; exact Nat.one_le_two_pow
    | succ d =>
      cases m with
      | zero => simp at hm
      | succ m =>
        have h1 : (d+1)/2 < 2^m := by rw [Nat.pow_succ] at hm; omega
        have := ih ((d+1)/2) (by omega) m h1
        rw [spow, Nat.pow_succ]; omega

theorem spow_pow (i : Nat) : spow (2^i) = 2^(i+1) := by
  obtain ⟨m, hm⟩ := spow_form (2^i)
  have h1 := spow_gt (2^i)
  have h2 := spow_min (2^i) (i+1) (by rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := i); omega)
  rw [hm] at h1 h2 ⊢
  have : i < m := by
    by_contra h
    have : 2^m ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have : m ≤ i + 1 := by
    by_contra h
    have : 2^(i+1) < 2^m := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have : m = i + 1 := by omega
  rw [this]

theorem spow_pred_pow (i : Nat) : spow (2^i - 1) = 2^i := by
  have hp : 0 < 2^i := Nat.two_pow_pos i
  obtain ⟨m, hm⟩ := spow_form (2^i - 1)
  have h1 := spow_gt (2^i - 1)
  have h2 := spow_min (2^i - 1) i (by omega)
  rw [hm] at h1 h2 ⊢
  have : i ≤ m := by
    by_contra h
    have : 2^m < 2^i := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have : m = i := by
    by_contra h
    have : 2^i < 2^m := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  rw [this]

-- Either `spow` does not change from `d - 1` to `d`, or `d` is a power of two.
theorem spow_step (d : Nat) (hd : 1 ≤ d) : spow (d - 1) = spow d ∨ ∃ i, d = 2^i := by
  by_cases h : spow (d - 1) = spow d
  · exact Or.inl h
  · right
    obtain ⟨a, ha⟩ := spow_form (d - 1)
    have h1 := spow_gt (d - 1)
    -- d ≤ 2^a
    have hda : d ≤ 2^a := by rw [ha] at h1; omega
    by_cases heq : d = 2^a
    · exact ⟨a, heq⟩
    · have hlt : d < 2^a := by omega
      have := spow_min d a hlt
      have h2 : spow (d - 1) ≤ spow d := by
        obtain ⟨b, hb⟩ := spow_form d
        have hg := spow_gt d
        have := spow_min (d - 1) b (by rw [hb] at hg; omega)
        rw [hb]; exact this
      exfalso
      apply h
      -- spow d ≤ 2^a = spow (d-1) and spow (d-1) ≤ spow d
      have h3 : spow d ≤ spow (d - 1) := by rw [ha]; exact this
      omega


-- lowb of 2^i times an odd number.
theorem lowb_pow_odd (i c : Nat) : lowb (2^i * (2*c+1)) = 2^i := by
  have hk : 0 < 2^i * (2*c+1) := Nat.mul_pos (Nat.two_pow_pos i) (by omega)
  obtain ⟨s', c', h1, h2⟩ := lowb_form _ hk
  have hle : 2^i ≤ lowb (2^i * (2*c+1)) := lowb_max _ i hk ⟨2*c+1, rfl⟩
  rw [h1] at hle ⊢
  have hi : i ≤ s' := by
    by_contra h
    have : 2^s' < 2^i := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  by_cases heq : s' = i
  · rw [heq]
  · exfalso
    have hs : i < s' := by omega
    -- 2^(i+1) divides 2^s' * (2c'+1) = 2^i * (2c+1)
    have h3 : 2^(i+1) ∣ 2^i * (2*c+1) := by
      rw [h2]
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) ⟨2*c'+1, rfl⟩
    rw [Nat.pow_succ] at h3
    have h4 : 2 ∣ 2*c+1 := by
      obtain ⟨m, hm⟩ := h3
      refine ⟨m, ?_⟩
      have hp : 0 < 2^i := Nat.two_pow_pos i
      have : 2^i * (2*c+1) = 2^i * (2*m) := by rw [hm]; ring
      exact Nat.eq_of_mul_eq_mul_left hp this
    omega

-- Clearing the low bits of a node: lowb (t - 2^i) = 2^i for i below the exponent of lowb t.
theorem lowb_sub_pow (t s i : Nat) (ht : 0 < t) (hs : lowb t = 2^s) (hi : i < s) : lowb (t - 2^i) = 2^i := by
  obtain ⟨s', c, h1, h2⟩ := lowb_form t ht
  have hss : s' = s := by
    have : (2:Nat)^s' = 2^s := by rw [← h1, hs]
    exact Nat.pow_right_injective (le_refl 2) this
  subst hss
  -- t - 2^i = 2^i * (2^(s'-i) * (2c+1) - 1) with an odd cofactor
  obtain ⟨u, hu⟩ : ∃ u, s' = i + u + 1 := ⟨s' - i - 1, by omega⟩
  have hp : 0 < 2^u * (2*c+1) := Nat.mul_pos (Nat.two_pow_pos u) (by omega)
  obtain ⟨w, hw⟩ : ∃ w, 2 * (2^u * (2*c+1)) - 1 = 2*w+1 := ⟨2^u * (2*c+1) - 1, by omega⟩
  have : t - 2^i = 2^i * (2*w+1) := by
    rw [h2, hu]
    have e1 : 2^(i+u+1) * (2*c+1) = 2^i * (2 * (2^u * (2*c+1))) := by
      rw [Nat.pow_succ, Nat.pow_add]; ring
    rw [e1, ← hw]
    have : 1 ≤ 2 * (2^u * (2*c+1)) := by omega
    rw [Nat.mul_sub, Nat.mul_one]
  rw [this]
  exact lowb_pow_odd i w


theorem pre_succ : ∀ (A : List Int) (k : Nat), k < A.length → pre A (k+1) = pre A k + A.getD k 0 := by
  intro A
  induction A with
  | nil => intro k hk; simp at hk
  | cons a t ih =>
    intro k hk
    cases k with
    | zero => simp [pre]
    | succ k =>
      have hk' : k < t.length := by simpa using hk
      have := ih k hk'
      simp only [pre] at this ⊢
      simp [List.take_succ_cons, this]
      omega

-- The part of the node `t` that is already covered once the nodes below `k` have been pushed up.
def Wc (t k : Nat) : Nat := t - min (lowb t) (spow (t - k))

def bstep (tree : List Int) (k : Nat) : List Int :=
  if k + lowb k < tree.length then tree.set (k + lowb k) (tree.getD (k + lowb k) 0 + tree.getD k 0) else tree

def BInv (A : List Int) (k : Nat) (tree : List Int) : Prop :=
  tree.length = A.length + 1 ∧ ∀ t, 1 ≤ t → t < tree.length →
    tree[t]? = some (if t < k then seg A t else A.getD (t-1) 0 + pre A (Wc t k) - pre A (t - lowb t))

theorem Wc_one (t : Nat) (ht : 1 ≤ t) : Wc t 1 = t - lowb t := by
  unfold Wc
  have h1 := spow_gt (t - 1)
  have h2 := lowb_le t ht
  have : min (lowb t) (spow (t - 1)) = lowb t := by omega
  rw [this]

theorem binv_init (A tree : List Int) (hl : tree.length = A.length + 1)
    (h0 : ∀ t, 1 ≤ t → t < tree.length → tree[t]? = some (A.getD (t-1) 0)) : BInv A 1 tree := by
  refine ⟨hl, ?_⟩
  intro t h1 h2
  rw [h0 t h1 h2, if_neg (by omega), Wc_one t h1]
  congr 1
  omega

theorem binv_final (A tree : List Int) (h : BInv A tree.length tree) : FInv tree A := by
  refine ⟨h.1, ?_⟩
  intro t h1 h2
  rw [h.2 t h1 h2, if_pos h2]

theorem Wc_self (k : Nat) (hk : 1 ≤ k) : Wc k k = k - 1 := by
  unfold Wc
  have := lowb_pos k hk
  simp [spow]
  omega

theorem Wc_same (t k : Nat) (hk : 1 ≤ k) (hkt : k < t) (hne : t ≠ k + lowb k) : Wc t (k+1) = Wc t k := by
  unfold Wc
  have hd : 1 ≤ t - k := by omega
  have e1 : t - (k+1) = (t - k) - 1 := by omega
  rw [e1]
  rcases spow_step (t - k) hd with h | ⟨i, hi⟩
  · rw [h]
  · rw [hi, spow_pred_pow, spow_pow]
    obtain ⟨s, c, hs, _⟩ := lowb_form t (by omega)
    by_cases hlt : i < s
    · exfalso
      have hk' : lowb (t - 2^i) = 2^i := lowb_sub_pow t s i (by omega) hs hlt
      have : t - 2^i = k := by omega
      rw [this] at hk'
      apply hne
      omega
    · have : 2^s ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hs]
      have h2 : 2^i ≤ 2^(i+1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

theorem Wc_at_j (k : Nat) (hk : 1 ≤ k) :
    Wc (k + lowb k) k = k - lowb k ∧ Wc (k + lowb k) (k+1) = k := by
  obtain ⟨e, c, he, hke⟩ := lowb_form k hk
  have hn := lowb_next k hk
  have hj : (k + lowb k) - k = 2^e := by rw [he]; omega
  have hj1 : (k + lowb k) - (k+1) = 2^e - 1 := by rw [he]; omega
  have hp : 0 < 2^e := Nat.two_pow_pos e
  constructor
  · unfold Wc
    rw [hj, spow_pow]
    have : min (lowb (k + lowb k)) (2^(e+1)) = 2^(e+1) := by
      rw [he] at hn ⊢
      have : 2^(e+1) = 2 * 2^e := by rw [Nat.pow_succ]; omega
      omega
    rw [this]
    rw [he, Nat.pow_succ]
    omega
  · unfold Wc
    rw [hj1, spow_pred_pow]
    have : min (lowb (k + lowb k)) (2^e) = 2^e := by
      rw [he] at hn ⊢
      omega
    rw [this, he]
    omega


theorem binv_step (A tree : List Int) (k : Nat) (h : BInv A k tree) (hk : 1 ≤ k) (hkn : k < tree.length) :
    BInv A (k+1) (bstep tree k) := by
  have hL := lowb_pos k hk
  have hlen : (bstep tree k).length = A.length + 1 := by
    unfold bstep; split <;> simp [h.1]
  refine ⟨hlen, ?_⟩
  intro t ht1 ht2
  have hl2 : (bstep tree k).length = tree.length := by unfold bstep; split <;> simp
  have ht2' : t < tree.length := by rw [hl2] at ht2; exact ht2
  have hkv := h.2 k hk hkn
  have hkA : k - 1 < A.length := by have := h.1; omega
  -- tree[k] = seg A k
  have hseg : tree[k]? = some (seg A k) := by
    rw [hkv, if_neg (by omega), Wc_self k hk]
    congr 1
    have := pre_succ A (k-1) hkA
    have e : k - 1 + 1 = k := by omega
    rw [e] at this
    unfold seg
    omega
  have hget : tree.getD k 0 = seg A k := by simp [List.getD_eq_getElem?_getD, hseg]
  by_cases hj : k + lowb k < tree.length
  · have hbs : bstep tree k = tree.set (k + lowb k) (tree.getD (k + lowb k) 0 + tree.getD k 0) := by
      unfold bstep; rw [if_pos hj]
    rw [hbs]
    by_cases htj : t = k + lowb k
    · subst htj
      have hv := h.2 (k + lowb k) (by omega) hj
      have hgj : tree.getD (k + lowb k) 0 = A.getD (k + lowb k - 1) 0 + pre A (Wc (k + lowb k) k) -
          pre A (k + lowb k - lowb (k + lowb k)) := by
        simp [List.getD_eq_getElem?_getD, hv, if_neg (show ¬ (k + lowb k < k) by omega)]
      rw [List.getElem?_set_self (by omega)]
      congr 1
      rw [if_neg (show ¬ (k + lowb k < k + 1) by omega), hgj, hget]
      obtain ⟨w1, w2⟩ := Wc_at_j k hk
      rw [w2]
      rw [w1]
      unfold seg
      omega
    · rw [List.getElem?_set_ne (Ne.symm htj)]
      rw [h.2 t ht1 ht2']
      congr 1
      by_cases htk : t < k
      · rw [if_pos htk, if_pos (by omega)]
      · by_cases hte : t = k
        · subst hte
          rw [if_neg (by omega), if_pos (by omega)]
          have hv := hkv
          rw [if_neg (by omega), Wc_self t hk] at hv
          have : seg A t = A.getD (t-1) 0 + pre A (t - 1) - pre A (t - lowb t) := by
            have := pre_succ A (t-1) hkA
            have e : t - 1 + 1 = t := by omega
            rw [e] at this
            unfold seg; omega
          rw [Wc_self t hk]
          exact this.symm
        · rw [if_neg htk, if_neg (by omega)]
          rw [Wc_same t k hk (by omega) htj]
  · have hbs : bstep tree k = tree := by unfold bstep; rw [if_neg hj]
    rw [hbs]
    rw [h.2 t ht1 ht2']
    congr 1
    by_cases htk : t < k
    · rw [if_pos htk, if_pos (by omega)]
    · by_cases hte : t = k
      · subst hte
        rw [if_neg (by omega), if_pos (by omega)]
        have hv := hkv
        rw [if_neg (by omega), Wc_self t hk] at hv
        have : seg A t = A.getD (t-1) 0 + pre A (t - 1) - pre A (t - lowb t) := by
          have := pre_succ A (t-1) hkA
          have e : t - 1 + 1 = t := by omega
          rw [e] at this
          unfold seg; omega
        rw [Wc_self t hk]
        exact this.symm
      · rw [if_neg htk, if_neg (by omega)]
        have htj : t ≠ k + lowb k := by omega
        rw [Wc_same t k hk (by omega) htj]

end Proofs.FenwickBuildMath
