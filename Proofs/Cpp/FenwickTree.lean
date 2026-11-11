import Proofs.Cpp.Gen.FenwickTree
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.Lowbit
import Proofs.FenwickBuildMath


/-! # `FenwickTree<T>` (library/segment_tree/fenwick_tree.hpp)

For any commutative additive monoid `T` (a commutative group for `sum(l, r)`), the tree represents an
array `A : Nat → T` of `n` elements (`Rep`); the constructors build it, `add` updates it, `sum` returns
prefix sums; the costs are O(n) for the constructors and O(log n) for `sum` and `add`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.FenwickMath

namespace Proofs.Cpp.FenwickTree

variable {T : Type} [AddCommMonoid T] [Inhabited T]

/-- `A lo + ... + A (hi - 1)`. -/
def seg (A : Nat → T) (lo hi : Nat) : T := ((List.range' lo (hi - lo)).map A).sum

theorem seg_consecutive (A : Nat → T) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    seg A a b + seg A b c = seg A a c := by
  have e := List.range'_append (s := a) (m := b - a) (n := c - b) (step := 1)
  rw [show a + 1 * (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at e
  simp [seg, ← e, List.sum_append]

/-- The tree represents the array `A` of `n` elements: node `k` holds `A` over `[k - lowb k, k)`. The
default-constructed tree has an empty vector. -/
structure Rep (t : cp.FenwickTree T) (n : Nat) (A : Nat → T) : Prop where
  bound : n < 2 ^ 31
  size : t.tree.size = n + 1 ∨ (t.tree.size = 0 ∧ n = 0)
  node : ∀ k, 0 < k → k ≤ n → t.tree[k]! = seg A (k - lowb k) k

theorem stepsS_succ (r : Nat) (hr : 0 < r) : stepsS r = 1 + stepsS (r - lowb r) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [stepsS]

theorem log2_mono' (a b : Nat) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.log2_zero]
  · exact log2_mono a b ha h

theorem stepsS_le_log (r : Nat) : stepsS r ≤ Nat.log2 r + 1 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp [stepsS]
  · have := stepsS_le r h; omega

/-- `sum(r)`: the prefix sum `A 0 + ... + A (r - 1)` in at most `log2 n + 3` steps. -/
theorem sum_spec (t : cp.FenwickTree T) (n : Nat) (A : Nat → T) (h : Rep t n A) (r : Int) (h0 : 0 ≤ r)
    (hr : r ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FenwickTree.sum_int t r
    ⦃⇓ s c => ⌜s = seg A 0 r.toNat ∧ c = t0 + 2 + stepsS r.toNat⌝⦄ := by
  mvcgen [cp.FenwickTree.sum_int]
  case inv =>
    exact ⟨fun ⟨q, s⟩ c => ⌜0 ≤ q ∧ q ≤ r ∧ s + seg A 0 q.toNat = seg A 0 r.toNat ∧
                            c + stepsS q.toNat = t0 + 1 + stepsS r.toNat⌝,
           fun ⟨_, s⟩ c => ⌜s = seg A 0 r.toNat ∧ c = t0 + 2 + stepsS r.toNat⌝,
           fun ⟨q, _⟩ => q.toNat⟩
  all_goals simp_all +zetaDelta [fuel]
  · obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    generalize (‹ℤ × T›).1 = q at *
    obtain rfl : q = 0 := by omega
    simp [seg, stepsS] at h3 h4 ⊢
    exact ⟨h3, by omega⟩
  · obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    generalize (‹ℤ × T›).1 = q at *
    have hq : 0 < q := ‹_›
    rw [land_neg q hq]
    have hl := lowb_pos q.toNat (by omega)
    have hl' := lowb_le q.toNat (by omega)
    have hnode := h.node q.toNat (by omega) (by omega)
    have e1 : (q - (lowb q.toNat : Int)).toNat = q.toNat - lowb q.toNat := by omega
    have e2 : get t.tree q = t.tree[q.toNat]! := rfl
    have e3 := stepsS_succ q.toNat (by omega)
    refine ⟨⟨by omega, by omega, ?_, by rw [e1]; omega⟩, by omega⟩
    rw [e1, e2, hnode, ← h3, ← seg_consecutive A (Nat.zero_le _) (Nat.sub_le q.toNat (lowb q.toNat))]
    ac_rfl
  · have := h.bound; omega

theorem seg_update (A : Nat → T) (i : Nat) (val : T) (lo hi : Nat) :
    seg (Function.update A i (A i + val)) lo hi = seg A lo hi + (if lo ≤ i ∧ i < hi then val else 0) := by
  unfold seg
  generalize hm : hi - lo = m
  induction m generalizing lo with
  | zero => simp; omega
  | succ m ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih (lo + 1) (by omega)]
    by_cases h : lo = i
    · subst h
      have : ¬ (lo + 1 ≤ lo ∧ lo < hi) := by omega
      simp only [Function.update_self, this, ite_false, add_zero, show lo ≤ lo ∧ lo < hi from ⟨le_refl _, by omega⟩,
        ite_true]
      simp only [show ¬ (lo + 1 ≤ lo) by omega, false_and, and_true, ite_false, ite_true, add_zero, true_and]
      ac_rfl
    · simp only [Function.update, h, dite_false]
      by_cases h2 : lo + 1 ≤ i ∧ i < hi
      · simp only [h2, ite_true, show lo ≤ i ∧ i < hi from ⟨by omega, h2.2⟩]; ac_rfl
      · simp only [h2, ite_false, show ¬ (lo ≤ i ∧ i < hi) by omega, add_zero]

/-- `k` is one of the nodes whose range contains position `p - 1` (1-indexed `p`). -/
def Covers (p k : Nat) : Prop := k - lowb k < p ∧ p ≤ k

instance (p k : Nat) : Decidable (Covers p k) := by unfold Covers; infer_instance

theorem covers_next (p i : Nat) (hi : 0 < i) (h : Covers p i) : Covers p (i + lowb i) := by
  have := lowb_next i hi
  have := lowb_pos i hi
  unfold Covers at *
  omega

theorem covers_gap (p i k : Nat) (hi : 0 < i) (h : Covers p i) (h1 : i < k) (h2 : k < i + lowb i) :
    ¬ Covers p k := by
  have := lowb_between i (k - i) hi (by omega) (by omega)
  rw [show i + (k - i) = k by omega] at this
  unfold Covers at *
  omega

theorem stepsA_succ (len k : Nat) (hk : 0 < k) (hl : k < len) : stepsA len k = 1 + stepsA len (k + lowb k) := by
  rw [stepsA]; simp [hk, hl]

theorem stepsA_stop (len k : Nat) (hl : len ≤ k) : stepsA len k = 0 := by
  rw [stepsA]; simp; omega

theorem rep_size_pos {t : cp.FenwickTree T} {n : Nat} {A : Nat → T} (h : Rep t n A) (hs : 0 < t.tree.size) :
    t.tree.size = n + 1 := by
  rcases h.size with h | h <;> omega

/-- One iteration of the loop of `add`: node `q` receives `val`, the next node is `q + lowb q`. -/
theorem add_step {t : cp.FenwickTree T} {n : Nat} {A : Nat → T} (h : Rep t n A) (p : Nat) (val : T)
    (tr : Array T) (q : Nat) (hsz : tr.size = t.tree.size) (hpq : p ≤ q) (hp : 0 < p)
    (hcov : q < t.tree.size → Covers p q)
    (hnodes : ∀ k, 0 < k → k ≤ n → tr[k]! = seg A (k - lowb k) k + (if k < q ∧ Covers p k then val else 0))
    (hq : q < tr.size) :
    (∀ k, 0 < k → k ≤ n → (set tr (q : Int) (get tr q + val))[k]! =
        seg A (k - lowb k) k + (if k < q + lowb q ∧ Covers p k then val else 0)) ∧
      (q + lowb q < t.tree.size → Covers p (q + lowb q)) := by
  have hs := rep_size_pos h (by omega)
  have hc := hcov (by omega)
  have hq0 : 0 < q := by omega
  refine ⟨?_, fun _ => covers_next p q hq0 hc⟩
  intro k hk hkn
  by_cases e : k = q
  · subst e
    rw [getElem!_set _ _ _ _ (by simpa using hq), get_eq, Int.toNat_natCast, hnodes k hk hkn]
    have := lowb_pos k hk
    simp [hc, show k < k + lowb k by omega]
  · rw [getElem!_set _ _ _ _ (by simpa using hq), Int.toNat_natCast, if_neg e]
    rw [hnodes k hk hkn]
    by_cases hlt : k < q
    · simp [hlt, show k < q + lowb q by omega]
    · by_cases hgt : k < q + lowb q
      · have := covers_gap p q k hq0 hc (by omega) hgt
        simp [hlt, this]
      · simp [hlt, hgt]

/-- `add(i, val)`: `A i += val` (nothing for `i ≥ n`), in `stepsA (n + 1) (i + 1) + 2` steps. -/
theorem add_spec (t : cp.FenwickTree T) (n : Nat) (A : Nat → T) (h : Rep t n A) (i : Int) (h0 : 0 ≤ i)
    (hi : i + 1 < 2 ^ 31) (val : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FenwickTree.add t i val
    ⦃⇓ t' c => ⌜Rep t' n (if i.toNat < n then Function.update A i.toNat (A i.toNat + val) else A) ∧
                c = t0 + 2 + stepsA t.tree.size (i.toNat + 1)⌝⦄ := by
  mvcgen [cp.FenwickTree.add]
  case inv =>
    exact ⟨fun ⟨tr, q⟩ c => ⌜tr.size = t.tree.size ∧ i < q ∧ i.toNat + 1 ≤ q.toNat ∧
                              (q.toNat < t.tree.size → Covers (i.toNat + 1) q.toNat) ∧
                              (∀ k, 0 < k → k ≤ n → tr[k]! = seg A (k - lowb k) k +
                                 (if k < q.toNat ∧ Covers (i.toNat + 1) k then val else 0)) ∧
                              c + stepsA t.tree.size q.toNat = t0 + 1 + stepsA t.tree.size (i.toNat + 1)⌝,
           fun ⟨tr, _⟩ c => ⌜Rep ⟨tr⟩ n (if i.toNat < n then Function.update A i.toNat (A i.toNat + val) else A) ∧
                              c = t0 + 2 + stepsA t.tree.size (i.toNat + 1)⌝,
           fun ⟨_, q⟩ => (t.tree.size - q).toNat⟩
  all_goals simp_all +zetaDelta [fuel]
  · -- the loop stops: every node in range has been visited
    obtain ⟨hsz, hiq, hpq, hcov, hnodes, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    generalize (‹Array T × ℤ›).2 = q at *
    generalize (‹Array T × ℤ›).1 = tr at *
    have hstop : t.tree.size ≤ q.toNat := by simp [size] at *; omega
    refine ⟨⟨h.bound, by rw [hsz]; exact h.size, ?_⟩, by rw [stepsA_stop _ _ hstop] at hc; omega⟩
    intro k hk hkn
    have hs := rep_size_pos h (by rcases h.size with h' | h' <;> omega)
    rw [hnodes k hk hkn]
    have hkq : (k : Int) < q := by omega
    simp only [hkq, true_and]
    by_cases hin : i < (n : Int)
    · simp only [hin, ite_true, seg_update]
      unfold Covers
      congr 1
      by_cases hc : k - lowb k < i.toNat + 1 ∧ i.toNat + 1 ≤ k
      · simp only [hc, show (k - lowb k ≤ i.toNat ∧ i.toNat < k) by omega, ite_true]
      · simp only [hc, show ¬(k - lowb k ≤ i.toNat ∧ i.toNat < k) by omega, ite_false]
    · have : ¬ Covers (i.toNat + 1) k := by unfold Covers; omega
      simp [hin, this]
  · -- one iteration
    obtain ⟨hsz, hiq, hpq, hcov, hnodes, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    generalize (‹Array T × ℤ›).2 = q at *
    generalize (‹Array T × ℤ›).1 = tr at *
    have hq0 : 0 < q := by omega
    have hqs : q.toNat < tr.size := by simp [size] at *; omega
    rw [land_neg q hq0]
    have hnodes' : ∀ k, 0 < k → k ≤ n → tr[k]! = seg A (k - lowb k) k +
        (if k < q.toNat ∧ Covers (i.toNat + 1) k then val else 0) := by
      intro k a b; rw [hnodes k a b]; simp only [show ((k : Int) < q) ↔ (k < q.toNat) by omega]
    obtain ⟨hn', hcov'⟩ := add_step h (i.toNat + 1) val tr q.toNat hsz hpq (by omega) hcov hnodes' hqs
    rw [show ((q.toNat : Nat) : Int) = q by omega] at hn'
    have hl := lowb_pos q.toNat (by omega)
    have e1 : (q + (lowb q.toNat : Int)).toNat = q.toNat + lowb q.toNat := by omega
    rw [stepsA_succ _ _ (by omega) (by omega)] at hc
    refine ⟨⟨by omega, by omega, by rw [e1]; exact hcov', ?_, by rw [e1]; omega⟩, by omega⟩
    intro k hk hkn
    rw [hn' k hk hkn]
    simp only [show ((k : Int) < q + lowb q.toNat) ↔ (k < q.toNat + lowb q.toNat) by omega]
  · -- before the loop
    have e : (i + 1).toNat = i.toNat + 1 := by omega
    rw [e]
    refine ⟨⟨le_refl _, fun _ => ?_, fun k hk hkn => ?_, rfl⟩, ?_⟩
    · have := lowb_pos (i.toNat + 1) (by omega)
      unfold Covers; omega
    · rw [h.node k hk hkn]
      have : ¬ ((k : Int) < i + 1 ∧ Covers (i.toNat + 1) k) := by unfold Covers; omega
      simp only [this, ite_false, add_zero]
    · have := h.bound
      rcases h.size with h' | h' <;> omega

/-- `FenwickTree()`: the tree of the empty array. -/
theorem init_0_spec (A : Nat → T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.FenwickTree.init_0 : Cpp.M (cp.FenwickTree T))
    ⦃⇓ t c => ⌜Rep t 0 A ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.FenwickTree.init_0]
  simp_all
  exact ⟨by norm_num, Or.inr ⟨rfl, rfl⟩, fun k hk hkn => by omega⟩

/-- `FenwickTree(n)`: the tree of `n` zeros (`T()` is `0`), in `n + 2` steps. -/
theorem init_int_spec (hd : (default : T) = 0) (n : Int) (h0 : 0 ≤ n) (hn : n + 1 < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.FenwickTree.init_int n : Cpp.M (cp.FenwickTree T))
    ⦃⇓ t c => ⌜Rep t n.toNat (fun _ => 0) ∧ c = t0 + 1 + (n.toNat + 1)⌝⦄ := by
  mvcgen [cp.FenwickTree.init_int]
  simp_all +zetaDelta [replicate]
  refine ⟨⟨by omega, Or.inl (by simp; omega), fun k hk hkn => ?_⟩, by omega⟩
  simp [getElem!_pos, show k < (n + 1).toNat by omega, seg]

/-- The state of the second loop of the vector constructor before node `k` is pushed up: nodes below `k`
are complete; node `t ≥ k` holds `A (t - 1)` and the part `[t - lowb t, Wc t k)` of its range. -/
def BuildInv (A : Nat → T) (n k : Nat) (tr : Array T) : Prop :=
  ∀ t, 0 < t → t ≤ n → tr[t]! =
    if t < k then seg A (t - lowb t) t else A (t - 1) + seg A (t - lowb t) (Proofs.FenwickBuildMath.Wc t k)

theorem seg_last (A : Nat → T) (a k : Nat) (h : a < k) : A (k - 1) + seg A a (k - 1) = seg A a k := by
  rw [← seg_consecutive A (by omega : a ≤ k - 1) (by omega : k - 1 ≤ k), add_comm]
  congr 1
  simp [seg, show k - (k - 1) = 1 by omega]

theorem build_step (A : Nat → T) (n k : Nat) (tr : Array T) (hsz : tr.size = n + 1) (hk : 0 < k) (hkn : k < n)
    (h : BuildInv A n k tr) :
    BuildInv A n (k + 1)
      (if k + lowb k < n + 1 then set tr (↑(k + lowb k)) (get tr ↑(k + lowb k) + get tr ↑k) else tr) := by
  have hL := lowb_pos k hk
  have hLn := lowb_next k hk
  have hLk := lowb_le k hk
  have hWj := Proofs.FenwickBuildMath.Wc_at_j k hk
  intro t ht htn
  have hfull : ∀ t, 0 < t → t ≤ n → t ≤ k → tr[t]! = seg A (t - lowb t) t := by
    intro t ht htn htk
    rw [h t ht htn]
    by_cases hlt : t < k
    · simp [hlt]
    · have : t = k := by omega
      subst this
      simp only [lt_irrefl, ite_false, Proofs.FenwickBuildMath.Wc_self t ht]
      exact seg_last A _ t (by omega)
  have hrhs : (if t < k + 1 then seg A (t - lowb t) t
      else A (t - 1) + seg A (t - lowb t) (Proofs.FenwickBuildMath.Wc t (k + 1))) =
      (if t ≤ k then seg A (t - lowb t) t
      else A (t - 1) + seg A (t - lowb t) (Proofs.FenwickBuildMath.Wc t (k + 1))) := by
    by_cases h' : t ≤ k
    · simp [h', show t < k + 1 by omega]
    · simp [h', show ¬ t < k + 1 by omega]
  rw [hrhs]
  by_cases hj : k + lowb k < n + 1
  · simp only [hj, ite_true]
    rw [getElem!_set _ _ _ _ (by simp; omega)]
    simp only [Int.toNat_natCast]
    by_cases htj : t = k + lowb k
    · subst htj
      simp only [ite_true, show ¬ k + lowb k ≤ k by omega, ite_false, get_eq, Int.toNat_natCast]
      rw [h (k + lowb k) (by omega) (by omega), hfull k hk (by omega) (le_refl _),
        if_neg (by omega), hWj.1, hWj.2, add_assoc, seg_consecutive A (by omega) (by omega)]
    · simp only [htj, ite_false]
      by_cases htk : t ≤ k
      · simp [htk, hfull t ht htn htk]
      · simp only [htk, ite_false]
        rw [h t ht htn, if_neg (by omega), Proofs.FenwickBuildMath.Wc_same t k hk (by omega) htj]
  · simp only [hj, ite_false]
    have htj : t ≠ k + lowb k := by omega
    by_cases htk : t ≤ k
    · simp [htk, hfull t ht htn htk]
    · simp only [htk, ite_false]
      rw [h t ht htn, if_neg (by omega), Proofs.FenwickBuildMath.Wc_same t k hk (by omega) htj]

/-- `FenwickTree(v)`: the tree of `A j = v[j]` (`T()` is `0`), in at most `3 n + 2` steps. -/
theorem init_vec_spec (v : Array T) (hn : v.size + 1 < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FenwickTree.init_vec v
    ⦃⇓ t c => ⌜Rep t v.size (fun j => v[j]!) ∧ c ≤ t0 + 3 * v.size + 2⌝⦄ := by
  mvcgen [cp.FenwickTree.init_vec]
  case inv1 =>
    exact ⇓⟨xs, tr⟩ c => ⌜tr.size = v.size + 1 ∧ (∀ t, 0 < t → t ≤ xs.prefix.length → tr[t]! = v[t - 1]!) ∧
                          c = t0 + 1 + (v.size + 1) + xs.prefix.length⌝
  case inv2 =>
    exact ⇓⟨xs, tr⟩ c => ⌜tr.size = v.size + 1 ∧ BuildInv (fun j => v[j]!) v.size (xs.prefix.length + 1) tr ∧
                          c = t0 + 1 + (v.size + 1) + v.size + xs.prefix.length⌝
  all_goals simp_all +zetaDelta
  · -- first loop: copy v[cur] into node cur + 1
    rename_i pref cur suff hcur b c tr ht hinv
    obtain ⟨hsz, hv, hc⟩ := hinv
    have e := range_cursor hcur
    have hl := range_prefix_length hcur
    simp [size] at e hl
    refine ⟨fun t ht' htl => ?_, by omega⟩
    rw [getElem!_set _ _ _ _ (by omega)]
    by_cases h' : t = (cur + 1).toNat
    · simp only [h', ite_true, get_eq]; congr 1; omega
    · simp only [h', ite_false]; exact hv t ht' (by omega)
  · simp [replicate, size]
    intro t a b; omega
  · -- second loop, the parent is in range
    rename_i pref cur suff hcur b c tr ht h1 hinv hif
    obtain ⟨hsz, hb, hc⟩ := hinv
    have e := range_cursor hcur
    have hl := range_prefix_length hcur
    simp [size] at e hl hif
    have hk : (0 : Int) < cur := by omega
    rw [land_neg cur hk] at hif ⊢
    have st := build_step (fun j => v[j]!) v.size (pref.length + 1) b hsz (by omega) (by omega) hb
    have ek : cur.toNat = pref.length + 1 := by omega
    rw [ek] at hif ⊢
    rw [if_pos (by omega)] at st
    refine ⟨?_, by omega⟩
    have e1 : cur + (lowb (pref.length + 1) : Int) = ((pref.length + 1 + lowb (pref.length + 1) : Nat) : Int) := by
      push_cast; omega
    have e2 : cur = ((pref.length + 1 : Nat) : Int) := by push_cast; omega
    rw [e1, e2]
    exact st
  · -- second loop, the parent is past the end
    rename_i pref cur suff hcur b c ht h1 hinv hif
    obtain ⟨hsz, hb, hc⟩ := hinv
    have e := range_cursor hcur
    have hl := range_prefix_length hcur
    simp [size] at e hl hif
    have hk : (0 : Int) < cur := by omega
    rw [land_neg cur hk] at hif
    have st := build_step (fun j => v[j]!) v.size (pref.length + 1) b hsz (by omega) (by omega) hb
    have ek : cur.toNat = pref.length + 1 := by omega
    rw [ek] at hif
    rw [if_neg (by omega)] at st
    exact ⟨st, by omega⟩
  · -- between the loops
    rename_i tr c hinv
    obtain ⟨hsz, hv, hc⟩ := hinv
    simp [range, size] at hv ⊢
    intro t ht htn
    rw [hv t ht htn, if_neg (by omega), Proofs.FenwickBuildMath.Wc_one t ht]
    simp [seg]
  · -- after the loops
    rename_i tr1 c1 hinv1 tr c hinv
    obtain ⟨hsz, hb, hc⟩ := hinv
    simp [range, size] at hb hc ⊢
    refine ⟨⟨by omega, Or.inl hsz, fun t ht htn => ?_⟩, by omega⟩
    rw [hb t ht htn]
    have e : v.size - 1 + 1 = v.size := by omega
    rw [e]
    by_cases hlt : t < v.size
    · simp [hlt]
    · have : t = v.size := by omega
      subst this
      simp only [hlt, ite_false]
      rw [Proofs.FenwickBuildMath.Wc_self _ ht]
      exact seg_last _ _ _ (by have := lowb_pos v.size ht; omega)

end Proofs.Cpp.FenwickTree

namespace Proofs.Cpp.FenwickTree

variable {T : Type} [AddCommGroup T] [Inhabited T]

/-- `sum(l, r)`: `A l + ... + A (r - 1)` for a commutative group `T`, in at most `2 log2 n + 7` steps. -/
theorem sum_range_spec (t : cp.FenwickTree T) (n : Nat) (A : Nat → T) (h : Rep t n A) (l r : Int) (hl : 0 ≤ l)
    (hlr : l ≤ r) (hr : r ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FenwickTree.sum_int_int t l r
    ⦃⇓ s c => ⌜s = seg A l.toNat r.toNat ∧ c ≤ t0 + 2 * Nat.log2 n + 7⌝⦄ := by
  obtain ⟨s1, c1, e1, p1⟩ := run_of_triple (sum_spec t n A h r (by omega) hr (t0 + 1))
  obtain ⟨s2, c2, e2, p2⟩ := run_of_triple (sum_spec t n A h l hl (by omega) c1)
  apply triple_of_run (s1 - s2) c2
  · simp [cp.FenwickTree.sum_int_int, tick, e1, e2]
  · refine ⟨?_, ?_⟩
    · rw [p1.1, p2.1, ← seg_consecutive A (Nat.zero_le l.toNat) (by omega : l.toNat ≤ r.toNat)]
      simp
    · have := stepsS_le_log r.toNat
      have := stepsS_le_log l.toNat
      have := log2_mono' r.toNat n (by omega)
      have := log2_mono' l.toNat n (by omega)
      omega

end Proofs.Cpp.FenwickTree
