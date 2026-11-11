import Proofs.Cpp.Gen.FenwickTree
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.Lowbit


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

end Proofs.Cpp.FenwickTree
