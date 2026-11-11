import Proofs.Cpp.Gen.CumulativeSum
import Proofs.Cpp.Lib.Basic

/-! # `CumulativeSum<T>` and `CumulativeSum2D<T>` (library/array/cumulative_sum.hpp)

One- and two-dimensional prefix sums over any additive commutative monoid `T` (a group for the range sums): the
constructors build the prefix sums in O(n) and O(n m), every query is O(1). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.CumulativeSum

section
variable {T : Type} [AddMonoid T] [Inhabited T]

/-- `A 0 + ... + A (k - 1)` of a vector. -/
def pre (v : Array T) (k : Nat) : T := (v.toList.take k).sum

theorem pre_succ (v : Array T) (k : Nat) (hk : k < v.size) : pre v (k + 1) = pre v k + v[k]! := by
  simp [pre, List.take_succ, getElem!_pos, hk]

theorem init_step (v cs : Array T) (L : Nat) (hL : L < v.size) (hsz : cs.size = v.size + 1)
    (hk : ∀ k, k ≤ L → cs[k]! = pre v k) :
    ∀ k, k ≤ L + 1 → (set cs (1 + (L : Int)) (get cs (1 + (L : Int) - 1) + get v (1 + (L : Int) - 1)))[k]! = pre v k := by
  intro k hk'
  have e1 : (1 + (L : Int)).toNat = L + 1 := by omega
  have e2 : 1 + (L : Int) - 1 = L := by omega
  rw [getElem!_set _ _ _ _ (by omega), e1, e2, get_natCast, get_natCast]
  by_cases e : k = L + 1
  · subst e; simp only [ite_true]; rw [hk L (le_refl _), pre_succ v L hL]
  · simp only [e, ite_false]; exact hk k (by omega)

/-- The object holds the prefix sums of `v`. -/
structure Rep (t : cp.CumulativeSum T) (v : Array T) : Prop where
  n : t.n = v.size
  size : t.cs.size = v.size + 1
  cs : ∀ k, k ≤ v.size → t.cs[k]! = pre v k

/-- `CumulativeSum(v)`: the prefix sums, in `2 n + 2` steps. -/
theorem init_spec (v : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum.init v ⦃⇓ t c => ⌜Rep t v ∧ c = t0 + 2 + 2 * v.size⌝⦄ := by
  mvcgen [cp.CumulativeSum.init]
  case inv1 =>
    exact ⇓⟨xs, cs⟩ c => ⌜cs.size = v.size + 1 ∧ (∀ k, k ≤ xs.prefix.length → cs[k]! = pre v k) ∧
                          c = t0 + 1 + (v.size + 1) + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    simp +zetaDelta [Proofs.Cpp.size] at hl
    subst e
    obtain ⟨hsz, hk, hc⟩ := ‹_ ∧ _ ∧ _›
    exact ⟨hsz, init_step v _ _ (by omega) hsz hk, by omega⟩
  · refine ⟨by simp [replicate, Proofs.Cpp.size], ?_, by simp [Proofs.Cpp.size]; omega⟩
    rw [getElem!_set _ _ _ _ (by simp [replicate, Proofs.Cpp.size])]
    simp [pre]
  · obtain ⟨hsz, hk, hc⟩ := ‹_ ∧ _ ∧ _›
    simp [range, Proofs.Cpp.size] at hk hc
    exact ⟨⟨by simp [Proofs.Cpp.size], hsz, hk⟩, by omega⟩

/-- `sum(a)`: `A 0 + ... + A (a - 1)` for `0 ≤ a ≤ n`, in one step. -/
theorem sum_spec (t : cp.CumulativeSum T) (v : Array T) (h : Rep t v) (a : Int) (h0 : 0 ≤ a) (ha : a ≤ v.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum.sum_int t a ⦃⇓ r c => ⌜r.1 = pre v a.toNat ∧ r.2 = t ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.CumulativeSum.sum_int]
  all_goals simp +zetaDelta at *
  · rw [get_eq, h.cs _ (by omega)]; exact ⟨rfl, ‹_›⟩
  · rw [h.n] at *; omega

end

section
variable {T : Type} [AddCommGroup T] [Inhabited T]

/-- `sum(a, b)`: `A a + ... + A (b - 1)` for `0 ≤ a ≤ b ≤ n`, in one step. -/
theorem sum_range_spec (t : cp.CumulativeSum T) (v : Array T) (h : Rep t v) (a b : Int) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ v.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum.sum_int_int t a b
    ⦃⇓ r c => ⌜r.1 = ((v.toList.drop a.toNat).take (b - a).toNat).sum ∧ r.2 = t ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.CumulativeSum.sum_int_int]
  all_goals simp +zetaDelta at *
  · rw [get_eq, get_eq, h.cs _ (by omega), h.cs _ (by omega)]
    have e : v.toList.take b.toNat = v.toList.take a.toNat ++ (v.toList.drop a.toNat).take (b - a).toNat := by
      rw [← List.take_append_drop a.toNat (v.toList.take b.toNat), List.take_take, List.drop_take]
      congr 2 <;> omega
    simp only [pre, e, List.sum_append]
    exact ⟨add_sub_cancel_left _ _, ‹_›⟩
  · exfalso
    have hn := h.n
    have := (‹0 ≤ a → a ≤ b → t.n < b›) h0 hab
    omega

end

end Proofs.Cpp.CumulativeSum

namespace Proofs.Cpp.CumulativeSum

section
variable {T : Type} [AddCommMonoid T] [Inhabited T]

/-- `v[i][0] + ... + v[i][j - 1]`. -/
def rowpre (v : Array (Array T)) (i j : Nat) : T := (v[i]!.toList.take j).sum

/-- The sum of `v` over `[0, i) × [0, j)`. -/
def rect (v : Array (Array T)) (i j : Nat) : T := ((v.toList.take i).map (fun row => (row.toList.take j).sum)).sum

theorem rect_succ (v : Array (Array T)) (i j : Nat) (hi : i < v.size) : rect v (i + 1) j = rect v i j + rowpre v i j := by
  simp [rect, rowpre, List.take_add_one, getElem!_pos, hi]

theorem rect_zero (v : Array (Array T)) (j : Nat) : rect v 0 j = 0 := by simp [rect]

theorem rect_col0 (v : Array (Array T)) (i : Nat) : rect v i 0 = 0 := by simp [rect]

theorem rowpre_succ (v : Array (Array T)) (i j : Nat) (hj : j < v[i]!.size) :
    rowpre v i (j + 1) = rowpre v i j + v[i]![j]! := by
  simp [rowpre, List.take_add_one, getElem!_pos, hj]

/-- Row `i` of `cs` holds the prefix sums of row `i - 1` of `v`. -/
def RowPre (v : Array (Array T)) (m : Nat) (cs : Array (Array T)) (i : Nat) : Prop :=
  cs[i]!.size = m + 1 ∧ ∀ j, j ≤ m → cs[i]![j]! = rowpre v (i - 1) j

/-- Row `i` of `cs` holds the two-dimensional prefix sums. -/
def RowRect (v : Array (Array T)) (m : Nat) (cs : Array (Array T)) (i : Nat) : Prop :=
  cs[i]!.size = m + 1 ∧ ∀ j, j ≤ m → cs[i]![j]! = rect v i j


theorem set_get_other (b : Array (Array T)) (i k : Nat) (x : Array T) (hk : k ≠ i) :
    (set b (i : Int) x)[k]! = b[k]! := by
  by_cases hi : i < b.size
  · rw [getElem!_set _ _ _ _ (by simpa using hi)]; simp [hk]
  · simp [set, Array.set!, Array.setIfInBounds, hi]

/-- One step of the inner loop of the second phase: append `v[I-1][J]` to the running row sum of row `I`. -/
theorem rowpush_step (v b : Array (Array T)) (I J : Nat) (m : Nat) (hI : 1 ≤ I) (hIn : I ≤ v.size)
    (hm : v[I - 1]!.size = m) (hJ : J < m) (hsz : b.size = v.size + 1)
    (hrow : b[I]!.size = J + 1) (hval : ∀ j, j ≤ J → b[I]![j]! = rowpre v (I - 1) j) :
    let b' := set b (I : Int) ((get b I).push (back (get b I) + get (get v ((I : Int) - 1)) J))
    b'.size = v.size + 1 ∧ (∀ k, k ≠ I → b'[k]! = b[k]!) ∧ b'[I]!.size = J + 1 + 1 ∧
      ∀ j, j ≤ J + 1 → b'[I]![j]! = rowpre v (I - 1) j := by
  intro b'
  have hIs : I < b.size := by omega
  have e1 : ((I : Int) - 1) = ((I - 1 : Nat) : Int) := by omega
  have hb' : b'[I]! = (b[I]!).push (b[I]![J]! + v[I - 1]![J]!) := by
    simp only [b', size_get_set_self _ _ _ hIs, get_natCast, e1, back, Array.back!]
    congr 2
    rw [hrow]; simp
  refine ⟨by simp [b', hsz], fun k hk => set_get_other _ _ _ _ hk, by rw [hb']; simp [hrow], fun j hj => ?_⟩
  rw [hb', getElem!_push, hrow]
  by_cases h1 : j < J + 1
  · simp only [h1, ite_true]; exact hval j (by omega)
  · have : j = J + 1 := by omega
    subst this
    simp only [lt_irrefl, ite_false, ite_true, hval J (le_refl _)]
    rw [rowpre_succ v (I - 1) J (by omega)]


/-- The start of row `I` in the second phase: the row becomes `[0]`. -/
theorem rowstart_step (v b : Array (Array T)) (I : Nat) (hIn : I ≤ v.size) (hsz : b.size = v.size + 1)
    (hempty : b[I]! = ([] : List T).toArray) :
    let b' := set b (I : Int) ((get b I).push 0)
    b'.size = v.size + 1 ∧ (∀ k, k ≠ I → b'[k]! = b[k]!) ∧ b'[I]!.size = 1 ∧ b'[I]![0]! = rowpre v (I - 1) 0 := by
  intro b'
  have hIs : I < b.size := by omega
  have hb' : b'[I]! = (b[I]!).push 0 := by simp only [b', size_get_set_self _ _ _ hIs, get_natCast]
  refine ⟨by simp [b', hsz], fun k hk => set_get_other _ _ _ _ hk, by rw [hb', hempty]; simp, ?_⟩
  rw [hb', hempty]; simp [rowpre]

/-- One step of the inner loop of the third phase: add row `I - 1` to row `I` at column `j`. -/
theorem colacc_step (v b : Array (Array T)) (I j m : Nat) (hI : 2 ≤ I) (hIn : I ≤ v.size) (hj : j ≤ m)
    (hsz : b.size = v.size + 1) (hprev : RowRect v m b (I - 1)) (hcur : b[I]![j]! = rowpre v (I - 1) j)
    (hrowsz : b[I]!.size = m + 1) :
    let b' := set b (I : Int) (set (get b I) (j : Int) (get (get b I) j + get (get b ((I : Int) - 1)) j))
    b'.size = v.size + 1 ∧ (∀ k, k ≠ I → b'[k]! = b[k]!) ∧ b'[I]!.size = m + 1 ∧
      (∀ k, k ≠ j → b'[I]![k]! = b[I]![k]!) ∧ b'[I]![j]! = rect v I j := by
  intro b'
  have hIs : I < b.size := by omega
  have e1 : ((I : Int) - 1) = ((I - 1 : Nat) : Int) := by omega
  have hb' : b'[I]! = set (b[I]!) (j : Int) (b[I]![j]! + b[I - 1]![j]!) := by
    simp only [b', size_get_set_self _ _ _ hIs, get_natCast, e1]
  refine ⟨by simp [b', hsz], fun k hk => set_get_other _ _ _ _ hk, by rw [hb']; simp [hrowsz], fun k hk => ?_, ?_⟩
  · rw [hb', getElem!_set _ _ _ _ (by simp; omega)]; simp [hk]
  · rw [hb', getElem!_set _ _ _ _ (by simp; omega)]
    simp only [Int.toNat_natCast, ite_true, hcur, hprev.2 j hj]
    rw [show I = (I - 1) + 1 by omega, rect_succ v (I - 1) j (by omega), add_comm]
    simp


theorem assert_rows (v : Array (Array T)) (hrect : ∀ i, i < v.size → v[i]!.size = v[0]!.size)
    {pref suff : List Int} {cur : Int} (h : range 1 (size v) = pref ++ cur :: suff) :
    size (get v cur) = size (get v 0) := by
  have hl := range_prefix_length h
  have e := range_cursor h
  subst e
  simp only [Proofs.Cpp.size] at hl ⊢
  rw [show (1 + (pref.length : Int)) = ((1 + pref.length : Nat) : Int) by push_cast; ring, get_natCast]
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl, get_natCast, hrect _ (by omega)]

theorem init2_spec (v : Array (Array T)) (hn : 0 < v.size) (hm : 0 < v[0]!.size)
    (hrect : ∀ i, i < v.size → v[i]!.size = v[0]!.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum2D.init v
    ⦃⇓ t c => ⌜t.n = v.size ∧ t.m = v[0]!.size ∧ t.cs.size = v.size + 1 ∧
               (∀ i, i ≤ v.size → RowRect v v[0]!.size t.cs i) ∧
               c ≤ t0 + 1 + 5 * v.size + 3 * v.size * v[0]!.size⌝⦄ := by
  mvcgen [cp.CumulativeSum2D.init]
  case inv1 => exact ⇓⟨xs, _⟩ c => ⌜c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    exact ⇓⟨xs, cs⟩ c => ⌜cs.size = v.size + 1 ∧ cs[0]! = Array.replicate (v[0]!.size + 1) 0 ∧
      (∀ i, 1 ≤ i → i ≤ xs.prefix.length → RowPre v v[0]!.size cs i) ∧
      (∀ i, xs.prefix.length + 1 ≤ i → i ≤ v.size → cs[i]! = ([] : List T).toArray) ∧
      c = t0 + 1 + (v.size - 1) + (v.size + 1) + (v[0]!.size + 1) + xs.prefix.length * (2 + 2 * v[0]!.size)⌝
  case inv3 =>
    rename_i pref cur suff hcur b c hb cs'
    exact ⇓⟨ys, cs⟩ c' => ⌜cs.size = v.size + 1 ∧ cs[0]! = Array.replicate (v[0]!.size + 1) 0 ∧
      (∀ i, 1 ≤ i → i < cur.toNat → RowPre v v[0]!.size cs i) ∧
      (∀ i, cur.toNat < i → i ≤ v.size → cs[i]! = ([] : List T).toArray) ∧
      cs[cur.toNat]!.size = ys.prefix.length + 1 ∧
      (∀ j, j ≤ ys.prefix.length → cs[cur.toNat]![j]! = rowpre v (cur.toNat - 1) j) ∧
      c' = c + 2 + 2 * ys.prefix.length⌝
  case inv4 =>
    exact ⇓⟨xs, cs⟩ c => ⌜cs.size = v.size + 1 ∧
      (∀ i, i ≤ xs.prefix.length + 1 → i ≤ v.size → RowRect v v[0]!.size cs i) ∧
      (∀ i, xs.prefix.length + 2 ≤ i → i ≤ v.size → RowPre v v[0]!.size cs i) ∧
      c = t0 + 1 + (v.size - 1) + (v.size + 1) + (v[0]!.size + 1) + v.size * (2 + 2 * v[0]!.size) +
        xs.prefix.length * (1 + v[0]!.size)⌝
  case inv5 =>
    rename_i pref cur suff hcur b c hb
    exact ⇓⟨ys, cs⟩ c' => ⌜cs.size = v.size + 1 ∧
      (∀ i, i < cur.toNat → RowRect v v[0]!.size cs i) ∧
      (∀ i, cur.toNat < i → i ≤ v.size → RowPre v v[0]!.size cs i) ∧
      cs[cur.toNat]!.size = v[0]!.size + 1 ∧ cs[cur.toNat]![0]! = 0 ∧
      (∀ j, 1 ≤ j → j ≤ ys.prefix.length → cs[cur.toNat]![j]! = rect v cur.toNat j) ∧
      (∀ j, ys.prefix.length < j → j ≤ v[0]!.size → cs[cur.toNat]![j]! = rowpre v (cur.toNat - 1) j) ∧
      c' = c + 1 + ys.prefix.length⌝
  all_goals simp +zetaDelta at *
  -- phase 1: the asserts on the row sizes
  · omega
  · exact absurd (assert_rows v hrect ‹_›) ‹_›
  · assumption
  · -- phase 2, inner loop: extend row I by one prefix sum
    rename_i cs n m t1 s_1 H1 cs_1 t2 cs_2 pref cur suff H2 b s_2 H3 cs_3 pref_1 cur_1 suff_1 H4 b_1 s_3 cs_4 H5 H6 H7
    have e1 := range_cursor H2; have l1 := range_prefix_length H2
    have e2 := range_cursor H4; have l2 := range_prefix_length H4
    simp +zetaDelta [Proofs.Cpp.size] at e1 l1 e2 l2
    subst e1 e2
    rw [show (1 + (pref.length : Int)) = ((pref.length + 1 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast] at *
    obtain ⟨hsz, h0, hlow, hhigh, hrow, hval, hc⟩ := H7
    have l2' : pref_1.length < v[0]!.size := by simpa [get_eq] using l2
    obtain ⟨s1, s2, s3, s4⟩ := rowpush_step v b_1 (pref.length + 1) pref_1.length v[0]!.size (by omega) (by omega)
      (by rw [show pref.length + 1 - 1 = pref.length by omega]; exact hrect _ (by omega)) (by omega) hsz hrow hval
    refine ⟨hsz, by rw [s2 0 (by omega)]; exact h0, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, s3, s4, by omega⟩
    · rw [RowPre, s2 i (by omega)]; exact hlow i hi1 hi2
    · rw [s2 i (by omega)]; exact hhigh i hi1 hi2
  · -- phase 2: start row I with [0]
    rename_i cs n m t1 s_1 H1 cs_1 t2 cs_2 pref cur suff H2 b s_2 H3 cs_3 H4 H5
    have e1 := range_cursor H2; have l1 := range_prefix_length H2
    simp +zetaDelta [Proofs.Cpp.size] at e1 l1
    subst e1
    rw [show (1 + (pref.length : Int)) = ((pref.length + 1 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast] at *
    obtain ⟨hsz, h0, hlow, hhigh, hc⟩ := H3
    obtain ⟨s1, s2, s3, s4⟩ := rowstart_step v b (pref.length + 1) (by omega) hsz (hhigh _ (le_refl _) (by omega))
    refine ⟨hsz, by rw [s2 0 (by omega)]; exact h0, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, s3, s4⟩
    · rw [RowPre, s2 i (by omega)]; exact hlow i hi1 (by omega)
    · rw [s2 i (by omega)]; exact hhigh i (by omega) hi2
  · -- phase 2: row I is complete
    rename_i cs n m t1 s_1 H1 cs_1 t2 cs_2 pref cur suff H2 b s_2 H3 cs_3 r s_3 H4 H5 H6
    have e1 := range_cursor H2; have l1 := range_prefix_length H2
    simp +zetaDelta [Proofs.Cpp.size] at e1 l1 H6
    subst e1
    rw [show (1 + (pref.length : Int)) = ((pref.length + 1 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast, get_eq, Int.toNat_zero] at *
    obtain ⟨hsz, h0, hlow, hhigh, hc⟩ := H3
    obtain ⟨rsz, r0, rlow, rhigh, rrow, rval, rc⟩ := H6
    refine ⟨rsz, r0, fun i hi1 hi2 => ?_, fun i hi1 hi2 => rhigh i (by omega) hi2, by rw [rc, hc]; ring⟩
    rcases Nat.lt_or_eq_of_le hi2 with h | h
    · exact rlow i hi1 (by omega)
    · subst h; exact ⟨rrow, rval⟩
  · -- phase 2: before the rows
    simp +zetaDelta [Proofs.Cpp.size, get_eq, resize, replicate, range_length] at *
    refine ⟨by simp [Proofs.Cpp.set], fun i h1 h2 => by omega, fun i hi1 hi2 => ?_, by omega⟩
    · rw [getElem!_set _ _ _ _ (by simp)]
      simp [show i ≠ 0 by omega, getElem!_pos, show i < v.size + 1 by omega]
  · -- phase 3, inner loop: add row I - 1 to row I at column j
    rename_i cs n m t1 s_1 H1 cs_1 t2 cs_2 r s_2 H2 pref cur suff H3 b s_3 H4 pref_1 cur_1 suff_1 H5 b_1 s_4 cs_3 H6 H7 H8
    have e1 := range_cursor H3; have l1 := range_prefix_length H3
    have e2 := range_cursor H5; have l2 := range_prefix_length H5
    simp +zetaDelta [Proofs.Cpp.size, get_eq] at e1 l1 e2 l2
    subst e1 e2
    rw [show (2 + (pref.length : Int)) = ((pref.length + 2 : Nat) : Int) by push_cast; ring,
      show (1 + (pref_1.length : Int)) = ((pref_1.length + 1 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast] at *
    obtain ⟨hsz, hlow, hhigh, hrow, h0, hdone, hrest, hc⟩ := H8
    obtain ⟨s1, s2, s3, s4, s5⟩ := colacc_step v b_1 (pref.length + 2) (pref_1.length + 1) v[0]!.size (by omega)
      (by omega) (by omega) hsz (hlow _ (by omega)) (hrest _ (by omega) (by omega)) hrow
    refine ⟨hsz, fun i hi => ?_, fun i hi1 hi2 => ?_, s3, by rw [s4 0 (by omega)]; exact h0,
      fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, by omega⟩
    · rw [RowRect, s2 i (by omega)]; exact hlow i hi
    · rw [RowPre, s2 i (by omega)]; exact hhigh i hi1 hi2
    · rcases Nat.lt_or_eq_of_le hj2 with h | h
      · rw [s4 j (by omega)]; exact hdone j hj1 (by omega)
      · subst h; exact s5
    · rw [s4 j (by omega)]; exact hrest j (by omega) hj2
  · -- phase 3: start row I
    rename_i pref cur suff H3 b s_3 H4 H5 H6
    have e1 := range_cursor H3; have l1 := range_prefix_length H3
    simp +zetaDelta [Proofs.Cpp.size, get_eq] at e1 l1
    subst e1
    rw [show (2 + (pref.length : Int)) = ((pref.length + 2 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast] at *
    obtain ⟨hsz, hlow, hhigh, hc⟩ := H4
    have hI := hhigh (pref.length + 2) (le_refl _) (by omega)
    refine ⟨hsz, fun i hi => hlow i (by omega) (by omega), fun i hi1 hi2 => hhigh i (by omega) hi2, hI.1,
      by rw [hI.2 0 (by omega)]; simp [rowpre], fun j h1 h2 => by omega, fun j h1 h2 => hI.2 j h2⟩
  · -- phase 3: row I is complete
    rename_i pref cur suff H3 b s_3 H4 r_1 s_4 H5 H6 H7
    have e1 := range_cursor H3; have l1 := range_prefix_length H3
    simp +zetaDelta [Proofs.Cpp.size, get_eq] at e1 l1 H7
    subst e1
    rw [show (2 + (pref.length : Int)) = ((pref.length + 2 : Nat) : Int) by push_cast; ring] at *
    simp only [Int.toNat_natCast, range_length] at *
    obtain ⟨hsz, hlow, hhigh, hc⟩ := H4
    obtain ⟨rsz, rlow, rhigh, rrow, r0, rdone, rrest, rc⟩ := H7
    have e3 : ((v[0]!.size : Int) + 1 - 1).toNat = v[0]!.size := by omega
    refine ⟨rsz, fun i hi1 hi2 => ?_, fun i hi1 hi2 => rhigh i (by omega) hi2, by rw [rc, hc, e3]; ring⟩
    rcases Nat.lt_or_eq_of_le hi1 with h | h
    · exact rlow i (by omega)
    · subst h
      refine ⟨rrow, fun j hj => ?_⟩
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; rw [r0, rect_col0]
      · exact rdone j hpos (by omega)
  · -- phase 3: before the rows
    rename_i r s_2 H2 H3 H4
    simp +zetaDelta [Proofs.Cpp.size, range_length] at H2 ⊢
    obtain ⟨rsz, r0, rlow, rhigh, rc⟩ := H2
    refine ⟨rsz, fun i hi1 hi2 => ?_, fun i hi1 hi2 => rlow i (by omega) hi2, by rw [rc]⟩
    rcases Nat.lt_or_eq_of_le hi1 with h | h
    · have : i = 0 := by omega
      subst this
      refine ⟨by rw [r0]; simp, fun j hj => ?_⟩
      rw [r0, rect_zero]; simp [getElem!_pos, show j < v[0]!.size + 1 by omega]
    · subst h
      obtain ⟨h1, h2⟩ := rlow 1 (le_refl _) (by omega)
      refine ⟨h1, fun j hj => ?_⟩
      rw [h2 j hj, show (1 : Nat) = 0 + 1 by rfl, rect_succ v 0 j (by omega), rect_zero]; simp
  · -- the result
    rename_i r s_2 H2 r_1 s_3 H3 H4 H5
    simp +zetaDelta [Proofs.Cpp.size, range_length, get_eq] at H3 ⊢
    obtain ⟨rsz, rlow, rhigh, rc⟩ := H3
    refine ⟨rsz, fun i hi => rlow i (by omega) hi, ?_⟩
    obtain ⟨K, hK⟩ : ∃ K, v.size = K + 1 := ⟨v.size - 1, by omega⟩
    rw [rc]
    simp only [hK, show (((K + 1 : Nat) : Int) + 1 - 2).toNat = K by omega, Nat.add_sub_cancel] at *
    ring_nf
    omega
  all_goals (exfalso; simp_all +zetaDelta [Proofs.Cpp.size, get_eq])


/-- The two-dimensional object holds the prefix sums of the `n × m` array `v`. -/
structure Rep2 (t : cp.CumulativeSum2D T) (v : Array (Array T)) : Prop where
  n : t.n = v.size
  m : t.m = v[0]!.size
  rows : ∀ i, i ≤ v.size → RowRect v v[0]!.size t.cs i

/-- `sum(a, b)`: the sum over `[0, a) × [0, b)`, in one step. -/
theorem sum2_spec (t : cp.CumulativeSum2D T) (v : Array (Array T)) (h : Rep2 t v) (a b : Int) (ha : 0 ≤ a)
    (ha' : a ≤ v.size) (hb : 0 ≤ b) (hb' : b ≤ v[0]!.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum2D.sum_int_int t a b
    ⦃⇓ r c => ⌜r.1 = rect v a.toNat b.toNat ∧ r.2 = t ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.CumulativeSum2D.sum_int_int]
  all_goals simp +zetaDelta at *
  · rw [get_eq, get_eq, (h.rows a.toNat (by omega)).2 b.toNat (by omega)]; exact ⟨rfl, ‹_›⟩
  · have := h.m; omega
  · have := h.n; omega

end

section
variable {T : Type} [AddCommGroup T] [Inhabited T]

/-- `sum(a1, b1, a2, b2)`: the sum over `[a1, a2) × [b1, b2)` (inclusion–exclusion of four prefix rectangles),
in one step. -/
theorem sum2_range_spec (t : cp.CumulativeSum2D T) (v : Array (Array T)) (h : Rep2 t v) (a1 b1 a2 b2 : Int)
    (h1 : 0 ≤ a1) (h2 : a1 ≤ a2) (h3 : a2 ≤ v.size) (h4 : 0 ≤ b1) (h5 : b1 ≤ b2) (h6 : b2 ≤ v[0]!.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.CumulativeSum2D.sum_int_int_int_int t a1 b1 a2 b2
    ⦃⇓ r c => ⌜r.1 = rect v a2.toNat b2.toNat - rect v a1.toNat b2.toNat - rect v a2.toNat b1.toNat +
                 rect v a1.toNat b1.toNat ∧ r.2 = t ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.CumulativeSum2D.sum_int_int_int_int]
  all_goals simp +zetaDelta at *
  · simp only [get_eq]
    rw [(h.rows a2.toNat (by omega)).2 b2.toNat (by omega), (h.rows a1.toNat (by omega)).2 b2.toNat (by omega),
      (h.rows a2.toNat (by omega)).2 b1.toNat (by omega), (h.rows a1.toNat (by omega)).2 b1.toNat (by omega)]
    exact ⟨rfl, ‹_›⟩
  all_goals (exfalso; have := h.m; have := h.n; omega)

end

end Proofs.Cpp.CumulativeSum
