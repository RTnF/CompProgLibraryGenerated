import Proofs.Cpp.Gen.SortUtil
import Proofs.Cpp.Lib.Basic

/-! # `sort_util` (library/array/sort_util.hpp): `inv_perm`, `compress`, `sort_vector`, `dedup_vector` -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.SortUtil

theorem sort_sorted {T : Type} [LinearOrder T] (x : Array T) : (Cpp.sort x).toList.Pairwise (· ≤ ·) := by
  unfold Cpp.sort
  simp only [List.toList_toArray]
  have h := List.pairwise_mergeSort (le := fun a b => !decide (b < a))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; exact le_trans h1 h2)
    (fun a b => by simp; exact le_total a b) x.toList
  exact h.imp (fun h => by simpa using h)

theorem sort_perm {T : Type} [LinearOrder T] (x : Array T) : (Cpp.sort x).toList.Perm x.toList := by
  unfold Cpp.sort
  simp only [List.toList_toArray]
  exact List.mergeSort_perm _ _

theorem mem_uniqueList {T : Type} [DecidableEq T] : ∀ (l : List T) (y : T), y ∈ uniqueList l ↔ y ∈ l
  | [], y => by simp [uniqueList]
  | [a], y => by simp [uniqueList]
  | a :: b :: t, y => by
    rw [uniqueList]
    split
    · rename_i h; rw [mem_uniqueList (a :: t)]; subst h; simp
    · rw [List.mem_cons, mem_uniqueList (b :: t)]; simp
termination_by l => l.length

theorem uniqueList_sorted {T : Type} [LinearOrder T] : ∀ (l : List T), l.Pairwise (· ≤ ·) →
    (uniqueList l).Pairwise (· < ·)
  | [], _ => by simp [uniqueList]
  | [a], _ => by simp [uniqueList]
  | a :: b :: t, hs => by
    rw [uniqueList]
    split
    · rename_i h
      apply uniqueList_sorted (a :: t)
      exact List.Pairwise.sublist (List.Sublist.cons₂ a (List.sublist_cons_self b t)) hs
    · rename_i h
      have hs' := List.pairwise_cons.mp hs
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, uniqueList_sorted (b :: t) hs'.2⟩
      rw [mem_uniqueList] at hy
      have hab : a < b := lt_of_le_of_ne (hs'.1 b (by simp)) h
      rcases List.mem_cons.mp hy with e | e
      · subst e; exact hab
      · exact lt_of_lt_of_le hab ((List.pairwise_cons.mp hs'.2).1 y e)
termination_by l => l.length

theorem sort_vector_spec {T : Type} [LinearOrder T] (x : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.sort_vector x
    ⦃⇓ r c => ⌜r = Cpp.sort x ∧ r.toList.Pairwise (· ≤ ·) ∧ r.toList.Perm x.toList ∧
      c = t0 + 1 + sortCost x.size⌝⦄ := by
  mvcgen [cp.sort_vector]
  simp_all +zetaDelta [sort_sorted, sort_perm]

theorem dedup_vector_spec {T : Type} [DecidableEq T] (x : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.dedup_vector x ⦃⇓ r c => ⌜r = Cpp.unique x ∧ c = t0 + 1 + x.size⌝⦄ := by
  mvcgen [cp.dedup_vector]
  simp_all +zetaDelta

/-- On a sorted vector, `dedup_vector` keeps exactly the values, in strictly increasing order. -/
theorem unique_sorted {T : Type} [LinearOrder T] (x : Array T) (hs : x.toList.Pairwise (· ≤ ·)) :
    (Cpp.unique x).toList.Pairwise (· < ·) ∧ ∀ y, y ∈ (Cpp.unique x).toList ↔ y ∈ x.toList := by
  unfold Cpp.unique
  simp only [List.toList_toArray]
  exact ⟨uniqueList_sorted _ hs, fun y => mem_uniqueList _ y⟩

theorem conv_id (x : Int) : (Conv.conv x : Int) = x := rfl

/-- The loop invariant of `inv_perm` after the first `k` positions. -/
def IP (v : Array Int) (k : Nat) (b : Array Int) : Prop :=
  b.size = v.size ∧ (∀ j, j < k → b[v[j]!.toNat]! = j) ∧
    (∀ y, y < v.size → (∀ j, j < k → v[j]!.toNat ≠ y) → b[y]! = -1)

theorem ip_step (v : Array Int) (hv : ∀ j, j < v.size → 0 ≤ v[j]! ∧ v[j]! < v.size)
    (hd : ∀ j k, j < v.size → k < v.size → v[j]! = v[k]! → j = k) (pref suff : List Int) (cur : Int)
    (hr : range 0 (size v) = pref ++ cur :: suff) (b : Array Int) (H : IP v pref.length b) :
    0 ≤ v[cur.toNat]! ∧ v[cur.toNat]! < v.size ∧ b[v[cur.toNat]!.toNat]! = -1 ∧
      IP v (pref.length + 1) (set b v[cur.toNat]! cur) ∧ cur = pref.length := by
  have e := range_cursor hr
  have hl := congrArg List.length hr
  simp [range_length, size] at hl e
  subst e
  obtain ⟨h1, h2, h3⟩ := H
  set k := pref.length
  have hvk := hv k (by omega)
  simp only [Int.toNat_natCast]
  have hfree : b[v[k]!.toNat]! = -1 := h3 _ (by omega) (fun j hj he => by
    have := hv j (by omega)
    have := hd j k (by omega) (by omega) (by omega); omega)
  have hg : ∀ y, (set b v[k]! (k : Int))[y]! = if y = v[k]!.toNat then (k : Int) else b[y]! := by
    intro y; rw [getElemBang_set _ _ _ _ (by omega)]
  refine ⟨hvk.1, hvk.2, hfree, ⟨by simp [h1], fun j hj => ?_, fun y hy hne => ?_⟩, by simp⟩
  · rw [hg]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · have hne : v[j]!.toNat ≠ v[k]!.toNat := fun he => by
        have := hd j k (by omega) (by omega) (by have := hv j (by omega); omega); omega
      rw [if_neg hne]; exact h2 j h
    · subst h; rw [if_pos rfl]
  · rw [hg, if_neg (fun he => hne k (by omega) he.symm)]
    exact h3 y hy (fun j hj => hne j (by omega))

theorem inv_perm_spec (v : Array Int) (hn : v.size < 2 ^ 31) (hv : ∀ j, j < v.size → 0 ≤ v[j]! ∧ v[j]! < v.size)
    (hd : ∀ j k, j < v.size → k < v.size → v[j]! = v[k]! → j = k) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.inv_perm v
    ⦃⇓ r c => ⌜r.size = v.size ∧ (∀ j, j < v.size → r[v[j]!.toNat]! = j) ∧ c = t0 + 1 + 3 * v.size⌝⦄ := by
  mvcgen [cp.inv_perm]
  case inv1 =>
    exact ⇓⟨xs, inv⟩ c => ⌜IP v xs.prefix.length inv ∧ c = t0 + 1 + v.size + xs.prefix.length⌝
  all_goals simp +zetaDelta [size, get, conv_id] at *
  case vc1.step.isTrue.isTrue =>
    obtain ⟨q1, q2, q3, q4, q5⟩ := ip_step v hv hd _ _ _ ‹range 0 _ = _ ++ _ :: _› _ ‹IP v _ _ ∧ _›.1
    exact ⟨q4, by have := ‹IP v _ _ ∧ _›.2; omega⟩
  case vc2.step.isTrue.isFalse =>
    obtain ⟨q1, q2, q3, q4, q5⟩ := ip_step v hv hd _ _ _ ‹range 0 _ = _ ++ _ :: _› _ ‹IP v _ _ ∧ _›.1
    rename_i h
    simp [q3] at h
  case vc3.step.isFalse =>
    obtain ⟨q1, q2, q3, q4, q5⟩ := ip_step v hv hd _ _ _ ‹range 0 _ = _ ++ _ :: _› _ ‹IP v _ _ ∧ _›.1
    rename_i h
    have := h (decide_eq_true q1)
    omega
  case vc4.pre =>
    refine ⟨⟨by simp [replicate], fun j hj => absurd hj (Nat.not_lt_zero _), fun y hy _ => ?_⟩, ‹_›⟩
    simp [replicate]; rw [getElem!_pos _ _ (by simp; omega)]; simp
  case vc5.post.success =>
    obtain ⟨⟨h1, h2, -⟩, hc⟩ := ‹IP v _ _ ∧ _›
    exact ⟨h1, h2, by omega⟩

theorem strict_idx {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (h : u.toList.Pairwise (· < ·))
    (i j : Nat) (hij : i < j) (hj : j < u.size) : u[i]! < u[j]! := by
  rw [getElem!_pos u i (by omega), getElem!_pos u j hj]
  have := List.pairwise_iff_getElem.mp h i j (by simp; omega) (by simpa using hj) hij
  simpa using this

/-- The binary search invariant: everything before `lo` is below `t`, everything from `hi` is at least `t`. -/
def BS {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (t : T) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ u.size ∧ (∀ i : Nat, (i : Int) < lo → u[i]! < t) ∧
    (∀ i : Nat, hi ≤ (i : Int) → i < u.size → t ≤ u[i]!)

theorem bw_half (d : Nat) (h : 0 < d) : bitWidth (d / 2) + 1 ≤ bitWidth d ∧ bitWidth (d - d / 2 - 1) + 1 ≤ bitWidth d := by
  have := bitWidth_div_two d h
  exact ⟨by omega, by have := bitWidth_mono (show d - d / 2 - 1 ≤ d / 2 by omega); omega⟩

theorem bs_lt {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (hs : u.toList.Pairwise (· < ·)) (t : T)
    (lo hi : Int) (H : BS u t lo hi) (hlh : lo < hi) (hm : get u (lo + div (hi - lo) 2) < t) :
    BS u t (lo + div (hi - lo) 2 + 1) hi ∧
      bitWidth (hi - (lo + div (hi - lo) 2 + 1)).toNat + 1 ≤ bitWidth (hi - lo).toNat ∧
      (hi - (lo + div (hi - lo) 2 + 1)).toNat < (hi - lo).toNat ∧ lo < lo + div (hi - lo) 2 + 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := H
  simp only [div] at hm ⊢
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hm ⊢
  rw [get_eq] at hm
  obtain ⟨_, hb⟩ := bw_half (hi - lo).toNat (by omega)
  have e : (hi - (lo + (hi - lo) / 2 + 1)).toNat = (hi - lo).toNat - (hi - lo).toNat / 2 - 1 := by omega
  refine ⟨⟨by omega, by omega, h2, fun i hi' => ?_, h4⟩, by rw [e]; omega, by omega, by omega⟩
  rcases Int.lt_or_le (i : Int) lo with h | h
  · exact h3 i h
  · rcases Nat.lt_or_ge i (lo + (hi - lo) / 2).toNat with h' | h'
    · exact lt_trans (strict_idx u hs _ _ h' (by omega)) hm
    · have : i = (lo + (hi - lo) / 2).toNat := by omega
      subst this; exact hm

theorem bs_ge {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (hs : u.toList.Pairwise (· < ·)) (t : T)
    (lo hi : Int) (H : BS u t lo hi) (hlh : lo < hi) (hm : t ≤ get u (lo + div (hi - lo) 2)) :
    BS u t lo (lo + div (hi - lo) 2) ∧
      bitWidth (lo + div (hi - lo) 2 - lo).toNat + 1 ≤ bitWidth (hi - lo).toNat ∧
      (lo + div (hi - lo) 2 - lo).toNat < (hi - lo).toNat ∧ div (hi - lo) 2 < hi - lo ∧
      bitWidth (div (hi - lo) 2).toNat + 1 ≤ bitWidth (hi - lo).toNat := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := H
  simp only [div] at hm ⊢
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hm ⊢
  rw [get_eq] at hm
  obtain ⟨hb, _⟩ := bw_half (hi - lo).toNat (by omega)
  have e : (lo + (hi - lo) / 2 - lo).toNat = (hi - lo).toNat / 2 := by omega
  have e2 : ((hi - lo) / 2).toNat = (hi - lo).toNat / 2 := by omega
  refine ⟨⟨h0, by omega, by omega, h3, fun i hi' hin => ?_⟩, by rw [e]; omega, by omega, by omega, by rw [e2]; omega⟩
  rcases Nat.lt_or_ge (lo + (hi - lo) / 2).toNat i with h' | h'
  · exact le_of_lt (lt_of_le_of_lt hm (strict_idx u hs _ _ h' hin))
  · have : i = (lo + (hi - lo) / 2).toNat := by omega
    subst this; exact hm

/-- When `t` occurs in `u`, the search ends on it. -/
theorem bs_found {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (hs : u.toList.Pairwise (· < ·)) (t : T)
    (ht : t ∈ u.toList) (lo : Int) (H : BS u t lo lo) : lo.toNat < u.size ∧ u[lo.toNat]! = t := by
  obtain ⟨h0, -, h2, h3, h4⟩ := H
  obtain ⟨q, hq, hqt⟩ := List.getElem_of_mem ht
  simp at hq
  have hq' : u[q]! = t := by rw [getElem!_pos u q hq]; simpa using hqt
  have hql : lo ≤ (q : Int) := by
    by_contra h
    have := h3 q (by omega); rw [hq'] at this; exact lt_irrefl _ this
  have hlt : lo.toNat < u.size := by omega
  refine ⟨hlt, ?_⟩
  have hge := h4 lo.toNat (by omega) hlt
  rcases Nat.lt_or_ge lo.toNat q with h | h
  · have := strict_idx u hs _ _ h hq
    rw [hq'] at this; exact absurd (lt_of_le_of_lt hge this) (lt_irrefl _)
  · have : q = lo.toNat := by omega
    subst this; exact hq'

/-- The invariant of the search loop of `compress` after the first `k` positions. -/
def CI {T : Type} [LinearOrder T] [Inhabited T] (x u : Array T) (k : Nat) (cm : Array Int) : Prop :=
  cm.size = x.size ∧ ∀ j, j < k → 0 ≤ cm[j]! ∧ cm[j]!.toNat < u.size ∧ u[cm[j]!.toNat]! = x[j]!

theorem arr_eq {T : Type} [Inhabited T] (r x : Array T) (h1 : r.size = x.size) (h2 : ∀ i, i < x.size → r[i]! = x[i]!) :
    r = x := by
  apply Array.ext h1
  intro i hi hi'
  have := h2 i hi'
  rwa [getElem!_pos r i hi, getElem!_pos x i hi'] at this

theorem sort_size {T : Type} [LinearOrder T] (x : Array T) : (Cpp.sort x).size = x.size := by
  have := (sort_perm x).length_eq; simpa using this

theorem uniqueList_length {T : Type} [DecidableEq T] : ∀ (l : List T), (uniqueList l).length ≤ l.length
  | [] => by simp [uniqueList]
  | [a] => by simp [uniqueList]
  | a :: b :: t => by
    rw [uniqueList]
    split
    · have := uniqueList_length (a :: t); simp at this ⊢; omega
    · have := uniqueList_length (b :: t); simp at this ⊢; omega
termination_by l => l.length

theorem unique_size {T : Type} [DecidableEq T] (x : Array T) : (Cpp.unique x).size ≤ x.size := by
  unfold Cpp.unique; simpa using uniqueList_length x.toList

theorem copy_step {T : Type} [Inhabited T] (x b : Array T) (pref suff : List Int) (cur : Int)
    (hr : range 0 (size x) = pref ++ cur :: suff) (h1 : b.size = x.size) (h2 : ∀ i, i < pref.length → b[i]! = x[i]!) :
    (set b cur (get x cur)).size = x.size ∧ (∀ i, i < pref.length + 1 → (set b cur (get x cur))[i]! = x[i]!) := by
  have e := range_cursor hr
  have hl := congrArg List.length hr
  simp [range_length, size] at hl e
  subst e
  refine ⟨by simp [h1], fun i hi => ?_⟩
  rw [getElemBang_set _ _ _ _ (by simp; omega)]
  split
  · rename_i h; simp at h; subst h; rfl
  · rename_i h; simp at h; exact h2 i (by omega)

theorem mem_unique_sort {T : Type} [LinearOrder T] [Inhabited T] (x : Array T) (j : Nat) (hj : j < x.size) :
    x[j]! ∈ (Cpp.unique (Cpp.sort x)).toList := by
  unfold Cpp.unique
  simp only [List.toList_toArray, mem_uniqueList]
  rw [(sort_perm x).mem_iff, getElem!_pos x j hj]
  exact Array.getElem_mem_toList hj

theorem cmp_step {T : Type} [LinearOrder T] [Inhabited T] (x : Array T) (pref suff : List Int) (cur : Int)
    (hr : range 0 (size x) = pref ++ cur :: suff) (b : Array Int) (H : CI x (Cpp.unique (Cpp.sort x)) pref.length b)
    (lo : Int) (hb : BS (Cpp.unique (Cpp.sort x)) x[cur.toNat]! lo lo) :
    CI x (Cpp.unique (Cpp.sort x)) (pref.length + 1) (set b cur lo) := by
  have e := range_cursor hr
  have hl := congrArg List.length hr
  simp [range_length, size] at hl e
  subst e
  have hs := (unique_sorted _ (sort_sorted x)).1
  have hlo0 := hb.1
  obtain ⟨f1, f2⟩ := bs_found _ hs _ (mem_unique_sort x _ (by omega)) lo hb
  obtain ⟨h1, h2⟩ := H
  refine ⟨by simp [h1], fun j hj => ?_⟩
  rw [getElemBang_set _ _ _ _ (by simp; omega)]
  split
  · rename_i h; simp at h; subst h
    exact ⟨hlo0, f1, by simpa using f2⟩
  · rename_i h; simp at h; exact h2 j (by omega)

theorem compress_spec {T : Type} [LinearOrder T] [Inhabited T] (x unzip : Array T) (cmp : Array Int)
    (hu : unzip.size = x.size) (hc : cmp.size = x.size) (hn : x.size < 2 ^ 31 - 1) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.compress x unzip cmp
    ⦃⇓ r c => ⌜r.1 = Cpp.unique (Cpp.sort x) ∧ r.2.size = x.size ∧
      (∀ j, j < x.size → 0 ≤ r.2[j]! ∧ r.2[j]!.toNat < r.1.size ∧ r.1[r.2[j]!.toNat]! = x[j]!) ∧
      c ≤ t0 + 1 + 2 * x.size + sortCost x.size + x.size * (2 + bitWidth x.size)⌝⦄ := by
  mvcgen [cp.compress]
  case inv1 =>
    exact ⇓⟨xs, u⟩ c => ⌜u.size = x.size ∧ (∀ i, i < xs.prefix.length → u[i]! = x[i]!) ∧
      c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    rename_i r s1 _ _ _ _
    exact ⇓⟨xs, cm⟩ c => ⌜r = x ∧ CI x (Cpp.unique (Cpp.sort r)) xs.prefix.length cm ∧
      c ≤ s1 + sortCost x.size + x.size + xs.prefix.length * (2 + bitWidth x.size)⌝
  case vc3.inv =>
    rename_i r _ _ _ _ _ _ cur _ _ _ s2 _
    exact ⟨fun ⟨lo, hi⟩ c => ⌜BS (Cpp.unique (Cpp.sort r)) x[cur.toNat]! lo hi ∧
        c + bitWidth (hi - lo).toNat ≤ s2 + 1 + bitWidth (Cpp.unique (Cpp.sort r)).size⌝,
      fun ⟨lo, _⟩ c => ⌜BS (Cpp.unique (Cpp.sort r)) x[cur.toNat]! lo lo ∧
        c ≤ s2 + 2 + bitWidth (Cpp.unique (Cpp.sort r)).size⌝,
      fun ⟨lo, hi⟩ => (hi - lo).toNat⟩
  all_goals simp +zetaDelta [size] at *
  case vc1.step =>
    obtain ⟨h1, h2, h3⟩ := ‹_ = x.size ∧ _ ∧ _›
    obtain ⟨c1, c2⟩ := copy_step x _ _ _ _ ‹range 0 _ = _ ++ _ :: _› h1 h2
    exact ⟨by simpa using c1, fun i hi => by simpa using c2 i hi, by omega⟩
  case vc2.pre => exact ⟨hu, ‹_›⟩
  case vc4.step.isTrue =>
    obtain ⟨⟨b0, b1, b2, b3, b4⟩, hc⟩ := ‹BS _ _ _ _ ∧ _›
    rename_i hle
    have e : _ = _ := Int.le_antisymm hle b1
    rw [e] at b2 b4 hc
    exact ⟨⟨b0, Int.le_refl _, b2, b3, b4⟩, by simp at hc; omega⟩
  case vc5.step.isFalse.isTrue =>
    obtain ⟨H, hc⟩ := ‹BS _ _ _ _ ∧ _›
    rename_i hlh hm
    obtain ⟨q1, q2, q3, q4⟩ := bs_lt _ (unique_sorted _ (sort_sorted _)).1 _ _ _ H hlh hm
    exact ⟨⟨q1, by omega⟩, q4, hlh⟩
  case vc6.step.isFalse.isFalse =>
    obtain ⟨H, hc⟩ := ‹BS _ _ _ _ ∧ _›
    rename_i hlh hm
    obtain ⟨q1, q2, q3, q4, q5⟩ := bs_ge _ (unique_sorted _ (sort_sorted _)).1 _ _ _ H hlh hm
    exact ⟨⟨q1, by omega⟩, q4, hlh⟩
  case vc7.step.pre =>
    rename_i r _ _ _ _ _ _ _ _ _ _ _ _
    have hm := unique_size (Cpp.sort r)
    rw [sort_size] at hm
    have := ‹r.size = x.size ∧ _ ∧ _›.1
    refine ⟨⟨Int.le_refl _, by omega, by omega, fun i hi => absurd hi (by omega),
      fun i hi hin => absurd hi (by omega)⟩, by simp only [fuel]; omega⟩
  case vc8.step.post.success =>
    obtain ⟨hrx, H, hc⟩ := ‹_ = x ∧ CI _ _ _ _ ∧ _›
    obtain ⟨hb, hc2⟩ := ‹BS _ _ _ _ ∧ _›
    rw [hrx] at H hb hc2 ⊢
    have hm := unique_size (Cpp.sort x)
    rw [sort_size] at hm
    have hbw := bitWidth_mono hm
    refine ⟨rfl, cmp_step _ _ _ _ ‹range 0 _ = _ ++ _ :: _› _ H _ hb, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  case vc9.post.success.pre =>
    obtain ⟨h1, h2, h3⟩ := ‹_ = x.size ∧ _ ∧ _›
    have e := arr_eq _ _ h1 h2
    subst e
    exact ⟨rfl, ⟨hc, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, by rw [sort_size]⟩
  case vc10.post.success.post.success =>
    obtain ⟨hrx, ⟨c1, c2⟩, hc⟩ := ‹_ = x ∧ CI _ _ _ _ ∧ _›
    have h0 := ‹_ = x.size ∧ _ ∧ _›.2.2
    rw [hrx] at c2 ⊢
    exact ⟨rfl, c1, c2, by omega⟩

end Proofs.Cpp.SortUtil
