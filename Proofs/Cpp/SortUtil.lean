import Proofs.Cpp.Gen.SortUtil
import Proofs.Cpp.Lib.Basic

/-! # `sort_util` (library/array/sort_util.hpp): `inv_perm`, `arg_sort`, `inv_arg_sort`, both `compress`, `sort_vector`,
`dedup_vector` -/

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

theorem mem_unique_sort {T : Type} [LinearOrder T] [Inhabited T] (x : Array T) (j : Nat) (hj : j < x.size) :
    x[j]! ∈ (Cpp.unique (Cpp.sort x)).toList := by
  unfold Cpp.unique
  simp only [List.toList_toArray, mem_uniqueList]
  rw [(sort_perm x).mem_iff, getElem!_pos x j hj]
  exact Array.getElem_mem_toList hj


/-- On a strictly increasing vector containing `t`, `std::lower_bound` finds `t`. -/
theorem lowerBound_found {T : Type} [LinearOrder T] [Inhabited T] (u : Array T) (hs : u.toList.Pairwise (· < ·))
    (t : T) (ht : t ∈ u.toList) :
    0 ≤ lowerBound u t ∧ (lowerBound u t).toNat < u.size ∧ u[(lowerBound u t).toNat]! = t := by
  obtain ⟨m, hm, e⟩ := List.getElem_of_mem ht
  simp only [Array.length_toList] at hm
  have hlt : u.toList.findIdx (fun a => !decide (a < t)) < u.toList.length :=
    List.findIdx_lt_length.mpr ⟨t, ht, by simp⟩
  have hk := List.findIdx_getElem (w := hlt)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at hk
  set k := u.toList.findIdx (fun a => !decide (a < t)) with hkdef
  have hkm : k = m := by
    rcases Nat.lt_trichotomy k m with h | h | h
    · have := strict_idx u hs k m h hm
      rw [getElem!_pos u k (by simpa using hlt), getElem!_pos u m hm] at this
      simp only [Array.getElem_toList] at e hk
      rw [e] at this
      exact absurd hk (not_le.mpr this)
    · exact h
    · have := List.not_of_lt_findIdx (p := fun a => !decide (a < t)) (xs := u.toList) (i := m) (by omega)
      simp only [e, lt_self_iff_false, decide_false, Bool.not_false, Bool.true_eq_false] at this
  simp only [Array.length_toList] at hlt
  refine ⟨by simp [lowerBound], by simp [lowerBound, ← hkdef]; omega, ?_⟩
  simp only [lowerBound, ← hkdef, Int.toNat_natCast]
  rw [hkm, getElem!_pos u m hm]
  simpa using e
/-- `compress(x, unzip, offset)`: `unzip` becomes the sorted distinct values of `x`, and the result holds the index of
`x[j]` in it plus `offset` (converted to `T`). -/
theorem compress_spec {T : Type} [LinearOrder T] [Inhabited T] [IntCast T] (x unzip : Array T) (offset : Int)
    (hn : x.size < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.compress_vec_vec_int x unzip offset
    ⦃⇓ r c => ⌜r.2 = Cpp.unique (Cpp.sort x) ∧ r.1.size = x.size ∧
      (∀ j, j < x.size → 0 ≤ lowerBound r.2 x[j]! ∧ (lowerBound r.2 x[j]!).toNat < r.2.size ∧
        r.2[(lowerBound r.2 x[j]!).toNat]! = x[j]! ∧ r.1[j]! = ((lowerBound r.2 x[j]! + offset : Int) : T)) ∧
      c ≤ t0 + 1 + 3 * x.size + sortCost x.size + x.size * (Nat.log2 x.size + 2)⌝⦄ := by
  have hu := unique_size (Cpp.sort x)
  rw [sort_size] at hu
  have hlog : Nat.log2 (Cpp.unique (Cpp.sort x)).size ≤ Nat.log2 x.size := log2_mono2 _ _ hu
  mvcgen [cp.compress_vec_vec_int]
  case inv1 =>
    exact ⇓⟨xs, cm⟩ c => ⌜cm.size = x.size ∧ (∀ j, j < xs.prefix.length →
      cm[j]! = ((lowerBound (Cpp.unique (Cpp.sort x)) x[j]! + offset : Int) : T)) ∧
      c ≤ t0 + 1 + 3 * x.size + sortCost x.size + xs.prefix.length * (Nat.log2 x.size + 2)⌝
  all_goals simp +zetaDelta [size, sort_size] at *
  case vc1.step =>
    have hr := ‹range _ _ = _ ++ _ :: _›
    obtain ⟨hs, hj, hc⟩ := ‹_ ∧ (∀ j, j < _ → _) ∧ _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp +zetaDelta [range_length, size] at hl e
    subst e
    refine ⟨by simp [hs], fun j hj' => ?_, ?_⟩
    · rw [getElemBang_set _ _ _ _ (by simp; omega)]
      split
      · rename_i h; simp at h; subst h; simp [get]
      · rename_i h; simp at h; exact hj j (by omega)
    · simp +zetaDelta only at *
      rw [Nat.add_mul, Nat.one_mul]
      omega
  case vc2.pre => exact ⟨by simp [replicate], by omega⟩
  case vc3.post.success =>
    obtain ⟨hs, hj, hc⟩ := ‹_ ∧ (∀ j, j < _ → _) ∧ _›
    have hsorted := (unique_sorted (Cpp.sort x) (sort_sorted x)).1
    refine ⟨hs, fun j hj' => ?_, hc⟩
    obtain ⟨h0, h1, h2⟩ := lowerBound_found _ hsorted _ (mem_unique_sort x j hj')
    exact ⟨h0, h1, h2, hj j hj'⟩

/-- `compress(x, offset)`: the indices of the values of `x` among its sorted distinct values, plus `offset`. -/
theorem compress_offset_spec {T : Type} [LinearOrder T] [Inhabited T] [IntCast T] (x : Array T) (offset : Int)
    (hn : x.size < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.compress_vec_int x offset
    ⦃⇓ r c => ⌜r.size = x.size ∧
      (∀ j, j < x.size → 0 ≤ lowerBound (Cpp.unique (Cpp.sort x)) x[j]! ∧
        (lowerBound (Cpp.unique (Cpp.sort x)) x[j]!).toNat < (Cpp.unique (Cpp.sort x)).size ∧
        (Cpp.unique (Cpp.sort x))[(lowerBound (Cpp.unique (Cpp.sort x)) x[j]!).toNat]! = x[j]! ∧
        r[j]! = ((lowerBound (Cpp.unique (Cpp.sort x)) x[j]! + offset : Int) : T)) ∧
      c ≤ t0 + 2 + 3 * x.size + sortCost x.size + x.size * (Nat.log2 x.size + 2)⌝⦄ := by
  have W := fun (Q : PostCond ((Array T) × (Array T)) PS) =>
    wp_of_triple (Q := Q) (fun t => compress_spec x ([] : List T).toArray offset hn t)
  mvcgen [cp.compress_vec_int, W]
  all_goals simp +zetaDelta at *
  intro r1 r2 c h1 h2 h3 hc
  subst h1
  exact ⟨h2, h3, by omega⟩

theorem range_pair_sublist (n a b : Nat) (hba : b < a) (ha : a < n) : [b, a].Sublist (List.range n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ]
    by_cases h : a = n
    · subst h
      exact List.Sublist.append (List.singleton_sublist.mpr (List.mem_range.mpr hba)) (List.Sublist.refl _)
    · exact (ih (by omega)).trans (List.sublist_append_left _ _)

theorem nodup_pair_sublist {α : Type} (l : List α) (hl : l.Nodup) (a b : α) (h1 : [a, b].Sublist l)
    (h2 : [b, a].Sublist l) : a = b := by
  induction l with
  | nil => simp at h1
  | cons x t ih =>
    have hx := (List.nodup_cons.mp hl).1
    have ht := (List.nodup_cons.mp hl).2
    rcases List.sublist_cons_iff.mp h1 with g1 | ⟨r1, e1, s1⟩ <;>
      rcases List.sublist_cons_iff.mp h2 with g2 | ⟨r2, e2, s2⟩
    · exact ih ht g1 g2
    · simp at e2; obtain ⟨rfl, rfl⟩ := e2
      exact absurd (g1.subset (by simp : b ∈ [a, b])) hx
    · simp at e1; obtain ⟨rfl, rfl⟩ := e1
      exact absurd (g2.subset (by simp : a ∈ [b, a])) hx
    · simp at e1 e2; obtain ⟨rfl, rfl⟩ := e1; exact e2.1.symm

/-- The stable sort of the indices `0 .. n-1` by `v`: ascending values, equal values in index order. -/
theorem stable_index_sort {T : Type} [LinearOrder T] [Inhabited T] (v : Array T) (n : Nat) :
    (((List.range n).map (fun i : Nat => (i : Int))).mergeSort
      (fun a b => !decide (v[b.toNat]! < v[a.toNat]!))).Pairwise
      (fun a b => v[a.toNat]! < v[b.toNat]! ∨ (v[a.toNat]! = v[b.toNat]! ∧ a < b)) := by
  set l := (List.range n).map (fun i : Nat => (i : Int))
  set le : Int → Int → Bool := fun a b => !decide (v[b.toNat]! < v[a.toNat]!)
  have trans : ∀ a b c, le a b = true → le b c = true → le a c = true := fun a b c h1 h2 => by
    simp [le] at h1 h2 ⊢; exact le_trans h1 h2
  have total : ∀ a b, (le a b || le b a) = true := fun a b => by simp [le]; exact le_total _ _
  have hs := List.pairwise_mergeSort trans total l
  have hnd : (l.mergeSort le).Nodup := (List.mergeSort_perm l le).nodup_iff.mpr
    (List.Pairwise.map _ (fun a b h e => h (by simpa using e)) List.nodup_range)
  rw [List.pairwise_iff_forall_sublist] at hs ⊢
  intro a b hab
  have hle := hs hab
  simp only [le, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have hma : a ∈ l := (List.mergeSort_perm l le).subset (hab.subset (by simp))
    have hmb : b ∈ l := (List.mergeSort_perm l le).subset (hab.subset (by simp))
    simp only [l, List.mem_map, List.mem_range] at hma hmb
    obtain ⟨a', ha', rfl⟩ := hma
    obtain ⟨b', hb', rfl⟩ := hmb
    by_contra hlt
    rcases Nat.lt_or_ge b' a' with hba | hba
    · have hsub : [(b' : Int), (a' : Int)].Sublist l := (range_pair_sublist n a' b' hba ha').map _
      have hle' : le (b' : Int) (a' : Int) = true := by
        simp only [le, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt]
        exact le_of_eq h.symm
      have h2 := List.pair_sublist_mergeSort trans total hle' hsub
      have e : (a' : Int) = (b' : Int) := nodup_pair_sublist _ hnd _ _ hab h2
      omega
    · have e : a' = b' := by omega
      subst e
      have := List.Nodup.sublist hab hnd
      simp at this

theorem stableSortBy_size {α : Type} (f : α → α → Bool) (l : Array α) : (Cpp.stableSortBy f l).size = l.size := by
  unfold Cpp.stableSortBy
  have := (List.mergeSort_perm l.toList (fun a b => !f b a)).length_eq
  simpa using this

/-- The result of `arg_sort(v)`. -/
def argSort {T : Type} [LT T] [DecidableLT T] [Inhabited T] (v : Array T) : Array Int :=
  Cpp.stableSortBy (fun a b => decide (v[a.toNat]! < v[b.toNat]!)) (Cpp.iota v.size 0)

theorem iota_toList (n : Nat) : (Cpp.iota n 0).toList = (List.range n).map (fun i : Nat => (i : Int)) := by
  apply List.ext_getElem
  · simp [Cpp.iota]
  · intro i h1 h2
    simp [Cpp.iota]

/-- `argSort v` lists `0 .. n-1`, by ascending value and, for equal values, by index. -/
theorem argSort_spec {T : Type} [LinearOrder T] [Inhabited T] (v : Array T) :
    (argSort v).toList.Perm ((List.range v.size).map (fun i : Nat => (i : Int))) ∧
    (argSort v).toList.Pairwise
      (fun a b => v[a.toNat]! < v[b.toNat]! ∨ (v[a.toNat]! = v[b.toNat]! ∧ a < b)) ∧
    (argSort v).size = v.size := by
  have hp : (argSort v).toList.Perm ((List.range v.size).map (fun i : Nat => (i : Int))) := by
    unfold argSort Cpp.stableSortBy
    simp only [List.toList_toArray]
    rw [← iota_toList]
    exact List.mergeSort_perm _ _
  refine ⟨hp, ?_, by have := hp.length_eq; simpa using this⟩
  unfold argSort Cpp.stableSortBy
  simp only [List.toList_toArray]
  rw [iota_toList]
  exact stable_index_sort v v.size

theorem arg_sort_spec {T : Type} [LinearOrder T] [Inhabited T] (v : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.arg_sort v
    ⦃⇓ r c => ⌜r = argSort v ∧ c = t0 + 1 + 3 * v.size + sortCost v.size⌝⦄ := by
  mvcgen [cp.arg_sort]
  all_goals simp +zetaDelta [size, replicate, argSort, get] at *
  have h1 : (Cpp.iota v.size 0).size = v.size := by simp [Cpp.iota]
  refine ⟨rfl, ?_⟩
  rw [stableSortBy_size, h1]
  omega

theorem argSort_perm_facts {T : Type} [LinearOrder T] [Inhabited T] (v : Array T) :
    (∀ j, j < (argSort v).size → 0 ≤ (argSort v)[j]! ∧ (argSort v)[j]! < (argSort v).size) ∧
    (∀ j k, j < (argSort v).size → k < (argSort v).size → (argSort v)[j]! = (argSort v)[k]! → j = k) := by
  obtain ⟨hp, -, hs⟩ := argSort_spec v
  have hnd : (argSort v).toList.Nodup := hp.nodup_iff.mpr
    (List.Pairwise.map _ (fun a b h e => h (by simpa using e)) List.nodup_range)
  refine ⟨fun j hj => ?_, fun j k hj hk e => ?_⟩
  · have hm : (argSort v)[j]! ∈ (argSort v).toList := by
      rw [getElem!_pos _ j hj]; exact Array.getElem_mem_toList hj
    rw [hp.mem_iff] at hm
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨i, hi, e⟩ := hm
    rw [← e, hs]; omega
  · rw [getElem!_pos _ j hj, getElem!_pos _ k hk] at e
    exact (List.Nodup.getElem_inj (xs := (argSort v).toList) (i := j) (j := k) (hi := by simpa using hj)
      (hj := by simpa using hk) hnd).mp (by simpa using e)

theorem inv_arg_sort_spec {T : Type} [LinearOrder T] [Inhabited T] (v : Array T) (hn : v.size < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.inv_arg_sort v
    ⦃⇓ r c => ⌜r.size = v.size ∧ (∀ j, j < v.size → r[((argSort v)[j]!).toNat]! = j) ∧
      c = t0 + 3 + 6 * v.size + sortCost v.size⌝⦄ := by
  have hs := (argSort_spec v).2.2
  obtain ⟨hv, hd⟩ := argSort_perm_facts v
  have W1 := fun (Q : PostCond (Array Int) PS) => wp_of_triple (Q := Q) (fun t => arg_sort_spec v t)
  have W2 := fun (Q : PostCond (Array Int) PS) =>
    wp_of_triple (Q := Q) (fun t => inv_perm_spec (argSort v) (by omega) hv hd t)
  mvcgen [cp.inv_arg_sort, W1]
  all_goals simp +zetaDelta at *
  apply (Triple.iff.mp (W2 _ _)) _
  intro r' c' h1 h2 h3
  exact ⟨by omega, fun j hj => h2 j (by omega), by omega⟩

end Proofs.Cpp.SortUtil
