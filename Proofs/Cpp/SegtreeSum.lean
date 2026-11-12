import Proofs.Cpp.Gen.SegtreeSum
import Proofs.Cpp.Lib.Basic
import Proofs.SegTreeMath

/-! # `segtree_sum` (library/segment_tree/segtree_sum.hpp)

The iterative segment tree for sums modulo `2^64`. The monoid of `Proofs.SegTreeMath` is instantiated with addition
modulo `2^64` (`M64`); the node vector is the model list `vL`. The query keeps `PInv` (`prod_step`), the update keeps
`SInv` (`sinv_step`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.SegTreeMath

namespace Proofs.Cpp.SegtreeSum

theorem two64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num

/-- Addition modulo `2^64` on the values `[0, 2^64)`. -/
def M64 : Mon where
  V x := 0 ≤ x ∧ x < 18446744073709551616
  op a b := (a + b) % 18446744073709551616
  e := 0
  closed a b _ _ := ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  he := by decide
  assoc a b c _ _ _ := by rw [Int.emod_add_emod, Int.add_emod_emod, Int.add_assoc]
  lid a ha := by simp only [Int.zero_add]; exact Int.emod_eq_of_lt ha.1 ha.2
  rid a ha := by simp only [Int.add_zero]; exact Int.emod_eq_of_lt ha.1 ha.2

/-- The node array as model values. -/
def vL (node : Array UInt64) : List Int := node.toList.map (fun x => (x.toNat : Int))

theorem vL_getD (node : Array UInt64) (k : Nat) : (vL node).getD k 0 = ((node[k]!).toNat : Int) := by
  unfold vL
  by_cases h : k < node.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos node k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg node k h]; rfl

theorem vL_allV (node : Array UInt64) : AllV M64 (vL node) := by
  intro x hx
  simp only [vL, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact ⟨by omega, by have := y.toNat_lt; rw [two64] at this; omega⟩

theorem add_val (x y : UInt64) : (((x + y).toNat : Nat) : Int) = M64.op (x.toNat : Int) (y.toNat : Int) := by
  simp only [M64, UInt64.toNat_add, two64]; push_cast; rfl

theorem get_val (node : Array UInt64) (x : Int) (hx : 0 ≤ x) : ((get node x).toNat : Int) = (vL node).getD x.toNat 0 := by
  rw [vL_getD, get_eq]

theorem mod2 (x : Int) (hx : 0 ≤ x) : mod x 2 ≠ 0 ↔ x.toNat % 2 = 1 := by
  simp only [mod]; rw [Int.tmod_eq_emod_of_nonneg hx]; omega

theorem div2 (x : Int) (hx : 0 ≤ x) : (div x 2).toNat = x.toNat / 2 ∧ 0 ≤ div x 2 := by
  simp only [div]; rw [Int.tdiv_eq_ediv_of_nonneg hx]; omega

theorem cl (l : Int) (hl0 : 0 ≤ l) : (div (if mod l 2 ≠ 0 then l + 1 else l) 2).toNat = pl1 l.toNat / 2 := by
  unfold pl1
  by_cases h : mod l 2 ≠ 0
  · rw [if_pos h, if_pos ((mod2 l hl0).mp h), (div2 _ (by omega)).1]; congr 1; omega
  · rw [if_neg h, if_neg (fun h' => h ((mod2 l hl0).mpr h')), (div2 _ hl0).1]

theorem cr (r : Int) (hr0 : 1 ≤ r) : (div (if mod r 2 ≠ 0 then r - 1 else r) 2).toNat = pr1 r.toNat / 2 := by
  unfold pr1
  by_cases h : mod r 2 ≠ 0
  · rw [if_pos h, if_pos ((mod2 r (by omega)).mp h), (div2 _ (by omega)).1]; congr 1; omega
  · rw [if_neg h, if_neg (fun h' => h ((mod2 r (by omega)).mpr h')), (div2 _ (by omega)).1]

theorem cleft (node : Array UInt64) (l : Int) (hl0 : 0 ≤ l) (left : UInt64) :
    (((if mod l 2 ≠ 0 then left + get node l else left).toNat : Nat) : Int) =
      pleft M64 (vL node) l.toNat (left.toNat : Int) := by
  unfold pleft
  by_cases h : mod l 2 ≠ 0
  · rw [if_pos h, if_pos ((mod2 l hl0).mp h), add_val, get_val node l hl0]
  · rw [if_neg h, if_neg (fun h' => h ((mod2 l hl0).mpr h'))]

theorem cright (node : Array UInt64) (r : Int) (hr0 : 1 ≤ r) (right : UInt64) :
    (((if mod r 2 ≠ 0 then right + get node (r - 1) else right).toNat : Nat) : Int) =
      pright M64 (vL node) r.toNat (right.toNat : Int) := by
  unfold pright
  by_cases h : mod r 2 ≠ 0
  · rw [if_pos h, if_pos ((mod2 r (by omega)).mp h), add_val, get_val node (r - 1) (by omega),
      show (r - 1).toNat = r.toNat - 1 by omega]
    simp only [M64]; rw [Int.add_comm]
  · rw [if_neg h, if_neg (fun h' => h ((mod2 r (by omega)).mpr h'))]

/-- The loop invariant of the product. -/
def QI (node : Array UInt64) (N : Nat) (T : Int) (C : Nat) (l r : Int) (left right : UInt64) (c : Nat) : Prop :=
  1 ≤ l ∧ PInv M64 (vL node) N T l.toNat r.toNat left.toNat right.toNat ∧ c + bitWidth r.toNat ≤ C

theorem step_vc (node : Array UInt64) (N : Nat) (hT : TInv M64 (vL node) N) (T : Int) (C : Nat) (l r : Int)
    (left right : UInt64) (c : Nat) (I : QI node N T C l r left right c) (hlr : l < r) :
    QI node N T C (div (if mod l 2 ≠ 0 then l + 1 else l) 2) (div (if mod r 2 ≠ 0 then r - 1 else r) 2)
        (if mod l 2 ≠ 0 then left + get node l else left) (if mod r 2 ≠ 0 then right + get node (r - 1) else right)
        (c + 1) ∧
      div (if mod r 2 ≠ 0 then r - 1 else r) 2 < r ∧ 0 < r := by
  obtain ⟨hl1, hI, hc⟩ := I
  have S := prod_step M64 (vL node) N T (vL_allV node) hT _ _ _ _ hI (by omega)
  have h1 := cl l (by omega)
  have h2 := cr r (by omega)
  have h3 := cleft node l (by omega) left
  have h4 := cright node r (by omega) right
  have hpr : pr1 r.toNat ≤ r.toNat := by unfold pr1; split <;> omega
  have hpl : 2 ≤ pl1 l.toNat := by unfold pl1; split <;> omega
  have hrl := S.2.1
  have hbw := bitWidth_div_two r.toNat (by omega)
  have hmono := bitWidth_mono (Nat.div_le_div_right (c := 2) hpr)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := (div2 _ (show 0 ≤ (if mod l 2 ≠ 0 then l + 1 else l) by split <;> omega)).2
    have : (div (if mod l 2 ≠ 0 then l + 1 else l) 2).toNat ≥ 1 := by rw [h1]; omega
    omega
  · rw [h1, h2, h3, h4]; exact S
  · rw [h2]; omega
  · have := (div2 _ (show 0 ≤ (if mod r 2 ≠ 0 then r - 1 else r) by split <;> omega)).2
    have h5 : (div (if mod r 2 ≠ 0 then r - 1 else r) 2).toNat < r.toNat := by rw [h2]; omega
    omega

theorem exit_vc (node : Array UInt64) (N : Nat) (T : Int) (C : Nat) (l r : Int) (left right : UInt64) (c : Nat)
    (I : QI node N T C l r left right c) (h : r ≤ l) :
    M64.op (left.toNat : Int) (right.toNat : Int) = T ∧ c + 1 ≤ C + 1 := by
  obtain ⟨hl1, hI, hc⟩ := I
  exact ⟨PInv_exit M64 _ _ _ _ _ _ _ hI (by omega), by omega⟩

theorem init_vc (node : Array UInt64) (N : Nat) (hT : TInv M64 (vL node) N) (hsz : node.size = 2 * N)
    (hN30 : N < 2 ^ 30) (l r : Nat) (hlr : l ≤ r) (hr : r ≤ N) (C c : Nat) (hc : c + bitWidth (r + N) ≤ C) :
    QI node N (rfold M64 (vL node) (N + l) (r - l)) C ((l : Int) + div (size node) 2) ((r : Int) + div (size node) 2)
      0 0 c ∧ (r : Int) + div (size node) 2 < 18446744073709551616 := by
  have hd : div (size node) 2 = (N : Int) := by
    simp only [div, size, hsz]; push_cast; exact Int.mul_tdiv_cancel_left _ (by decide)
  have hN := hT.1
  rw [hd]
  have e1 : ((l : Int) + N).toNat = N + l := by omega
  have e2 : ((r : Int) + N).toNat = N + r := by omega
  have hV := rfold_V M64 (vL node) (vL_allV node) (r - l) (N + l) (by rw [hT.2.1]; omega)
  have hP : PInv M64 (vL node) N (rfold M64 (vL node) (N + l) (r - l)) (N + l) (N + r) 0 0 := by
    refine ⟨by omega, by omega, by omega, M64.he, M64.he, ?_⟩
    rw [show N + r - (N + l) = r - l by omega]
    exact (congrArg (M64.op · M64.e) (M64.lid _ hV)).trans (M64.rid _ hV)
  have hb : r + N < 18446744073709551616 := by omega
  refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
  · rw [e1, e2]; simpa using hP
  · rw [e2, Nat.add_comm N r]; exact hc

theorem segtree_sum_product_spec (node : Array UInt64) (N : Nat) (hT : TInv M64 (vL node) N) (hN30 : N < 2 ^ 30)
    (l r : Nat) (hlr : l ≤ r) (hr : r ≤ N) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.segtree_sum_product node l r
    ⦃⇓ res c => ⌜((res.toNat : Nat) : Int) = rfold M64 (vL node) (N + l) (r - l) ∧
      c ≤ t0 + 2 + bitWidth (r + N)⌝⦄ := by
  have hsz : node.size = 2 * N := by have := hT.2.1; simpa [vL] using this
  mvcgen [cp.segtree_sum_product]
  case inv =>
    exact ⟨fun ⟨l', r', le, ri⟩ c => ⌜QI node N (rfold M64 (vL node) (N + l) (r - l)) (t0 + 1 + bitWidth (r + N))
        l' r' le ri c⌝,
      fun ⟨_, _, le, ri⟩ c => ⌜M64.op (le.toNat : Int) (ri.toNat : Int) = rfold M64 (vL node) (N + l) (r - l) ∧
        c ≤ t0 + 2 + bitWidth (r + N)⌝,
      fun ⟨_, r', _, _⟩ => r'.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · have E := exit_vc _ _ _ _ _ _ _ _ _ ‹QI _ _ _ _ _ _ _ _ _› ‹_ ≤ _›
    exact ⟨E.1, by omega⟩
  all_goals (try (rename_i hlr hl hr
                  have S := step_vc node N hT _ _ _ _ _ _ _ ‹QI _ _ _ _ _ _ _ _ _› hlr
                  simp only [ne_eq, hl, hr, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at S
                  exact ⟨S.1, S.2.1, S.2.2⟩))
  · exact init_vc node N hT hsz hN30 l r hlr hr _ _ (by omega)
  · obtain ⟨h1, h2⟩ := ‹M64.op _ _ = _ ∧ _›
    exact ⟨h1, h2⟩

theorem vL_set (node : Array UInt64) (i : Int) (x : UInt64) :
    vL (set node i x) = (vL node).set i.toNat (x.toNat : Int) := by
  unfold vL Proofs.Cpp.set; simp [Array.set!, Array.toList_setIfInBounds, List.map_set]

theorem vL_length (node : Array UInt64) : (vL node).length = node.size := by simp [vL]

/-- The update loop: the tree is consistent off the path from `i` to the root, the leaves are the new leaves. -/
def UI (node0 : Array UInt64) (N p : Nat) (val : UInt64) (C : Nat) (nd : Array UInt64) (i : Int) (c : Nat) : Prop :=
  0 ≤ i ∧ i < N ∧ nd.size = 2 * N ∧ SInv M64 (vL nd) N i.toNat ∧
    (∀ k, N ≤ k → (vL nd).getD k 0 = ((vL node0).set p (val.toNat : Int)).getD k 0) ∧ c + bitWidth i.toNat ≤ C

theorem set_step (node0 : Array UInt64) (N p : Nat) (val : UInt64) (C : Nat) (nd : Array UInt64) (i : Int) (c : Nat)
    (I : UI node0 N p val C nd i c) (h1 : 1 ≤ i) :
    UI node0 N p val C (set nd i (get nd (2 * i) + get nd (2 * i + 1))) (div i 2) (c + 1) ∧ div i 2 < i := by
  obtain ⟨h0, hiN, hs, hS, hleaf, hc⟩ := I
  have hlen : (vL nd).length = 2 * N := by rw [vL_length, hs]
  have S := sinv_step M64 (vL nd) N i.toNat hS (by omega) (by omega) hlen
  have hv : vL (set nd i (get nd (2 * i) + get nd (2 * i + 1))) =
      (vL nd).set i.toNat (M64.op ((vL nd).getD (2 * i.toNat) 0) ((vL nd).getD (2 * i.toNat + 1) 0)) := by
    rw [vL_set, add_val, get_val nd _ (by omega), get_val nd _ (by omega),
      show (2 * i).toNat = 2 * i.toNat by omega, show (2 * i + 1).toNat = 2 * i.toNat + 1 by omega]
  obtain ⟨hd1, hd2⟩ := div2 i h0
  have hbw := bitWidth_div_two i.toNat (by omega)
  refine ⟨⟨hd2, by omega, by simp [hs], by rw [hv, hd1]; exact S, fun k hk => ?_, by rw [hd1]; omega⟩, by omega⟩
  rw [hv, getD_setE, if_neg (by omega)]; exact hleaf k hk

theorem set_exit (node0 : Array UInt64) (N p : Nat) (val : UInt64) (C : Nat) (nd : Array UInt64) (i : Int) (c : Nat)
    (I : UI node0 N p val C nd i c) (h1 : i < 1) (hN : 0 < N) :
    TInv M64 (vL nd) N ∧ (∀ k, N ≤ k → (vL nd)[k]?.getD 0 = ((vL node0).set p (val.toNat : Int))[k]?.getD 0) ∧
      c + 1 ≤ C + 1 := by
  obtain ⟨h0, hiN, hs, hS, hleaf, hc⟩ := I
  have e : i.toNat = 0 := by omega
  rw [e] at hS
  refine ⟨⟨hN, by rw [vL_length, hs], sinv_zero M64 _ N hS⟩, fun k hk => ?_, by omega⟩
  have := hleaf k hk; simpa [List.getD_eq_getElem?_getD] using this

theorem set_init (node : Array UInt64) (N : Nat) (hT : TInv M64 (vL node) N) (hsz : node.size = 2 * N)
    (hN30 : N < 2 ^ 30) (idx : Nat) (hidx : idx < N) (val : UInt64) (C c : Nat) (hc : c + bitWidth N ≤ C) :
    UI node N (idx + N) val C (set node ((idx : Int) + div (size node) 2) val) (div ((idx : Int) + div (size node) 2) 2) c ∧
      div ((idx : Int) + div (size node) 2) 2 < 18446744073709551616 := by
  have hd : div (size node) 2 = (N : Int) := by
    simp only [div, size, hsz]; push_cast; exact Int.mul_tdiv_cancel_left _ (by decide)
  rw [hd]
  obtain ⟨hd1, hd2⟩ := div2 ((idx : Int) + N) (by omega)
  have e : ((idx : Int) + N).toNat = idx + N := by omega
  rw [e] at hd1
  have hbw := bitWidth_mono (show (idx + N) / 2 ≤ N by omega)
  refine ⟨⟨hd2, by omega, by simp [hsz], ?_, fun k hk => ?_, by rw [hd1]; omega⟩, by omega⟩
  · rw [vL_set, e, hd1]; exact sinv_init M64 _ N _ _ hT (by omega) (by omega)
  · rw [vL_set, e]

theorem segtree_sum_set_spec (node : Array UInt64) (N : Nat) (hT : TInv M64 (vL node) N) (hN30 : N < 2 ^ 30)
    (idx : Nat) (hidx : idx < N) (val : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.segtree_sum_set node idx val
    ⦃⇓ res c => ⌜TInv M64 (vL res) N ∧
      (∀ k, N ≤ k → (vL res).getD k 0 = ((vL node).set (idx + N) (val.toNat : Int)).getD k 0) ∧
      c ≤ t0 + 2 + bitWidth N⌝⦄ := by
  have hsz : node.size = 2 * N := by have := hT.2.1; simpa [vL] using this
  mvcgen [cp.segtree_sum_set]
  case inv =>
    exact ⟨fun ⟨nd, i⟩ c => ⌜UI node N (idx + N) val (t0 + 1 + bitWidth N) nd i c⌝,
      fun ⟨nd, _⟩ c => ⌜TInv M64 (vL nd) N ∧
        (∀ k, N ≤ k → (vL nd).getD k 0 = ((vL node).set (idx + N) (val.toNat : Int)).getD k 0) ∧
        c ≤ t0 + 2 + bitWidth N⌝,
      fun ⟨_, i⟩ => i.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · have E := set_exit _ _ _ _ _ _ _ _ ‹UI _ _ _ _ _ _ _ _› ‹_ < (1 : Int)› hT.1
    exact ⟨E.1, E.2.1, by omega⟩
  · have S := set_step _ _ _ _ _ _ _ _ ‹UI _ _ _ _ _ _ _ _› ‹(1 : Int) ≤ _›
    exact ⟨S.1, S.2, by have := ‹(1 : Int) ≤ _›; omega⟩
  · exact set_init node N hT hsz hN30 idx hidx val _ _ (by omega)
  · exact ‹_ ∧ _›

end Proofs.Cpp.SegtreeSum
