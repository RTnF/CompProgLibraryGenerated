import Proofs.Cpp.Gen.TopologicalSort
import Proofs.Cpp.Lib.Basic
import Proofs.TopoSortMath
import Proofs.TreeRootMath

/-! # `topological_sort` (library/graph/topological_sort.hpp)

Kahn's algorithm on CSR arrays. The three translated loops count the in-degrees, enqueue the sources (`F`), and
run the queue; the arrays follow the pure model of `Proofs.TopoSortMath` (`initSt`, `kahnL`, `decr`; relation `Rel`),
whose `kahn_final` gives the order's properties. The inner loop looks at the edges of the dequeued vertices, at most
all `m` edges (`W_le`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.TopoSortMath

namespace Proofs.Cpp.TopologicalSort

def natL (a : Array Int) : List Nat := a.toList.map Int.toNat

theorem natL_getD (a : Array Int) (k : Nat) : (natL a).getD k 0 = (a[k]!).toNat := by
  unfold natL
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

/-- The arrays `indeg`, `order`, `qt` hold the model state `st` (counters, queue). -/
def Rel (n : Nat) (st : List Nat × List Nat) (indeg order : Array Int) (qt : Int) : Prop :=
  indeg.size = n ∧ (∀ w : Nat, w < n → indeg[w]! = (st.1.getD w 0 : Int)) ∧ order.size = n ∧
    qt = (st.2.length : Int) ∧ ∀ j : Nat, j < st.2.length → order[j]! = (st.2.getD j 0 : Int)

theorem natL_length (a : Array Int) : (natL a).length = a.size := by simp [natL]

theorem target_val (target : Array Int) (htarget : ∀ k : Nat, 0 ≤ target[k]!) (k : Nat) :
    get target (k : Int) = (((natL target).getD k 0 : Nat) : Int) := by
  rw [get_eq, natL_getD]; simp; have := htarget k; omega

theorem take_succ_getD (l : List Nat) (k : Nat) (hk : k < l.length) : l.take (k + 1) = l.take k ++ [l.getD k 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- One step of the counting loop. -/
theorem count_step (target : Array Int) (n : Nat) (hT : ∀ x ∈ natL target, x < n)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (d : Array Int) (L : Nat) (hL : L < target.size)
    (h : d.size = n ∧ ∀ w : Nat, w < n → d[w]! = (((natL target).take L).count w : Int)) :
    (set d (get target (L : Int)) (get d (get target (L : Int)) + 1)).size = n ∧
    ∀ w : Nat, w < n → (set d (get target (L : Int)) (get d (get target (L : Int)) + 1))[w]! =
      (((natL target).take (L + 1)).count w : Int) := by
  obtain ⟨hs, hc⟩ := h
  have hL' : L < (natL target).length := by rw [natL_length]; exact hL
  set x := (natL target).getD L 0 with hx
  have hxn : x < n := hT x (by rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL']; simp)
  rw [target_val target htarget L, ← hx, take_succ_getD _ _ hL', ← hx]
  refine ⟨by simp [hs], fun w hw => ?_⟩
  rw [getElemBang_set _ _ _ _ (by simp; omega), List.count_append, List.count_singleton]
  by_cases hwx : w = x
  · subst hwx; simp [get_eq, hc _ hw]
  · rw [if_neg (by simp; omega), hc w hw]; simp [Ne.symm hwx]

/-- The vertices `< i` without predecessors, in order. -/
def F (target : Array Int) (i : Nat) : List Nat := (List.range i).filter (fun w => (natL target).count w = 0)

theorem enq_step (target : Array Int) (n : Nat) (d o : Array Int) (q : Int) (L : Nat) (hLn : L < n)
    (hd : d.size = n ∧ ∀ w : Nat, w < n → d[w]! = (((natL target).take (natL target).length).count w : Int))
    (h : o.size = n ∧ q = ((F target L).length : Int) ∧ ∀ j : Nat, j < (F target L).length →
      o[j]! = ((F target L).getD j 0 : Int)) :
    (get d (L : Int) = 0 → (set o q (L : Int)).size = n ∧ q + 1 = ((F target (L + 1)).length : Int) ∧
        ∀ j : Nat, j < (F target (L + 1)).length → (set o q (L : Int))[j]! = ((F target (L + 1)).getD j 0 : Int)) ∧
    (¬get d (L : Int) = 0 → o.size = n ∧ q = ((F target (L + 1)).length : Int) ∧
        ∀ j : Nat, j < (F target (L + 1)).length → o[j]! = ((F target (L + 1)).getD j 0 : Int)) := by
  obtain ⟨hs, hq, he⟩ := h
  have hdL : get d (L : Int) = (((natL target).count L : Nat) : Int) := by
    rw [get_eq, Int.toNat_natCast, hd.2 L hLn, List.take_length]
  have hF : F target (L + 1) = F target L ++ (if (natL target).count L = 0 then [L] else []) := by
    simp [F, List.range_succ, List.filter_append, List.filter_singleton]
  have hlenF : (F target L).length ≤ L := by
    unfold F; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  rw [hdL]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have h0' : (natL target).count L = 0 := by exact_mod_cast h0
    rw [hF, if_pos h0']
    refine ⟨by simp [hs], by simp; omega, fun j hj => ?_⟩
    simp only [List.length_append, List.length_singleton] at hj
    rw [getElemBang_set _ _ _ _ (by omega)]
    by_cases hjq : j = q.toNat
    · rw [if_pos hjq]; simp [List.getD_eq_getElem?_getD, show j = (F target L).length by omega]
    · rw [if_neg hjq, he j (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < (F target L).length by omega)]
  · have h0' : ¬(natL target).count L = 0 := by intro h; apply h0; exact_mod_cast h
    rw [hF, if_neg h0', List.append_nil]
    exact ⟨hs, hq, he⟩

section Kahn
variable (head target : Array Int) (n : Nat)

/-- The model state after `L` steps of the main loop. -/
abbrev K (L : Nat) : List Nat × List Nat := kahnL (natL head) (natL target) L (initSt (natL target) n)

/-- The vertex taken from the queue at step `L`. -/
abbrev V (L : Nat) : Nat := (K head target n L).2.getD L 0

/-- The model state after the first `d` edges of `V L`. -/
abbrev innerS (L d : Nat) : List Nat × List Nat :=
  ((outL (natL head) (natL target) (V head target n L)).take d).foldl (fun s w => decr w s) (K head target n L)

/-- The work of the inner loop in the first `L` steps. -/
def W : Nat → Nat
  | 0 => 0
  | L + 1 => W L + if L < (K head target n L).2.length
      then (outL (natL head) (natL target) (V head target n L)).length else 0

end Kahn

section Steps
variable {head target : Array Int} {n : Nat}

theorem fold_inv (S : List Nat) : ∀ (d : Nat) (rest : List Nat) (st : List Nat × List Nat),
    d ≤ rest.length → (∀ x ∈ rest, x < n) → Inv (natL head) (natL target) n S rest st →
    Inv (natL head) (natL target) n S (rest.drop d) ((rest.take d).foldl (fun s w => decr w s) st) := by
  intro d
  induction d with
  | zero => intro rest st _ _ I; simpa using I
  | succ d ih =>
    intro rest st hd hlt I
    cases rest with
    | nil => simp at hd
    | cons w r =>
      simp only [List.take_succ_cons, List.foldl_cons, List.drop_succ_cons]
      exact ih r _ (by simp at hd; omega) (fun x hx => hlt x (by simp [hx]))
        (decr_inv _ _ n S w r st (hlt w (by simp)) I)

theorem outL_len (H : HeadOK (natL head) (natL target) n) (v : Nat) (hv : v < n) :
    (outL (natL head) (natL target) v).length = (natL head).getD (v + 1) 0 - (natL head).getD v 0 := by
  have h1 := HeadOK.le _ _ n H n (Nat.le_refl n) (v + 1) (by omega)
  rw [H.last] at h1
  unfold outL; rw [List.length_take, List.length_drop]; omega

theorem head_val (hhead : ∀ k : Nat, 0 ≤ head[k]!) (k : Nat) : get head (k : Int) = (((natL head).getD k 0 : Nat) : Int) := by
  rw [get_eq, natL_getD]; simp; have := hhead k; omega

theorem K_inv (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n) (L : Nat) :
    Inv0 (natL head) (natL target) n L (K head target n L) :=
  kahnL_inv _ _ n hT _ (init_inv _ _ n H hT) L

/-- The facts about the edge `j` of the vertex taken at step `L`. -/
theorem edge_facts (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (L : Nat) (d0 o0 : Array Int) (q0 : Int) (RO : Rel n (K head target n L) d0 o0 q0) (hlt : (L : Int) < q0)
    (prefI suff : List Int)
    (hr : range 0 (get head (get o0 L + 1) - get head (get o0 L)) = prefI ++ (prefI.length : Int) :: suff) :
    L < (K head target n L).2.length ∧ get o0 L = (V head target n L : Int) ∧ V head target n L < n ∧
    prefI.length < (outL (natL head) (natL target) (V head target n L)).length ∧
    get target (get head (get o0 L) + prefI.length) =
      (((outL (natL head) (natL target) (V head target n L)).getD prefI.length 0 : Nat) : Int) := by
  obtain ⟨-, -, -, hq, he⟩ := RO
  have hL : L < (K head target n L).2.length := by omega
  have hv : get o0 L = (V head target n L : Int) := by rw [get_eq, Int.toNat_natCast, he L hL]
  have hVn : V head target n L < n := (K_inv H hT L).lt _ (by
    unfold V; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL]; simp)
  have hl := range_prefix_length hr
  rw [hv, show (V head target n L : Int) + 1 = ((V head target n L + 1 : Nat) : Int) by simp,
    head_val hhead, head_val hhead] at hl
  have hlen := outL_len H _ hVn
  simp only [Int.sub_zero] at hl
  refine ⟨hL, hv, hVn, by omega, ?_⟩
  rw [hv, head_val hhead, outL_getD _ _ _ _ (by omega), ← Nat.cast_add, target_val target htarget]

/-- One edge of the inner loop: the arrays follow `decr`. -/
theorem decr_step (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (L : Nat) (d0 o0 : Array Int) (q0 : Int) (RO : Rel n (K head target n L) d0 o0 q0) (hlt : (L : Int) < q0)
    (prefI suff : List Int)
    (hr : range 0 (get head (get o0 L + 1) - get head (get o0 L)) = prefI ++ (prefI.length : Int) :: suff)
    (dd o : Array Int) (q : Int) (RI : Rel n (innerS head target n L prefI.length) dd o q) :
    let w := get target (get head (get o0 L) + prefI.length)
    let dd' := set dd w (get dd w - 1)
    (get dd' w = 0 → Rel n (innerS head target n L (prefI.length + 1)) dd' (set o q w) (q + 1)) ∧
    (¬get dd' w = 0 → Rel n (innerS head target n L (prefI.length + 1)) dd' o q) := by
  intro w dd'
  obtain ⟨hL, hv, hVn, hj, hw⟩ := edge_facts H hT hhead htarget L d0 o0 q0 RO hlt prefI suff hr
  set V := V head target n L
  set j := prefI.length
  set ol := outL (natL head) (natL target) V
  set x := ol.getD j 0 with hx
  set st := K head target n L
  set st' := innerS head target n L j with hst'
  have I0 := K_inv H hT L
  have Ipre := step_pre _ _ n L st I0 hL
  have hVeq : st.2[L] = V := by
    show st.2[L] = (K head target n L).2.getD L 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL]; rfl
  rw [hVeq] at Ipre
  have Ij : Inv (natL head) (natL target) n (st.2.take (L + 1)) (ol.drop j) st' :=
    fold_inv (head := head) (target := target) _ j ol st (by omega) (outL_lt (natL head) _ n hT V) Ipre
  have hdrop : ol.drop j = x :: ol.drop (j + 1) := by
    rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.drop_eq_getElem_cons hj
  rw [hdrop] at Ij
  have hxn : x < n := outL_lt (natL head) _ n hT V x (by
    rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact List.getElem_mem hj)
  have Ij1 := decr_inv _ _ n _ x _ st' hxn Ij
  have hst1 : innerS head target n L (j + 1) = decr x st' := by
    show (ol.take (j + 1)).foldl _ st = _
    rw [fold_take_succ _ _ _ _ hj]
    rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hc := Ij.cnt x hxn
  simp only [List.count_cons_self] at hc
  have hy : 1 ≤ st'.1.getD x 0 := by omega
  have hlen1 := Inv.ord_len _ _ n _ _ _ Ij1
  obtain ⟨hs, hdv, ho, hq, he⟩ := RI
  have hwx : w = (x : Int) := hw
  have gdd : get dd w = (st'.1.getD x 0 : Int) := by rw [hwx, get_eq, Int.toNat_natCast, hdv x hxn]
  have hlenx : x < st'.1.length := by rw [Ij.len]; exact hxn
  have hw' : w.toNat = x := by rw [hwx]; simp
  have gset : get dd' w = get dd w - 1 := by
    simp only [dd']; rw [get_eq, getElemBang_set _ _ _ _ (by rw [hw']; omega), if_pos rfl]
  have gdd' : get dd' w = ((st'.1.getD x 0 - 1 : Nat) : Int) := by
    rw [gset, gdd]; omega
  have hset : ∀ w' : Nat, w' < n → dd'[w']! = ((decr x st').1.getD w' 0 : Int) := by
    intro w' hwn
    simp only [dd', decr]
    rw [getElemBang_set _ _ _ _ (by rw [hw']; omega), gdd, hw']
    by_cases h : w' = x
    · subst h
      rw [if_pos rfl]; simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hlenx, Option.getD_some]
      have hy' := hy; rw [List.getD_eq_getElem?_getD] at hy'
      omega
    · simp only [Int.toNat_natCast, h, ite_false, hdv w' hwn]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]
  rw [hst1]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [gdd'] at h0
    have h0' : st'.1.getD x 0 - 1 = 0 := by exact_mod_cast h0
    have hS : (decr x st').2 = st'.2 ++ [x] := by unfold decr; rw [if_pos h0']
    rw [hS] at hlen1
    simp only [List.length_append, List.length_singleton] at hlen1
    refine ⟨by simp only [dd', size_set]; exact hs, hset, by simp only [size_set]; exact ho,
      by rw [hS, hq]; simp, fun k hk => ?_⟩
    rw [hS] at hk ⊢
    simp only [List.length_append, List.length_singleton] at hk
    rw [getElemBang_set _ _ _ _ (by omega)]
    by_cases hkq : k = q.toNat
    · rw [if_pos hkq, hwx]; simp [List.getD_eq_getElem?_getD, show k = st'.2.length by omega]
    · rw [if_neg hkq, he k (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < st'.2.length by omega)]
  · rw [gdd'] at h0
    have h0' : ¬st'.1.getD x 0 - 1 = 0 := by intro h; apply h0; rw [h]; rfl
    have hS : (decr x st').2 = st'.2 := by unfold decr; rw [if_neg h0']
    exact ⟨by simp only [dd', size_set]; exact hs, hset, ho, by rw [hS]; exact hq, by rw [hS]; exact he⟩

theorem K_succ (L : Nat) : K head target n (L + 1) = stepQ (natL head) (natL target) L (K head target n L) := by
  simp only [K, kahnL, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem inner_init (L : Nat) (d o : Array Int) (q : Int) (R : Rel n (K head target n L) d o q) :
    Rel n (innerS head target n L 0) d o q := by
  simpa [innerS] using R

theorem inner_done (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (L : Nat) (d0 o0 : Array Int) (q0 : Int)
    (RO : Rel n (K head target n L) d0 o0 q0) (hlt : (L : Int) < q0) (d o : Array Int) (q : Int)
    (RI : Rel n (innerS head target n L (range 0 (get head (get o0 L + 1) - get head (get o0 L))).length) d o q) :
    Rel n (K head target n (L + 1)) d o q ∧
      ∀ c t : Nat, c = t + L + W head target n L + 1 + (range 0 (get head (get o0 L + 1) - get head (get o0 L))).length →
        c = t + (L + 1) + W head target n (L + 1) := by
  obtain ⟨-, -, -, hq, he⟩ := RO
  have hL : L < (K head target n L).2.length := by omega
  have hv : get o0 L = (V head target n L : Int) := by rw [get_eq, Int.toNat_natCast, he L hL]
  have hVn : V head target n L < n := (K_inv H hT L).lt _ (by
    unfold V; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL]; simp)
  have hlen : (range 0 (get head (get o0 L + 1) - get head (get o0 L))).length =
      (outL (natL head) (natL target) (V head target n L)).length := by
    rw [range_length, hv, show (V head target n L : Int) + 1 = ((V head target n L + 1 : Nat) : Int) by simp,
      head_val hhead, head_val hhead, outL_len H _ hVn]
    omega
  rw [hlen] at RI ⊢
  have e : innerS head target n L (outL (natL head) (natL target) (V head target n L)).length =
      K head target n (L + 1) := by
    rw [K_succ]; unfold stepQ; rw [if_pos hL]; simp [innerS, procV, V]
  rw [e] at RI
  exact ⟨RI, fun c t hc => by rw [hc]; simp [W, hL]; omega⟩

theorem outer_skip (L : Nat) (d o : Array Int) (q : Int) (R : Rel n (K head target n L) d o q) (hge : q ≤ (L : Int)) :
    Rel n (K head target n (L + 1)) d o q ∧ W head target n (L + 1) = W head target n L := by
  have hL : ¬L < (K head target n L).2.length := by have := R.2.2.2.1; omega
  have e : K head target n (L + 1) = K head target n L := by rw [K_succ]; unfold stepQ; rw [if_neg hL]
  rw [e]; exact ⟨R, by simp [W, hL]⟩

theorem outer_init (d o : Array Int) (q : Int)
    (h1 : d.size = n ∧ ∀ w : Nat, w < n → d[w]! = (((natL target).take (natL target).length).count w : Int))
    (h2 : o.size = n ∧ q = ((F target n).length : Int) ∧
      ∀ j : Nat, j < (F target n).length → o[j]! = ((F target n).getD j 0 : Int)) :
    Rel n (K head target n 0) d o q := by
  obtain ⟨hs, hc⟩ := h1
  obtain ⟨ho, hq, he⟩ := h2
  have hK : K head target n 0 = initSt (natL target) n := rfl
  rw [hK]
  refine ⟨hs, fun w hw => ?_, ho, hq, he⟩
  rw [hc w hw, List.take_length]
  simp [initSt, List.getD_eq_getElem?_getD, hw]

end Steps

theorem topological_sort_spec (head target indeg order : Array Int) (n : Nat)
    (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (hz : indeg.size = n ∧ ∀ w : Nat, w < n → indeg[w]! = 0) (hord : order.size = n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.topological_sort head target indeg order n
    ⦃⇓ r c => ⌜Rel n (K head target n n) r.2.1 r.2.2 r.1 ∧
               c = t0 + 1 + target.size + n + n + W head target n n⌝⦄ := by
  mvcgen [cp.topological_sort]
  case inv1 =>
    exact ⇓⟨xs, d⟩ c => ⌜(d.size = n ∧ ∀ w : Nat, w < n →
      d[w]! = (((natL target).take xs.prefix.length).count w : Int)) ∧ c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    exact ⇓⟨xs, o, q⟩ c => ⌜(o.size = n ∧ q = ((F target xs.prefix.length).length : Int) ∧
      ∀ j : Nat, j < (F target xs.prefix.length).length → o[j]! = ((F target xs.prefix.length).getD j 0 : Int)) ∧
      c = t0 + 1 + target.size + xs.prefix.length⌝
  case inv3 =>
    exact ⇓⟨xs, d, o, q⟩ c => ⌜Rel n (K head target n xs.prefix.length) d o q ∧
      c = t0 + 1 + target.size + n + xs.prefix.length + W head target n xs.prefix.length⌝
  case inv4 =>
    rename_i pref _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⇓⟨ys, d, o, q⟩ c => ⌜Rel n (innerS head target n pref.length ys.prefix.length) d o q ∧
      c = t0 + 1 + target.size + n + pref.length + W head target n pref.length + 1 + ys.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 _ = _ ++ _ :: _›; simp at e; subst e))
  · obtain ⟨hI, hc⟩ := ‹(_ ∧ ∀ w < n, _) ∧ _›
    have hl0 := range_prefix_length ‹range 0 _ = _ ++ _ :: _›
    simp +zetaDelta only [size, Int.sub_zero, Int.toNat_natCast] at hl0
    have R := count_step target n hT htarget _ _ hl0 hI
    exact ⟨⟨by simpa using R.1, R.2⟩, by omega⟩
  · exact ⟨⟨hz.1, fun w hw => by simp [hz.2 w hw]⟩, ‹_›⟩
  all_goals (try (have hl := range_prefix_length ‹range 0 (n : Int) = _ ++ _ :: _›
                  simp only [Int.sub_zero, Int.toNat_natCast] at hl
                  have h1 := (‹(_ ∧ ∀ w < n, _ = ((List.count w (List.take _ (natL target)) : Nat) : Int)) ∧ _›).1
                  rw [range_length, size, Int.sub_zero, Int.toNat_natCast, ← natL_length target] at h1
                  obtain ⟨h2, hc⟩ := ‹(_ ∧ _ = ((F target _).length : Int) ∧ _) ∧ _›
                  simp only [← List.getD_eq_getElem?_getD] at h2
                  have R := enq_step target n _ _ _ _ hl h1 h2
                  simp only [List.getD_eq_getElem?_getD, size_set] at R
                  first
                  | exact ⟨R.1 ‹_›, by omega⟩
                  | exact ⟨R.2 ‹_›, by omega⟩))
  · have hc := (‹(_ ∧ ∀ w < n, _ = ((List.count w (List.take _ (natL target)) : Nat) : Int)) ∧ _›).2
    rw [range_length, size, Int.sub_zero, Int.toNat_natCast] at hc
    exact ⟨by simp [F, hord], hc⟩
  all_goals (try (have e := range_cursor ‹range 0 (n : Int) = _ ++ _ :: _›; simp at e; subst e))
  -- the inner loop
  all_goals (try (obtain ⟨RO, hc0⟩ := ‹Rel n (K _ _ _ _) _ _ _ ∧ _›
                  obtain ⟨RI, hc⟩ := ‹Rel n (innerS _ _ _ _ _) _ _ _ ∧ _›
                  have D := decr_step H hT hhead htarget _ _ _ _ RO ‹_› _ _ ‹_› _ _ _ RI
                  first
                  | exact ⟨D.1 ‹_›, by omega⟩
                  | exact ⟨D.2 ‹_›, by omega⟩))
  · obtain ⟨RO, hc⟩ := ‹Rel n (K _ _ _ _) _ _ _ ∧ _›
    exact ⟨inner_init _ _ _ _ RO, by omega⟩
  · obtain ⟨RO, hc0⟩ := ‹Rel n (K _ _ _ _) _ _ _ ∧ _›
    obtain ⟨RI, hc⟩ := ‹Rel n (innerS _ _ _ _ _) _ _ _ ∧ _›
    have D := inner_done H hT hhead _ _ _ _ RO ‹_› _ _ _ RI
    exact ⟨D.1, D.2 _ _ hc⟩
  · obtain ⟨RO, hc⟩ := ‹Rel n (K _ _ _ _) _ _ _ ∧ _›
    have D := outer_skip _ _ _ _ RO ‹_›
    exact ⟨D.1, by rw [D.2]; omega⟩
  · have h1 := (‹(_ ∧ ∀ w < n, _ = ((List.count w (List.take _ (natL target)) : Nat) : Int)) ∧ _›)
    rw [range_length, size, Int.sub_zero, Int.toNat_natCast, ← natL_length target] at h1
    obtain ⟨h2, hc⟩ := ‹(_ ∧ _ = ((F target _).length : Int) ∧ _) ∧ _›
    simp only [range_length, Int.sub_zero, Int.toNat_natCast, ← List.getD_eq_getElem?_getD] at h2 hc
    exact ⟨outer_init _ _ _ h1.1 h2, by simp [W]; omega⟩
  exact ‹_ ∧ _›

/-! ## The work: the edges of the dequeued vertices, at most all edges -/

theorem decr_prefix (w : Nat) (st : List Nat × List Nat) : st.2 <+: (decr w st).2 := by
  unfold decr; split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem fold_prefix : ∀ (l : List Nat) (st : List Nat × List Nat), st.2 <+: (l.foldl (fun s w => decr w s) st).2
  | [], _ => List.prefix_refl _
  | w :: l, st => (decr_prefix w st).trans (fold_prefix l _)

section
variable {head target : Array Int} {n : Nat}

theorem K_prefix (L : Nat) : (K head target n L).2 <+: (K head target n (L + 1)).2 := by
  rw [K_succ]; unfold stepQ; split
  · exact fold_prefix _ _
  · exact List.prefix_refl _

theorem W_eq (L : Nat) : W head target n L =
    (((K head target n L).2.take L).map (fun v => (outL (natL head) (natL target) v).length)).sum := by
  induction L with
  | zero => simp [W]
  | succ L ih =>
    by_cases h : L < (K head target n L).2.length
    · obtain ⟨ext, hext⟩ := K_prefix (head := head) (target := target) (n := n) L
      rw [W, if_pos h, ih, ← hext, List.take_succ, List.take_append_of_le_length (by omega),
        List.getElem?_append_left h, List.getElem?_eq_getElem h]
      simp [V, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.take_succ]; simp [List.getElem?_eq_getElem h]
    · have e : K head target n (L + 1) = K head target n L := by rw [K_succ]; unfold stepQ; rw [if_neg h]
      rw [W, if_neg h, ih, e, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp

theorem W_le (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n) :
    W head target n n ≤ target.size := by
  have I := K_inv H hT n
  have hlen := Inv.ord_len _ _ n _ _ _ I
  rw [W_eq, List.take_of_length_le hlen]
  have hle := Proofs.TreeRootMath.sum_nodup_le (fun v => (outL (natL head) (natL target) v).length) n _ I.nodup I.lt
  have e : ((List.range n).map (fun v => (outL (natL head) (natL target) v).length)) =
      (List.range n).map (fun v => (natL head).getD (v + 1) 0 - (natL head).getD v 0) := by
    apply List.map_congr_left; intro v hv; exact outL_len H v (List.mem_range.mp hv)
  rw [e] at hle
  have htel := Proofs.TreeRootMath.sum_outdeg (natL head) n H.mono
  rw [H.last, H.zero, natL_length] at htel
  omega

end

/-- `topological_sort(head, target, indeg, order, n)` on CSR arrays (`HeadOK`, heads in `[0, n)`, `indeg` all zero):
the returned `k` and `order[0 .. k)` are the queue `Q` of Kahn's algorithm. `Q` has distinct vertices; every
in-neighbour of `Q[j]` appears before `j`; every vertex outside `Q` has an in-neighbour outside `Q` (so `k < n` exactly
when there is a cycle); at most `1 + 2n + 2m` steps for `m` edges. -/
theorem topological_sort_correct (head target indeg order : Array Int) (n : Nat)
    (H : HeadOK (natL head) (natL target) n) (hT : ∀ x ∈ natL target, x < n)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (hz : indeg.size = n ∧ ∀ w : Nat, w < n → indeg[w]! = 0) (hord : order.size = n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.topological_sort head target indeg order n
    ⦃⇓ r c => ⌜∃ Q : List Nat, r.1 = Q.length ∧ (∀ j : Nat, j < Q.length → r.2.2[j]! = (Q.getD j 0 : Int)) ∧
        Q.Nodup ∧ (∀ x ∈ Q, x < n) ∧
        (∀ j (hj : j < Q.length), ∀ u, u < n → Q[j] ∈ outL (natL head) (natL target) u → u ∈ Q.take j) ∧
        (∀ w, w < n → w ∉ Q → ∃ u, u < n ∧ u ∉ Q ∧ w ∈ outL (natL head) (natL target) u) ∧
        c ≤ t0 + 1 + 2 * n + 2 * target.size⌝⦄ := by
  obtain ⟨r, c, hrun, R, hc⟩ := run_of_triple (topological_sort_spec head target indeg order n H hT hhead htarget hz hord t0)
  apply triple_of_run r c hrun
  have F := kahn_final _ _ n hT _ (init_inv _ _ n H hT)
  obtain ⟨hnd, hlt, -, hj, hout⟩ := F
  have hW := W_le (head := head) (target := target) H hT
  exact ⟨(K head target n n).2, R.2.2.2.1, R.2.2.2.2, hnd, hlt, hj, hout, by omega⟩

end Proofs.Cpp.TopologicalSort
