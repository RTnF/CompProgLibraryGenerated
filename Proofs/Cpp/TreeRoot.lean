import Proofs.Cpp.Gen.TreeRoot
import Proofs.Cpp.Lib.Basic
import Proofs.Math.TreeRootMath

/-! # `tree_root` (library/tree/tree_root.hpp)

Rooting by an iterative depth-first search. The translated loops keep the arrays equal to the state of the pure model
`runL` of `Proofs.TreeRootMath` together with the ghost list of popped vertices and the farthest vertex (`RelS`,
`runA`); the model's `TreeSpec` and `FarSpec` then describe the result, and the work is at most all `m` arcs. The
theorem is stated for `Cost = long long` (`Int`), the instance of the differential test. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.TreeRootMath

namespace Proofs.Cpp.TreeRoot

def natL (a : Array Int) : List Nat := a.toList.map Int.toNat

abbrev HL (head : Array Int) : List Nat := natL head
abbrev TL (target : Array Int) : List Nat := natL target

/-- One step of the model together with the ghost list of popped vertices and the farthest vertex. -/
def stepA (head target cost : Array Int) (x : St × List Nat × Nat) : St × List Nat × Nat :=
  (step (natL head) (natL target) cost.toList x.1, stepD x.1 x.2.1, stepF x.1 x.2.2)

def runA (head target cost : Array Int) (x0 : St × List Nat × Nat) : Nat → St × List Nat × Nat
  | 0 => x0
  | k + 1 => stepA head target cost (runA head target cost x0 k)

/-- The arrays hold the model state `st` and the farthest vertex `F`. -/
def RelS (n : Nat) (st : St) (F : Nat) (p d c s : Array Int) (sp : Int) : Prop :=
  p.toList = st.par ∧ d.toList = st.dep ∧ c.toList = st.cd ∧ s.size = n + 1 ∧ sp = (st.S.length : Int) ∧
    (∀ j : Nat, j < st.S.length → s[j]! = (st.S.getD j 0 : Int)) ∧ s[n]! = (F : Int)

/-- The work of the popped vertices `D`: their arcs. -/
def work (head : Array Int) (D : List Nat) : Nat := (D.map (fun v => (arcs (natL head) v).length)).sum

/-- The model state inside the inner loop: the top `V` popped and its first `j` arcs looked at. -/
def innerSt (head target cost : Array Int) (st : St) (V j : Nat) : St :=
  ((arcs (natL head) V).take j).foldl (fun s p => relax (natL target) cost.toList V p s) { st with S := st.S.dropLast }

def init0 (parent depth cd : Array Int) (root : Nat) : St × List Nat × Nat :=
  (initSt parent.toList depth.toList cd.toList root, [], root)

abbrev Top (st : St) : Nat := st.S.getLast?.getD 0

section Model
variable (head target cost : Array Int)

theorem runA_fst (x0 : St × List Nat × Nat) (k : Nat) :
    (runA head target cost x0 k).1 = runL (natL head) (natL target) cost.toList k x0.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runA, stepA]; rw [ih, runL_succ]

/-- The model's precondition, in the form of `Proofs.TreeRootMath`. -/
structure Pre (target cost parent depth cd : Array Int) (n root Cb : Nat) : Prop where
  hT : ∀ q, (natL target).getD q 0 < n
  hC : ∀ q, (cost.toList.getD q 0).natAbs ≤ Cb
  hroot : root < n
  hP : parent.size = n
  hD : depth.size = n
  hCd : cd.size = n
  hneg : ∀ v, v < n → parent.toList.getD v 0 < 0

variable {head target cost}

theorem runA_inv {parent depth cd : Array Int} {n root Cb : Nat} (P : Pre target cost parent depth cd n root Cb)
    (k : Nat) :
    InvK (natL head) (natL target) cost.toList n root Cb k (runA head target cost (init0 parent depth cd root) k).1 ∧
      GInv2 (runA head target cost (init0 parent depth cd root) k).1
        (runA head target cost (init0 parent depth cd root) k).2.1
        (runA head target cost (init0 parent depth cd root) k).2.2 := by
  have I0 : InvK (natL head) (natL target) cost.toList n root Cb 0 (initSt parent.toList depth.toList cd.toList root) :=
    ⟨initInv _ _ _ n root Cb _ _ _ P.hroot (by simp [P.hP]) (by simp [P.hD]) (by simp [P.hCd]) P.hneg,
      by simp [initSt], fun _ => by simp [initSt]⟩
  have K := runL_inv _ _ _ n root Cb P.hT P.hC _ I0
  refine ⟨by rw [runA_fst]; exact K k, ?_⟩
  induction k with
  | zero => exact ginv2_init _ _ _ root
  | succ k ih =>
    have hk : InvK (natL head) (natL target) cost.toList n root Cb k
        (runA head target cost (init0 parent depth cd root) k).1 := by rw [runA_fst]; exact K k
    exact ginv2_step _ _ _ n root Cb P.hT P.hC _ _ _ hk.I ih

theorem innerSt_succ (st : St) (V j : Nat) (hj : j < (arcs (natL head) V).length) :
    innerSt head target cost st V (j + 1) =
      relax (natL target) cost.toList V ((natL head).getD V 0 + j) (innerSt head target cost st V j) := by
  unfold innerSt
  rw [List.take_succ, List.getElem?_eq_getElem hj, List.foldl_append]
  simp [arcs]

theorem innerSt_full (st : St) (V : Nat) :
    innerSt head target cost st V (arcs (natL head) V).length = procV (natL head) (natL target) cost.toList V st := by
  simp [innerSt, procV]

theorem relax_S_le (V p : Nat) (st : St) :
    st.S.length ≤ (relax (natL target) cost.toList V p st).S.length := by
  unfold relax; split <;> simp

theorem foldl_S_le (V : Nat) : ∀ (l : List Nat) (st : St),
    st.S.length ≤ (l.foldl (fun s p => relax (natL target) cost.toList V p s) st).S.length := by
  intro l
  induction l with
  | nil => intro st; exact Nat.le_refl _
  | cons a l ih => intro st; exact Nat.le_trans (relax_S_le V a st) (ih _)

theorem innerSt_le_full (st : St) (V j : Nat) :
    (innerSt head target cost st V j).S.length ≤
      (procV (natL head) (natL target) cost.toList V st).S.length := by
  unfold procV innerSt
  conv => rhs; rw [← List.take_append_drop j (arcs (natL head) V), List.foldl_append]
  exact foldl_S_le V _ _

theorem step_some (st : St) (h : st.S ≠ []) :
    step (natL head) (natL target) cost.toList st =
      procV (natL head) (natL target) cost.toList (Top st) st := by
  unfold step
  obtain ⟨S0, x, hx⟩ := List.eq_nil_or_concat st.S |>.resolve_left h
  rw [hx]; simp [Top, hx]

/-- The stack never holds more than `n` vertices. -/
theorem S_len_le {n root Cb : Nat} (st : St) (I : Inv (natL head) (natL target) cost.toList n root Cb st) :
    st.S.length ≤ n := by
  have hsub : st.S ⊆ List.range n := fun x hx => List.mem_range.mpr (I.B.Llt x (I.B.Ssub x hx))
  simpa using List.Nodup.length_le_of_subset I.B.Snd hsub

end Model

theorem toList_set (a : Array Int) (i : Int) (x : Int) : (set a i x).toList = a.toList.set i.toNat x := by
  unfold Proofs.Cpp.set; simp [Array.set!, Array.toList_setIfInBounds]

theorem get_toList (a : Array Int) (i : Int) : get a i = a.toList.getD i.toNat 0 := by
  rw [get_eq]
  by_cases h : i.toNat < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a i.toNat h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a i.toNat h]

theorem natL_getD (a : Array Int) (k : Nat) : (natL a).getD k 0 = (a[k]!).toNat := by
  unfold natL
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

section Arrays
variable {head target cost : Array Int}

/-- Looking at the arc `a` (index expression `q`, head `w`) of the vertex `V` (value `v`): the arrays follow `relax`. -/
theorem relax_rel (n : Nat) (st : St) (F V a : Nat) (p d c s : Array Int) (sp v w q : Int)
    (R : RelS n st F p d c s sp) (hv : v = V) (hw : w = ((natL target).getD a 0 : Int))
    (hq : get cost q = cost.toList.getD a 0) (hlen : st.S.length < n) :
    (get p w < 0 → RelS n (relax (natL target) cost.toList V a st) F (set p w v) (set d w (get d v + 1))
        (set c w (get c v + get cost q)) (set s sp w) (sp + 1)) ∧
    (¬get p w < 0 → RelS n (relax (natL target) cost.toList V a st) F p d c s sp) := by
  obtain ⟨hp, hd, hc, hs, hsp, hS, hF⟩ := R
  have hcond : get p w < 0 ↔ st.par.getD ((natL target).getD a 0) 0 < 0 := by
    rw [get_toList, hp, hw, Int.toNat_natCast]
  refine ⟨fun hneg => ?_, fun hneg => ?_⟩
  · unfold relax
    rw [if_pos (hcond.mp hneg)]
    have hw' : w.toNat = (natL target).getD a 0 := by rw [hw]; simp
    refine ⟨by rw [toList_set, hp, hw', hv], by rw [toList_set, hd, hw', get_toList, hd, hv]; simp,
      by rw [toList_set, hc, hw', get_toList, hc, hq, hv]; simp, by simp [hs], by simp [hsp], fun j hj => ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hj
      rw [getElemBang_set _ _ _ _ (by omega)]
      by_cases hjs : j = sp.toNat
      · rw [if_pos hjs, hw]
        have : j = st.S.length := by omega
        subst this; simp [List.getD_eq_getElem?_getD]
      · rw [if_neg hjs, hS j (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < st.S.length by omega)]
    · rw [getElemBang_set _ _ _ _ (by omega), if_neg (by omega)]; exact hF
  · unfold relax
    rw [if_neg (fun h => hneg (hcond.mpr h))]
    exact ⟨hp, hd, hc, hs, hsp, hS, hF⟩

end Arrays

section Steps
variable {head target cost parent depth cd : Array Int} {n root Cb : Nat}

abbrev X (head target cost parent depth cd : Array Int) (root L : Nat) : St × List Nat × Nat :=
  runA head target cost (init0 parent depth cd root) L

/-- Popping: the value read from the stack is the model's top, a vertex. -/
theorem pop_facts (P : Pre target cost parent depth cd n root Cb) (L : Nat) (p0 d0 c0 s0 : Array Int) (sp0 : Int)
    (hO : RelS n (X head target cost parent depth cd root L).1 (X head target cost parent depth cd root L).2.2
      p0 d0 c0 s0 sp0) (hpos : 0 < sp0) :
    (X head target cost parent depth cd root L).1.S ≠ [] ∧
    get s0 (sp0 - 1) = (Top (X head target cost parent depth cd root L).1 : Int) ∧
    Top (X head target cost parent depth cd root L).1 < n := by
  set st := (X head target cost parent depth cd root L).1
  obtain ⟨-, -, -, hs, hsp, hS, -⟩ := hO
  have hne : st.S ≠ [] := by intro h; rw [h] at hsp; simp at hsp; omega
  have hlast : Top st = st.S.getD (st.S.length - 1) 0 := by
    unfold Top; rw [List.getLast?_eq_getElem?]; simp [List.getD_eq_getElem?_getD]
  have I := (runA_inv (head := head) P L).1.I
  have hmem : Top st ∈ st.S := by
    rw [hlast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := List.length_pos_iff.mpr hne; omega)]
    simp
  refine ⟨hne, ?_, I.B.Llt _ (I.B.Ssub _ hmem)⟩
  rw [get_eq, show (sp0 - 1).toNat = st.S.length - 1 by omega, hS _ (by have := List.length_pos_iff.mpr hne; omega),
    hlast]

theorem head_val (hhead : ∀ k : Nat, 0 ≤ head[k]!) (V : Nat) : get head (V : Int) = ((natL head).getD V 0 : Int) := by
  rw [get_eq, natL_getD]; simp; have := hhead V; omega

theorem deg_eq (hhead : ∀ k : Nat, 0 ≤ head[k]!) (V : Nat) :
    (get head ((V : Int) + 1) - get head (V : Int)).toNat = (arcs (natL head) V).length := by
  rw [show (V : Int) + 1 = ((V + 1 : Nat) : Int) by simp, head_val hhead, head_val hhead]
  simp [arcs]

theorem inner_step (P : Pre target cost parent depth cd n root Cb) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (L : Nat) (p0 d0 c0 s0 : Array Int) (sp0 : Int)
    (hO : RelS n (X head target cost parent depth cd root L).1 (X head target cost parent depth cd root L).2.2
      p0 d0 c0 s0 sp0) (hpos : 0 < sp0) (pref suff : List Int) (cur : Int)
    (hr : range 0 (get head (get s0 (sp0 - 1) + 1) - get head (get s0 (sp0 - 1))) = pref ++ cur :: suff)
    (p d c s : Array Int) (sp : Int)
    (hI : RelS n (innerSt head target cost (X head target cost parent depth cd root L).1
      (Top (X head target cost parent depth cd root L).1) pref.length) (X head target cost parent depth cd root L).2.2
      p d c s sp) :
    (get p (get target (get head (get s0 (sp0 - 1)) + cur)) < 0 →
      RelS n (innerSt head target cost (X head target cost parent depth cd root L).1
        (Top (X head target cost parent depth cd root L).1) (pref.length + 1)) (X head target cost parent depth cd root L).2.2
        (set p (get target (get head (get s0 (sp0 - 1)) + cur)) (get s0 (sp0 - 1)))
        (set d (get target (get head (get s0 (sp0 - 1)) + cur)) (get d (get s0 (sp0 - 1)) + 1))
        (set c (get target (get head (get s0 (sp0 - 1)) + cur))
          (get c (get s0 (sp0 - 1)) + get cost (get head (get s0 (sp0 - 1)) + cur)))
        (set s sp (get target (get head (get s0 (sp0 - 1)) + cur))) (sp + 1)) ∧
    (¬get p (get target (get head (get s0 (sp0 - 1)) + cur)) < 0 →
      RelS n (innerSt head target cost (X head target cost parent depth cd root L).1
        (Top (X head target cost parent depth cd root L).1) (pref.length + 1)) (X head target cost parent depth cd root L).2.2
        p d c s sp) := by
  obtain ⟨hne, hv, hVn⟩ := pop_facts P L p0 d0 c0 s0 sp0 hO hpos
  set st := (X head target cost parent depth cd root L).1
  set V := Top st with hVd
  rw [hv] at hr ⊢
  have e := range_cursor hr
  have hl := range_prefix_length hr
  rw [Int.sub_zero, deg_eq hhead] at hl
  simp only [Int.zero_add] at e
  subst e
  set a := (natL head).getD V 0 + pref.length
  have hidx : get head (V : Int) + (pref.length : Int) = (a : Int) := by rw [head_val hhead]; simp [a]
  rw [hidx]
  have hw : get target (a : Int) = ((natL target).getD a 0 : Int) := by
    rw [get_eq, natL_getD]; simp; have := htarget a; omega
  have hq : get cost (a : Int) = cost.toList.getD a 0 := by rw [get_toList]; simp
  rw [innerSt_succ _ _ _ hl]
  have hstep : step (natL head) (natL target) cost.toList st = (X head target cost parent depth cd root (L + 1)).1 := rfl
  have I1 := (runA_inv (head := head) P (L + 1)).1.I
  rw [← hstep, step_some st hne] at I1
  have hfull := S_len_le _ I1
  rw [← hVd] at hfull
  have hle := innerSt_le_full (head := head) (target := target) (cost := cost) st V (pref.length + 1)
  rw [innerSt_succ _ _ _ hl] at hle
  constructor
  · intro hneg
    have hlen : (innerSt head target cost st V pref.length).S.length < n := by
      have hc : (innerSt head target cost st V pref.length).par.getD ((natL target).getD a 0) 0 < 0 := by
        rw [← hI.1, ← Int.toNat_natCast ((natL target).getD a 0), ← get_toList, ← hw]; exact hneg
      unfold relax at hle; rw [if_pos hc] at hle
      simp at hle; omega
    exact (relax_rel n _ _ V a p d c s sp _ _ _ hI rfl hw hq hlen).1 hneg
  · intro hneg
    unfold relax
    rw [if_neg]
    · exact hI
    · intro hc; apply hneg
      rw [hw, get_toList, hI.1]; simpa [a] using hc

end Steps

section Outer
variable {head target cost parent depth cd : Array Int} {n root Cb : Nat}

theorem pop_init (st : St) (F : Nat) (p d c s : Array Int) (sp : Int) (R : RelS n st F p d c s sp) (hpos : 0 < sp) :
    RelS n (innerSt head target cost st (Top st) 0) F p d c s (sp - 1) := by
  obtain ⟨hp, hd, hc, hs, hsp, hS, hF⟩ := R
  unfold innerSt
  simp only [List.take_zero, List.foldl_nil]
  refine ⟨hp, hd, hc, hs, by simp; omega, fun j hj => ?_, hF⟩
  simp only [List.length_dropLast] at hj
  rw [hS j (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_dropLast, show j < st.S.length - 1 by omega,
    List.getElem?_eq_getElem (show j < st.S.length by omega)]

theorem X_succ (L : Nat) : X head target cost parent depth cd root (L + 1) =
    stepA head target cost (X head target cost parent depth cd root L) := rfl

theorem pop_done (P : Pre target cost parent depth cd n root Cb) (hhead : ∀ k : Nat, 0 ≤ head[k]!) (L : Nat)
    (p0 d0 c0 s0 : Array Int) (sp0 : Int)
    (hO : RelS n (X head target cost parent depth cd root L).1 (X head target cost parent depth cd root L).2.2
      p0 d0 c0 s0 sp0) (hpos : 0 < sp0) (p d c s : Array Int) (sp : Int)
    (hI : RelS n (innerSt head target cost (X head target cost parent depth cd root L).1
      (Top (X head target cost parent depth cd root L).1)
      (range 0 (get head (get s0 (sp0 - 1) + 1) - get head (get s0 (sp0 - 1)))).length)
      (X head target cost parent depth cd root L).2.2 p d c s sp) :
    (get c s[n]! < get c (get s0 (sp0 - 1)) →
      RelS n (X head target cost parent depth cd root (L + 1)).1 (X head target cost parent depth cd root (L + 1)).2.2
        p d c (set s n (get s0 (sp0 - 1))) sp) ∧
    (¬get c s[n]! < get c (get s0 (sp0 - 1)) →
      RelS n (X head target cost parent depth cd root (L + 1)).1 (X head target cost parent depth cd root (L + 1)).2.2
        p d c s sp) ∧
    (∀ c t0 : Nat, c = t0 + 1 + L + work head (X head target cost parent depth cd root L).2.1 + 1 +
        (range 0 (get head (get s0 (sp0 - 1) + 1) - get head (get s0 (sp0 - 1)))).length →
      c = t0 + 1 + (L + 1) + work head (X head target cost parent depth cd root (L + 1)).2.1) := by
  obtain ⟨hne, hv, hVn⟩ := pop_facts P L p0 d0 c0 s0 sp0 hO hpos
  have G := (runA_inv (head := head) P L).2
  have I := (runA_inv (head := head) P L).1.I
  set x := X head target cost parent depth cd root L with hx
  set st := x.1
  set V := Top st with hVd
  rw [hv] at hI ⊢
  rw [range_length, Int.sub_zero, deg_eq hhead, innerSt_full, ← step_some st hne] at hI
  simp only [range_length, Int.sub_zero, deg_eq hhead]
  obtain ⟨I1, -, -, h4⟩ := step_inv _ _ _ n root Cb P.hT P.hC st I
  obtain ⟨v', S0, ext, hS0, -, -, -, hcd⟩ := h4 hne
  have hl' : st.S.getLast? = some v' := by rw [hS0]; simp
  have hV' : V = v' := by rw [hVd]; unfold Top; rw [hl']; rfl
  have hlastS : st.S.getLast? = some V := by rw [hl', hV']
  have hstep : X head target cost parent depth cd root (L + 1) =
      (step (natL head) (natL target) cost.toList st, x.2.1 ++ [V],
        if st.cd.getD x.2.2 0 < st.cd.getD V 0 then V else x.2.2) := by
    rw [X_succ, ← hx]; simp only [stepA, stepD, stepF]; rw [show x.1.S.getLast? = some V from hlastS]
  have hVL : V ∈ st.L := I.B.Ssub V (by rw [hS0, hV']; simp)
  have hFL : x.2.2 ∈ st.L := G.Fin
  obtain ⟨hp, hd, hc, hs, hsp, hS, hF⟩ := hI
  have cV : get c (V : Int) = st.cd.getD V 0 := by rw [get_toList, hc]; simpa using hcd V hVL
  have cF : get c s[n]! = st.cd.getD x.2.2 0 := by rw [hF, get_toList, hc]; simpa using hcd _ hFL
  have hlen := S_len_le _ I1
  rw [hstep]
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun c t0 hc => by simp [work] at hc ⊢; omega⟩
  · rw [cF, cV] at hlt
    simp only [if_pos hlt]
    refine ⟨hp, hd, hc, by simp [hs], hsp, fun j hj => ?_, ?_⟩
    · rw [getElemBang_set _ _ _ _ (by simp; omega), if_neg (by simp; omega)]; exact hS j hj
    · rw [getElemBang_set _ _ _ _ (by simp; omega), if_pos (by simp)]
  · rw [cF, cV] at hlt
    simp only [if_neg hlt]
    exact ⟨hp, hd, hc, hs, hsp, hS, hF⟩

theorem outer_skip (L : Nat) (p d c s : Array Int) (sp : Int)
    (hO : RelS n (X head target cost parent depth cd root L).1 (X head target cost parent depth cd root L).2.2
      p d c s sp) (hle : sp ≤ 0) :
    RelS n (X head target cost parent depth cd root (L + 1)).1 (X head target cost parent depth cd root (L + 1)).2.2
      p d c s sp ∧
    work head (X head target cost parent depth cd root (L + 1)).2.1 = work head (X head target cost parent depth cd root L).2.1 := by
  have hnil : (X head target cost parent depth cd root L).1.S = [] := by
    have := hO.2.2.2.2.1; apply List.eq_nil_of_length_eq_zero; omega
  have hlast : (X head target cost parent depth cd root L).1.S.getLast? = none := by rw [hnil]; rfl
  have e : X head target cost parent depth cd root (L + 1) = X head target cost parent depth cd root L := by
    rw [X_succ]; simp only [stepA, step, stepD, stepF, hlast]
  rw [e]; exact ⟨hO, rfl⟩

theorem outer_init (P : Pre target cost parent depth cd n root Cb) (stk : Array Int) (hstk : stk.size = n + 1) :
    RelS n (X head target cost parent depth cd root 0).1 (X head target cost parent depth cd root 0).2.2
      (set parent root root) (set depth root 0) (set cd root 0) (set (set stk 0 root) n root) 1 := by
  have := P.hroot
  refine ⟨by rw [toList_set]; simp [X, runA, init0, initSt], by rw [toList_set]; simp [X, runA, init0, initSt],
    by rw [toList_set]; simp [X, runA, init0, initSt], by simp [hstk], by simp [X, runA, init0, initSt],
    fun j hj => ?_, ?_⟩
  · simp [X, runA, init0, initSt] at hj; subst hj
    rw [getElemBang_set _ _ _ _ (by simp; omega), if_neg (by simp; omega), getElemBang_set _ _ _ _ (by simp; omega)]
    simp [X, runA, init0, initSt]
  · rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp [X, runA, init0]

end Outer

theorem tree_root_spec (head target cost parent depth cd stk : Array Int) (root n Cb : Nat)
    (P : Pre target cost parent depth cd n root Cb) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hstk : stk.size = n + 1) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_root (Cost := Int) head target cost parent depth cd stk root n
    ⦃⇓ r c => ⌜∃ sp, RelS n (X head target cost parent depth cd root n).1 (X head target cost parent depth cd root n).2.2
        r.1 r.2.1 r.2.2.1 r.2.2.2 sp ∧ c = t0 + 1 + n + work head (X head target cost parent depth cd root n).2.1⌝⦄ := by
  mvcgen [cp.tree_root]
  case inv1 =>
    exact ⇓⟨xs, p, d, cdv, s, sp⟩ c =>
      ⌜RelS n (runA head target cost (init0 parent depth cd root) xs.prefix.length).1
          (runA head target cost (init0 parent depth cd root) xs.prefix.length).2.2 p d cdv s sp ∧
        c = t0 + 1 + xs.prefix.length +
          work head (runA head target cost (init0 parent depth cd root) xs.prefix.length).2.1⌝
  case inv2 =>
    rename_i pref cur suff hr b _ _ _ _ _ _ _ _ s0 _ _ _ _ _ _
    exact ⇓⟨ys, p, d, cdv, s, sp⟩ c =>
      ⌜RelS n (innerSt head target cost (runA head target cost (init0 parent depth cd root) pref.length).1
            ((runA head target cost (init0 parent depth cd root) pref.length).1.S.getLast?.getD 0) ys.prefix.length)
          (runA head target cost (init0 parent depth cd root) pref.length).2.2 p d cdv s sp ∧
        c = t0 + 1 + pref.length + work head (runA head target cost (init0 parent depth cd root) pref.length).2.1 +
          1 + ys.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 (n : Int) = _ ++ _ :: _›; simp at e; subst e))
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    have hI := ‹RelS n (innerSt _ _ _ _ _ _) _ _ _ _ _ _ ∧ _›
    exact ⟨(inner_step P hhead htarget _ _ _ _ _ _ hO.1 ‹_› _ _ _ ‹_› _ _ _ _ _ hI.1).1 ‹_›, by omega⟩
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    have hI := ‹RelS n (innerSt _ _ _ _ _ _) _ _ _ _ _ _ ∧ _›
    exact ⟨(inner_step P hhead htarget _ _ _ _ _ _ hO.1 ‹_› _ _ _ ‹_› _ _ _ _ _ hI.1).2 (Int.not_lt.mpr ‹_›), by omega⟩
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    exact ⟨pop_init _ _ _ _ _ _ _ hO.1 ‹_›, hO.2⟩
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    have hI := ‹RelS n (innerSt _ _ _ _ _ _) _ _ _ _ _ _ ∧ _›
    have D := pop_done P hhead _ _ _ _ _ _ hO.1 ‹_› _ _ _ _ _ hI.1
    exact ⟨D.1 (by simpa using ‹decide _ = true›), D.2.2 _ _ hI.2⟩
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    have hI := ‹RelS n (innerSt _ _ _ _ _ _) _ _ _ _ _ _ ∧ _›
    have D := pop_done P hhead _ _ _ _ _ _ hO.1 ‹_› _ _ _ _ _ hI.1
    exact ⟨D.2.1 (by have h := ‹decide _ = false›; exact of_decide_eq_false h), D.2.2 _ _ hI.2⟩
  · have hO := ‹RelS n (runA _ _ _ _ _).1 _ _ _ _ _ _ ∧ _›
    have D := outer_skip _ _ _ _ _ _ hO.1 ‹_›
    simp only [X] at D
    exact ⟨D.1, by rw [D.2]; omega⟩
  · exact ⟨outer_init P stk hstk, by simp [work, X, runA, init0]; omega⟩
  · exact ⟨⟨_, (‹RelS n _ _ _ _ _ _ _ ∧ _›).1⟩, (‹RelS n _ _ _ _ _ _ _ ∧ _›).2⟩

/-- `tree_root` on CSR arrays (`Pre`: arc heads in `[0, n)`, costs bounded by `Cb`, `parent` all negative): the
resulting `parent`, `depth`, `cost_depth` are those of a model state satisfying `TreeSpec` (the rooted tree of the
vertices reachable from `root`), `stk[n]` is the farthest vertex (`FarSpec`), and the run takes at most
`n + m + 1` steps for `m = head[n]` arcs. -/
theorem tree_root_correct (head target cost parent depth cd stk : Array Int) (root n Cb : Nat)
    (P : Pre target cost parent depth cd n root Cb) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (hmono : ∀ i, i < n → (natL head).getD i 0 ≤ (natL head).getD (i + 1) 0)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hstk : stk.size = n + 1) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_root (Cost := Int) head target cost parent depth cd stk root n
    ⦃⇓ r c => ⌜∃ st : St, st.par = r.1.toList ∧ st.dep = r.2.1.toList ∧ st.cd = r.2.2.1.toList ∧
        TreeSpec (natL head) (natL target) cost.toList n root Cb st ∧
        FarSpec (natL head) (natL target) n root st (r.2.2.2[n]!).toNat ∧
        c ≤ t0 + 1 + n + (natL head).getD n 0⌝⦄ := by
  obtain ⟨r, c, hrun, sp, R, hc⟩ := run_of_triple (tree_root_spec head target cost parent depth cd stk root n Cb
    P hhead htarget hstk t0)
  apply triple_of_run r c hrun
  have K := (runA_inv (head := head) P n).1
  have G := (runA_inv (head := head) P n).2
  set x := X head target cost parent depth cd root n with hx
  have hS := final_S_nil _ _ _ n root Cb _ K
  obtain ⟨hp, hd, hc', -, -, -, hF⟩ := R
  refine ⟨x.1, hp.symm, hd.symm, hc'.symm, ?_, ?_, ?_⟩
  · have e : x.1 = runL (natL head) (natL target) cost.toList n (initSt parent.toList depth.toList cd.toList root) := by
      rw [hx, X, runA_fst]; rfl
    rw [e]
    exact tree_root_spec2 _ _ _ n root Cb P.hT P.hC _ _ _ P.hroot (by simp [P.hP]) (by simp [P.hD]) (by simp [P.hCd])
      P.hneg
  · rw [hF]; simpa using far_spec _ _ _ n root Cb P.hT _ _ _ K.I G hS
  · have hle := sum_nodup_le (fun v => (arcs (natL head) v).length) n x.2.1 G.g.nd
      (fun y hy => K.I.B.Llt y (G.g.inL y hy))
    have htel := sum_outdeg (natL head) n hmono
    have e2 : (fun v => (arcs (natL head) v).length) = (fun v => (natL head).getD (v + 1) 0 - (natL head).getD v 0) := by
      funext v; simp [arcs]
    rw [e2] at hle
    unfold work at hc
    rw [e2] at hc
    omega

end Proofs.Cpp.TreeRoot
