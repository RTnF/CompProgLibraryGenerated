import Proofs.LowlinkFinal
import Proofs.LowlinkScan
import Proofs.DijkstraExec

namespace Proofs.LowlinkLists
open Proofs.PrimMath (Rtc)
open Proofs.DoublingNested (i32)
open Proofs.LowlinkInv Proofs.LowlinkScan Proofs.LowlinkPop Proofs.LowlinkPush Proofs.LowlinkRoot Proofs.CppScalar

theorem getD_set_gen (l : List Int) (j : Nat) (a : Int) (i : Nat) (d : Int) :
    (l.set j a).getD i d = if i = j ∧ j < l.length then a else l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h
    by_cases hj : j < l.length <;> simp [hj]
  · simp [h, Ne.symm h]

/-- The mutable arrays together with the abstract machine state. -/
structure XS where
  st : St
  Ol : List Int
  Ll : List Int
  Pl : List Int
  Sl : List Int
  Il : List Int
  Kl : List Int

structure LR (n : Nat) (x : XS) : Prop where
  lO : x.Ol.length = n
  lL : x.Ll.length = n
  lP : x.Pl.length = n
  lS : x.Sl.length = n
  lI : x.Il.length = n
  lK : x.Kl.length = n
  fO : ∀ i, x.st.O i = x.Ol.getD i (-1)
  fL : ∀ i, x.st.L i = x.Ll.getD i 0
  fP : ∀ i, x.st.P i = x.Pl.getD i (-1)
  fS : ∀ i, x.st.Sp i = x.Sl.getD i 0
  fI : ∀ i, x.st.It i = x.Il.getD i 0
  fK : ∀ i, i < x.st.sp → x.Kl.getD i 0 = ((x.st.Sk i : Nat) : Int)
  vO : ∀ y ∈ x.Ol, i32.valid y = true
  vL : ∀ y ∈ x.Ll, i32.valid y = true
  vP : ∀ y ∈ x.Pl, i32.valid y = true
  vS : ∀ y ∈ x.Sl, i32.valid y = true
  vI : ∀ y ∈ x.Il, i32.valid y = true
  vK : ∀ y ∈ x.Kl, i32.valid y = true

theorem valid_set {l : List Int} (hl : ∀ y ∈ l, i32.valid y = true) (j : Nat) {a : Int} (ha : i32.valid a = true) :
    ∀ y ∈ l.set j a, i32.valid y = true := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hl y h
  · rw [h]; exact ha

/-! ### Transitions of the arrays -/

def pushX (hd : Nat → Nat) (x : XS) (v w : Nat) : XS :=
  { st := pushS hd x.st v w
    Ol := x.Ol.set w (x.st.Vis.length : Int)
    Ll := x.Ll.set w (x.st.Vis.length : Int)
    Pl := x.Pl.set w (v : Int)
    Sl := x.Sl
    Il := (x.Il.set v (x.st.It v + 1)).set w (hd w : Int)
    Kl := x.Kl.set x.st.sp (w : Int) }

theorem LR_push {n : Nat} (hd : Nat → Nat) {x : XS} (R : LR n x) {v w : Nat} (hvn : v < n) (hwn : w < n)
    (hspn : x.st.sp < n) (hcnt : i32.valid (x.st.Vis.length : Int) = true) (hv : i32.valid (v : Int) = true)
    (hw : i32.valid (w : Int) = true) (hit : i32.valid (x.st.It v + 1) = true) (hhd : i32.valid (hd w : Int) = true) :
    LR n (pushX hd x v w) := by
  refine ⟨?_, ?_, ?_, R.lS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, R.vS, ?_, ?_⟩
  · simp [pushX, R.lO]
  · simp [pushX, R.lL]
  · simp [pushX, R.lP]
  · simp [pushX, R.lI]
  · simp [pushX, R.lK]
  · intro i
    show upd x.st.O w (x.st.Vis.length : Int) i = (x.Ol.set w (x.st.Vis.length : Int)).getD i (-1)
    rw [getD_set_gen]
    by_cases h : i = w
    · subst h; simp [upd_same, R.lO, hwn]
    · simp [upd, h, R.fO i]
  · intro i
    show upd x.st.L w (x.st.Vis.length : Int) i = (x.Ll.set w (x.st.Vis.length : Int)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = w
    · subst h; simp [upd_same, R.lL, hwn]
    · simp [upd, h, R.fL i]
  · intro i
    show upd x.st.P w (v : Int) i = (x.Pl.set w (v : Int)).getD i (-1)
    rw [getD_set_gen]
    by_cases h : i = w
    · subst h; simp [upd_same, R.lP, hwn]
    · simp [upd, h, R.fP i]
  · intro i
    exact R.fS i
  · intro i
    show upd (upd x.st.It v (x.st.It v + 1)) w (hd w : Int) i = ((x.Il.set v (x.st.It v + 1)).set w (hd w : Int)).getD i 0
    rw [getD_set_gen, getD_set_gen]
    by_cases h : i = w
    · subst h; simp [upd_same, R.lI, hwn, hvn]
    · by_cases h2 : i = v
      · subst h2; simp [upd, h, R.lI, hvn, R.fI i]
      · simp [upd, h, h2, R.fI i]
  · intro i hi
    have hi' : i < x.st.sp + 1 := hi
    show (x.Kl.set x.st.sp (w : Int)).getD i 0 = (((upd x.st.Sk x.st.sp w) i : Nat) : Int)
    rw [getD_set_gen]
    by_cases h : i = x.st.sp
    · subst h; simp [upd_same, R.lK, hspn]
    · have := R.fK i (by omega)
      have h' : ¬ (i = x.st.sp ∧ x.st.sp < x.Kl.length) := fun hh => h hh.1
      rw [if_neg h', this]
      simp [upd, h]
  · exact valid_set R.vO _ hcnt
  · exact valid_set R.vL _ hcnt
  · exact valid_set R.vP _ hv
  · exact valid_set (valid_set R.vI _ hit) _ hhd
  · exact valid_set R.vK _ hw


def advX (x : XS) (v : Nat) : XS :=
  { st := scanS x.st v x.st.L
    Ol := x.Ol
    Ll := x.Ll
    Pl := x.Pl
    Sl := x.Sl
    Il := x.Il.set v (x.st.It v + 1)
    Kl := x.Kl }

def backX (x : XS) (v w : Nat) : XS :=
  { st := scanS x.st v (upd x.st.L v (min (x.st.L v) (x.st.O w)))
    Ol := x.Ol
    Ll := x.Ll.set v (min (x.st.L v) (x.st.O w))
    Pl := x.Pl
    Sl := x.Sl
    Il := x.Il.set v (x.st.It v + 1)
    Kl := x.Kl }

theorem LR_adv {n : Nat} {x : XS} (R : LR n x) {v : Nat} (hvn : v < n) (hit : i32.valid (x.st.It v + 1) = true) :
    LR n (advX x v) := by
  refine ⟨R.lO, R.lL, R.lP, R.lS, ?_, R.lK, R.fO, R.fL, R.fP, R.fS, ?_, R.fK, R.vO, R.vL, R.vP, R.vS, ?_, R.vK⟩
  · simp [advX, R.lI]
  · intro i
    show upd x.st.It v (x.st.It v + 1) i = (x.Il.set v (x.st.It v + 1)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = v
    · subst h; simp [upd_same, R.lI, hvn]
    · simp [upd, h, R.fI i]
  · exact valid_set R.vI _ hit

theorem LR_back {n : Nat} {x : XS} (R : LR n x) {v w : Nat} (hvn : v < n) (hit : i32.valid (x.st.It v + 1) = true)
    (hm : i32.valid (min (x.st.L v) (x.st.O w)) = true) : LR n (backX x v w) := by
  refine ⟨R.lO, ?_, R.lP, R.lS, ?_, R.lK, R.fO, ?_, R.fP, R.fS, ?_, R.fK, R.vO, ?_, R.vP, R.vS, ?_, R.vK⟩
  · simp [backX, R.lL]
  · simp [backX, R.lI]
  · intro i
    show upd x.st.L v (min (x.st.L v) (x.st.O w)) i = (x.Ll.set v (min (x.st.L v) (x.st.O w))).getD i 0
    rw [getD_set_gen]
    by_cases h : i = v
    · subst h; simp [upd_same, R.lL, hvn]
    · simp [upd, h, R.fL i]
  · intro i
    show upd x.st.It v (x.st.It v + 1) i = (x.Il.set v (x.st.It v + 1)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = v
    · subst h; simp [upd_same, R.lI, hvn]
    · simp [upd, h, R.fI i]
  · exact valid_set R.vL _ hm
  · exact valid_set R.vI _ hit

def popX (x : XS) (v : Nat) : XS :=
  { st := popS x.st v
    Ol := x.Ol
    Ll := if 0 ≤ x.st.P v then x.Ll.set (x.st.P v).toNat (min (x.st.L (x.st.P v).toNat) (x.st.L v)) else x.Ll
    Pl := x.Pl
    Sl := if 0 ≤ x.st.P v then x.Sl.set (x.st.P v).toNat
      (x.st.Sp (x.st.P v).toNat + (if x.st.O (x.st.P v).toNat ≤ x.st.L v then 1 else 0)) else x.Sl
    Il := x.Il
    Kl := x.Kl }

theorem LR_pop {n : Nat} {x : XS} (R : LR n x) {v : Nat} (hpn : ∀ p : Nat, x.st.P v = (p : Int) → p < n)
    (hm : ∀ p : Nat, x.st.P v = (p : Int) → i32.valid (min (x.st.L p) (x.st.L v)) = true)
    (hs : ∀ p : Nat, x.st.P v = (p : Int) → i32.valid (x.st.Sp p + (if x.st.O p ≤ x.st.L v then 1 else 0)) = true) :
    LR n (popX x v) := by
  by_cases hP : 0 ≤ x.st.P v
  · obtain ⟨p, hp⟩ : ∃ p : Nat, x.st.P v = (p : Int) := ⟨(x.st.P v).toNat, by omega⟩
    have hpn' := hpn p hp
    have ep : (x.st.P v).toNat = p := by omega
    have hL : (popX x v).Ll = x.Ll.set p (min (x.st.L p) (x.st.L v)) := by
      simp only [popX, if_pos hP, ep]
    have hS : (popX x v).Sl = x.Sl.set p (x.st.Sp p + (if x.st.O p ≤ x.st.L v then 1 else 0)) := by
      simp only [popX, if_pos hP, ep]
    refine ⟨R.lO, ?_, R.lP, ?_, R.lI, R.lK, ?_, ?_, ?_, ?_, ?_, ?_, R.vO, ?_, R.vP, ?_, R.vI, R.vK⟩
    · rw [hL]; simp [R.lL]
    · rw [hS]; simp [R.lS]
    · intro i; exact R.fO i
    · intro i
      rw [hL]
      show (if x.st.P v = (i : Int) then min (x.st.L i) (x.st.L v) else x.st.L i) = _
      rw [getD_set_gen]
      by_cases h : i = p
      · subst h; simp [hp, R.lL, hpn']
      · have : ¬ x.st.P v = (i : Int) := by omega
        simp [this, h, R.fL i]
    · intro i; exact R.fP i
    · intro i
      rw [hS]
      show (if x.st.P v = (i : Int) then x.st.Sp i + (if x.st.O i ≤ x.st.L v then 1 else 0) else x.st.Sp i) = _
      rw [getD_set_gen]
      by_cases h : i = p
      · subst h; simp [hp, R.lS, hpn']
      · have : ¬ x.st.P v = (i : Int) := by omega
        simp [this, h, R.fS i]
    · intro i; exact R.fI i
    · intro i hi
      exact R.fK i (by have : i < x.st.sp - 1 := hi; omega)
    · rw [hL]; exact valid_set R.vL _ (hm p hp)
    · rw [hS]; exact valid_set R.vS _ (hs p hp)
  · have hL : (popX x v).Ll = x.Ll := by simp only [popX, if_neg hP]
    have hS : (popX x v).Sl = x.Sl := by simp only [popX, if_neg hP]
    refine ⟨R.lO, ?_, R.lP, ?_, R.lI, R.lK, R.fO, ?_, R.fP, ?_, R.fI, ?_, R.vO, ?_, R.vP, ?_, R.vI, R.vK⟩
    · rw [hL]; exact R.lL
    · rw [hS]; exact R.lS
    · intro i
      rw [hL]
      show (if x.st.P v = (i : Int) then min (x.st.L i) (x.st.L v) else x.st.L i) = _
      have : ¬ x.st.P v = (i : Int) := by omega
      rw [if_neg this]; exact R.fL i
    · intro i
      rw [hS]
      show (if x.st.P v = (i : Int) then x.st.Sp i + (if x.st.O i ≤ x.st.L v then 1 else 0) else x.st.Sp i) = _
      have : ¬ x.st.P v = (i : Int) := by omega
      rw [if_neg this]; exact R.fS i
    · intro i hi
      exact R.fK i (by have : i < x.st.sp - 1 := hi; omega)
    · rw [hL]; exact R.vL
    · rw [hS]; exact R.vS

def rootX (hd : Nat → Nat) (x : XS) (r : Nat) : XS :=
  { st := rootS hd x.st r
    Ol := x.Ol.set r (x.st.Vis.length : Int)
    Ll := x.Ll.set r (x.st.Vis.length : Int)
    Pl := x.Pl
    Sl := x.Sl
    Il := x.Il.set r (hd r : Int)
    Kl := x.Kl.set 0 (r : Int) }

theorem LR_root {n : Nat} (hd : Nat → Nat) {x : XS} (R : LR n x) {r : Nat} (hrn : r < n)
    (hcnt : i32.valid (x.st.Vis.length : Int) = true) (hr : i32.valid (r : Int) = true)
    (hhd : i32.valid (hd r : Int) = true) : LR n (rootX hd x r) := by
  refine ⟨?_, ?_, R.lP, R.lS, ?_, ?_, ?_, ?_, R.fP, R.fS, ?_, ?_, ?_, ?_, R.vP, R.vS, ?_, ?_⟩
  · simp [rootX, R.lO]
  · simp [rootX, R.lL]
  · simp [rootX, R.lI]
  · simp [rootX, R.lK]
  · intro i
    show upd x.st.O r (x.st.Vis.length : Int) i = (x.Ol.set r (x.st.Vis.length : Int)).getD i (-1)
    rw [getD_set_gen]
    by_cases h : i = r
    · subst h; simp [upd_same, R.lO, hrn]
    · simp [upd, h, R.fO i]
  · intro i
    show upd x.st.L r (x.st.Vis.length : Int) i = (x.Ll.set r (x.st.Vis.length : Int)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = r
    · subst h; simp [upd_same, R.lL, hrn]
    · simp [upd, h, R.fL i]
  · intro i
    show upd x.st.It r (hd r : Int) i = (x.Il.set r (hd r : Int)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = r
    · subst h; simp [upd_same, R.lI, hrn]
    · simp [upd, h, R.fI i]
  · intro i hi
    have hi' : i < 1 := hi
    have : i = 0 := by omega
    subst this
    show (x.Kl.set 0 (r : Int)).getD 0 0 = (((upd x.st.Sk 0 r) 0 : Nat) : Int)
    rw [getD_set_gen]
    have h0 : 0 < x.Kl.length := by rw [R.lK]; omega
    simp [upd_same, h0]
  · exact valid_set R.vO _ hcnt
  · exact valid_set R.vL _ hcnt
  · exact valid_set R.vI _ hhd
  · exact valid_set R.vK _ hr

end Proofs.LowlinkLists
