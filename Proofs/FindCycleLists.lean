import Proofs.FindCycleSpec
import Proofs.FindCycleProg
import Proofs.LowlinkExec3

namespace Proofs.FindCycleLists
open Proofs.CppScalar
open Proofs.DoublingNested (i32)
open Proofs.LowlinkInv (AdjH)
open Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.LowlinkLists (getD_set_gen valid_set)

abbrev hdF (H : List Nat) : Nat → Nat := fun a => H.getD a 0
abbrev tgF (T : List Nat) : Nat → Nat := fun a => T.getD a 0

/-- The arrays together with the abstract state. -/
structure XF where
  st : FS
  Cl : List Int
  Il : List Int
  Kl : List Int
  Yl : List Int

structure LRF (n : Nat) (x : XF) : Prop where
  lC : x.Cl.length = n
  lI : x.Il.length = n
  lK : x.Kl.length = n
  lY : x.Yl.length = n
  fC : ∀ i, x.st.C i = x.Cl.getD i 0
  fI : ∀ i, x.st.It i = x.Il.getD i 0
  fK : ∀ i, i < x.st.sp → x.Kl.getD i 0 = ((x.st.Sk i : Nat) : Int)
  vC : ∀ y ∈ x.Cl, i32.valid y = true
  vI : ∀ y ∈ x.Il, i32.valid y = true
  vK : ∀ y ∈ x.Kl, i32.valid y = true
  vY : ∀ y ∈ x.Yl, i32.valid y = true

/-- The vectors of `find_cycle`. -/
def VXF (H T : List Nat) (x : XF) : Nat → List Int := fun k =>
  if k = 0 then H.map (fun a : Nat => (a : Int)) else if k = 1 then T.map (fun a : Nat => (a : Int))
  else if k = 2 then x.Cl else if k = 3 then x.Il else if k = 4 then x.Kl else if k = 5 then x.Yl else []

theorem VXF_0 (H T x) : VXF H T x 0 = H.map (fun a : Nat => (a : Int)) := by simp [VXF]
theorem VXF_1 (H T x) : VXF H T x 1 = T.map (fun a : Nat => (a : Int)) := by simp [VXF]
theorem VXF_2 (H T x) : VXF H T x 2 = x.Cl := by simp [VXF]
theorem VXF_3 (H T x) : VXF H T x 3 = x.Il := by simp [VXF]
theorem VXF_4 (H T x) : VXF H T x 4 = x.Kl := by simp [VXF]
theorem VXF_5 (H T x) : VXF H T x 5 = x.Yl := by simp [VXF]

theorem VXF_w2 (H T x L') : Proofs.MultiVec.upd (VXF H T x) 2 L' = VXF H T { x with Cl := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VXF]; split_ifs <;> simp_all
theorem VXF_w3 (H T x L') : Proofs.MultiVec.upd (VXF H T x) 3 L' = VXF H T { x with Il := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VXF]; split_ifs <;> simp_all
theorem VXF_w4 (H T x L') : Proofs.MultiVec.upd (VXF H T x) 4 L' = VXF H T { x with Kl := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VXF]; split_ifs <;> simp_all
theorem VXF_w5 (H T x L') : Proofs.MultiVec.upd (VXF H T x) 5 L' = VXF H T { x with Yl := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VXF]; split_ifs <;> simp_all

theorem VXF_congr (H T : List Nat) {a b : XF} (h2 : a.Cl = b.Cl) (h3 : a.Il = b.Il) (h4 : a.Kl = b.Kl)
    (h5 : a.Yl = b.Yl) : VXF H T a = VXF H T b := by
  funext j
  simp only [VXF, h2, h3, h4, h5]

def skipXF (x : XF) (v : Nat) : XF :=
  { st := fSkip x.st v, Cl := x.Cl, Il := x.Il.set v (x.st.It v + 1), Kl := x.Kl, Yl := x.Yl }

def pushXF (hd : Nat → Nat) (x : XF) (v w : Nat) : XF :=
  { st := fPush hd x.st v w, Cl := x.Cl.set w 1, Il := (x.Il.set v (x.st.It v + 1)).set w (hd w : Int),
    Kl := x.Kl.set x.st.sp (w : Int), Yl := x.Yl }

def popXF (x : XF) (v : Nat) : XF :=
  { st := fPop x.st v, Cl := x.Cl.set v 2, Il := x.Il, Kl := x.Kl, Yl := x.Yl }

def rootXF (hd : Nat → Nat) (x : XF) (r : Nat) : XF :=
  { st := fRoot hd x.st r, Cl := x.Cl.set r 1, Il := x.Il.set r (hd r : Int), Kl := x.Kl.set 0 (r : Int), Yl := x.Yl }

theorem LRF_skip {n : Nat} {x : XF} (R : LRF n x) {v : Nat} (hvn : v < n) (hit : i32.valid (x.st.It v + 1) = true) :
    LRF n (skipXF x v) := by
  refine ⟨R.lC, ?_, R.lK, R.lY, R.fC, ?_, R.fK, R.vC, ?_, R.vK, R.vY⟩
  · simp [skipXF, R.lI]
  · intro i
    show Proofs.LowlinkInv.upd x.st.It v (x.st.It v + 1) i = (x.Il.set v (x.st.It v + 1)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = v
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lI, hvn]
    · simp [Proofs.LowlinkInv.upd, h, R.fI i]
  · exact valid_set R.vI _ hit

theorem LRF_pop {n : Nat} {x : XF} (R : LRF n x) {v : Nat} (hvn : v < n) (hsp : 0 < x.st.sp) :
    LRF n (popXF x v) := by
  refine ⟨?_, R.lI, R.lK, R.lY, ?_, R.fI, ?_, ?_, R.vI, R.vK, R.vY⟩
  · simp [popXF, R.lC]
  · intro i
    show Proofs.LowlinkInv.upd x.st.C v 2 i = (x.Cl.set v 2).getD i 0
    rw [getD_set_gen]
    by_cases h : i = v
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lC, hvn]
    · simp [Proofs.LowlinkInv.upd, h, R.fC i]
  · intro i hi
    exact R.fK i (by have : i < x.st.sp - 1 := hi; omega)
  · exact valid_set R.vC _ (by decide)

theorem LRF_push {n : Nat} (hd : Nat → Nat) {x : XF} (R : LRF n x) {v w : Nat} (hvn : v < n) (hwn : w < n)
    (hspn : x.st.sp < n) (hw : i32.valid (w : Int) = true) (hit : i32.valid (x.st.It v + 1) = true)
    (hhd : i32.valid (hd w : Int) = true) : LRF n (pushXF hd x v w) := by
  refine ⟨?_, ?_, ?_, R.lY, ?_, ?_, ?_, ?_, ?_, ?_, R.vY⟩
  · simp [pushXF, R.lC]
  · simp [pushXF, R.lI]
  · simp [pushXF, R.lK]
  · intro i
    show Proofs.LowlinkInv.upd x.st.C w 1 i = (x.Cl.set w 1).getD i 0
    rw [getD_set_gen]
    by_cases h : i = w
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lC, hwn]
    · simp [Proofs.LowlinkInv.upd, h, R.fC i]
  · intro i
    show Proofs.LowlinkInv.upd (Proofs.LowlinkInv.upd x.st.It v (x.st.It v + 1)) w (hd w : Int) i =
      ((x.Il.set v (x.st.It v + 1)).set w (hd w : Int)).getD i 0
    rw [getD_set_gen, getD_set_gen]
    by_cases h : i = w
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lI, hwn, hvn]
    · by_cases h2 : i = v
      · subst h2; simp [Proofs.LowlinkInv.upd, h, R.lI, hvn, R.fI i]
      · simp [Proofs.LowlinkInv.upd, h, h2, R.fI i]
  · intro i hi
    have hi' : i < x.st.sp + 1 := hi
    show (x.Kl.set x.st.sp (w : Int)).getD i 0 = (((Proofs.LowlinkInv.upd x.st.Sk x.st.sp w) i : Nat) : Int)
    rw [getD_set_gen]
    by_cases h : i = x.st.sp
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lK, hspn]
    · have := R.fK i (by omega)
      have h' : ¬ (i = x.st.sp ∧ x.st.sp < x.Kl.length) := fun hh => h hh.1
      rw [if_neg h', this]
      simp [Proofs.LowlinkInv.upd, h]
  · exact valid_set R.vC _ (by decide)
  · exact valid_set (valid_set R.vI _ hit) _ hhd
  · exact valid_set R.vK _ hw

theorem LRF_root {n : Nat} (hd : Nat → Nat) {x : XF} (R : LRF n x) {r : Nat} (hrn : r < n)
    (hr : i32.valid (r : Int) = true) (hhd : i32.valid (hd r : Int) = true) : LRF n (rootXF hd x r) := by
  refine ⟨?_, ?_, ?_, R.lY, ?_, ?_, ?_, ?_, ?_, ?_, R.vY⟩
  · simp [rootXF, R.lC]
  · simp [rootXF, R.lI]
  · simp [rootXF, R.lK]
  · intro i
    show Proofs.LowlinkInv.upd x.st.C r 1 i = (x.Cl.set r 1).getD i 0
    rw [getD_set_gen]
    by_cases h : i = r
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lC, hrn]
    · simp [Proofs.LowlinkInv.upd, h, R.fC i]
  · intro i
    show Proofs.LowlinkInv.upd x.st.It r (hd r : Int) i = (x.Il.set r (hd r : Int)).getD i 0
    rw [getD_set_gen]
    by_cases h : i = r
    · subst h; simp [Proofs.LowlinkInv.upd_same, R.lI, hrn]
    · simp [Proofs.LowlinkInv.upd, h, R.fI i]
  · intro i hi
    have hi' : i < 1 := hi
    have : i = 0 := by omega
    subst this
    show (x.Kl.set 0 (r : Int)).getD 0 0 = (((Proofs.LowlinkInv.upd x.st.Sk 0 r) 0 : Nat) : Int)
    rw [getD_set_gen]
    have h0 : 0 < x.Kl.length := by rw [R.lK]; omega
    simp [Proofs.LowlinkInv.upd_same, h0]
  · exact valid_set R.vC _ (by decide)
  · exact valid_set R.vI _ hhd
  · exact valid_set R.vK _ hr

end Proofs.FindCycleLists
