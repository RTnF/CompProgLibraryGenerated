import Proofs.FindCyclePhi
import Proofs.FindCycleLists

namespace Proofs.FindCycleOk
open Proofs.CppScalar
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
open Proofs.DijkstraScan (i32v)
open Proofs.LowlinkInv (AdjH)
open Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi Proofs.FindCycleSpec Proofs.FindCycleLists

structure FStepOK (n : Nat) (hd tg : Nat → Nat) (x x' : XF) : Prop where
  inv : FInv n hd tg x'.st
  lr : LRF n x'
  vis : ∀ a, x.st.C a ≠ 0 → x'.st.C a ≠ 0
  phi : phiF n hd x'.st + 1 ≤ phiF n hd x.st

/-- The state after a back arc was found: the snapshot of the stack and the arrays. -/
structure FoundS (n : Nat) (hd tg : Nat → Nat) (x : XF) (fsp fw : Nat) : Prop where
  fnd : Found n hd tg x.st.Sk fsp fw
  kl : ∀ i, i < fsp → x.Kl.getD i 0 = ((x.st.Sk i : Nat) : Int)
  lC : x.Cl.length = n
  lI : x.Il.length = n
  lK : x.Kl.length = n
  lY : x.Yl.length = n
  vC : ∀ y ∈ x.Cl, i32.valid y = true
  vI : ∀ y ∈ x.Il, i32.valid y = true
  vK : ∀ y ∈ x.Kl, i32.valid y = true
  vY : ∀ y ∈ x.Yl, i32.valid y = true

def foundXF (x : XF) (v : Nat) : XF :=
  { st := { x.st with sp := 0 }, Cl := x.Cl, Il := x.Il.set v (x.st.It v + 1), Kl := x.Kl, Yl := x.Yl }

theorem step_pushF {n : Nat} {hd tg : Nat → Nat} (G : FGH n hd tg) {x : XF} (I : FInv n hd tg x.st) (R : LRF n x)
    {v w q : Nat} (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v)
    (hit : q < hd (v + 1)) (hw : tg q = w) (hwc : x.st.C w = 0) (hn : n < M31)
    (hit1 : i32.valid (x.st.It v + 1) = true) (hhd : hd w < M31) : FStepOK n hd tg x (pushXF hd x v w) := by
  have hvg := top_gray I hsp hv
  have hrng := I.it_rng v (by omega)
  have hvn := I.c_lt v (by omega)
  have hadj : AdjH hd tg v w := ⟨q, by omega, hit, hw⟩
  have hwn := (G.adj_lt v w hadj).2
  have hspn : x.st.sp < n := by
    have hle := I.sp_le
    -- the stack plus the new vertex are distinct vertices below n
    have hnd : ((List.range x.st.sp).map x.st.Sk ++ [w]).Nodup := by
      rw [List.nodup_append]
      refine ⟨?_, by simp, ?_⟩
      · apply Proofs.PrimMath.nodup_map_inj List.nodup_range
        intro a ha b hb h
        exact I.sk_inj a b (List.mem_range.mp ha) (List.mem_range.mp hb) h
      · intro a ha b hb
        simp at hb
        subst hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        have := I.sk_gray i (List.mem_range.mp hi)
        intro e; rw [e] at this; omega
    have hsub : ((List.range x.st.sp).map x.st.Sk ++ [w]) ⊆ List.range n := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        have := I.sk_gray i (List.mem_range.mp hi)
        exact List.mem_range.mpr (I.c_lt _ (by omega))
      · simp at h; subst h; exact List.mem_range.mpr hwn
    have := List.Nodup.length_le_of_subset hnd hsub
    simp at this
    omega
  refine ⟨inv_push G I hsp hv hq hit hw hwc, ?_, ?_, ?_⟩
  · exact LRF_push hd R hvn hwn hspn (i32v _ (by omega)) hit1 (i32v _ hhd)
  · intro a ha
    by_cases haw : a = w
    · subst haw; show (fPush hd x.st v a).C a ≠ 0; rw [show (fPush hd x.st v a).C a = 1 from Proofs.LowlinkInv.upd_same _ _ _]; omega
    · show (fPush hd x.st v w).C a ≠ 0
      rw [show (fPush hd x.st v w).C a = x.st.C a from Proofs.LowlinkInv.upd_ne _ _ _ _ haw]; exact ha
  · exact phiF_push n hd x.st v w hvn hwn (by omega) hwc hrng.1 (by omega)

theorem step_skipF {n : Nat} {hd tg : Nat → Nat} (G : FGH n hd tg) {x : XF} (I : FInv n hd tg x.st) (R : LRF n x)
    {v w q : Nat} (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v)
    (hit : q < hd (v + 1)) (hw : tg q = w) (hwb : x.st.C w = 2) (hit1 : i32.valid (x.st.It v + 1) = true) :
    FStepOK n hd tg x (skipXF x v) := by
  have hvg := top_gray I hsp hv
  have hrng := I.it_rng v (by omega)
  have hvn := I.c_lt v (by omega)
  exact ⟨inv_skip I hsp hv hq hit hw hwb, LRF_skip R hvn hit1, fun a ha => ha,
    phiF_skip n hd x.st v hvn (by omega) hrng.1 (by omega)⟩

theorem step_popF {n : Nat} {hd tg : Nat → Nat} {x : XF} (I : FInv n hd tg x.st) (R : LRF n x) {v : Nat}
    (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hit : x.st.It v = (hd (v + 1) : Int)) :
    FStepOK n hd tg x (popXF x v) := by
  have hvg := top_gray I hsp hv
  have hvn := I.c_lt v (by omega)
  refine ⟨inv_pop I hsp hv hit, LRF_pop R hvn hsp, ?_, phiF_pop n hd x.st v hsp hvg⟩
  intro a ha
  by_cases hav : a = v
  · subst hav
    show (fPop x.st a).C a ≠ 0
    rw [show (fPop x.st a).C a = 2 from Proofs.LowlinkInv.upd_same _ _ _]; omega
  · show (fPop x.st v).C a ≠ 0
    rw [show (fPop x.st v).C a = x.st.C a from Proofs.LowlinkInv.upd_ne _ _ _ _ hav]; exact ha

theorem found_ofF {n : Nat} {hd tg : Nat → Nat} {x : XF} (I : FInv n hd tg x.st) (R : LRF n x) {v w q : Nat}
    (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v) (hit : q < hd (v + 1))
    (hw : tg q = w) (hwg : x.st.C w = 1) (hvn : v < n) (hit1 : i32.valid (x.st.It v + 1) = true) :
    FoundS n hd tg (foundXF x v) x.st.sp w := by
  have hF := found_of_inv I hsp hv hq hit hw hwg
  have R2 := LRF_skip R hvn hit1
  refine ⟨hF, fun i hi => R.fK i hi, R.lC, ?_, R.lK, R.lY, R.vC, ?_, R.vK, R.vY⟩
  · show (x.Il.set v (x.st.It v + 1)).length = n
    simp [R.lI]
  · exact R2.vI

end Proofs.FindCycleOk
