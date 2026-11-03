import Proofs.LowlinkPhi
import Proofs.LowlinkExec
import Proofs.LowlinkExec2

namespace Proofs.LowlinkStep
open Proofs.CppScalar
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
open Proofs.DijkstraScan (i32v)
open Proofs.LowlinkInv Proofs.LowlinkScan Proofs.LowlinkPop Proofs.LowlinkPush Proofs.LowlinkRoot Proofs.LowlinkLists
open Proofs.LowlinkPhi Proofs.LowlinkExec Proofs.LowlinkExec2

/-- The machine step preserves the invariant, the array relation, the visited set and decreases the potential. -/
structure StepOK (n : Nat) (hd tg : Nat → Nat) (x x' : XS) : Prop where
  inv : MInv n hd tg x'.st
  lr : LR n x'
  vis : ∀ a ∈ x.st.Vis, a ∈ x'.st.Vis
  phi : phi n hd x'.st + 1 ≤ phi n hd x.st

theorem i32_of_lt (a : Nat) (h : a < M31) : i32.valid (a : Int) = true := i32v a h

theorem step_push {n : Nat} {hd tg : Nat → Nat} (G : GH n hd tg) {x : XS} (I : MInv n hd tg x.st) (R : LR n x)
    {v w q : Nat} (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v)
    (hit : (q : Int) < (hd (v + 1) : Int)) (hw : tg q = w) (hwU : x.st.O w < 0) (hn : n < M31)
    (hit1 : i32.valid (x.st.It v + 1) = true) (hhd : hd w < M31) : StepOK n hd tg x (pushX hd x v w) := by
  have hvV := (I.sk_mem (x.st.sp - 1) (by omega)).1
  rw [hv] at hvV
  have hvn := I.vis_lt v hvV
  have hwV : w ∉ x.st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
  have hrng := I.it_rng v hvV
  have hadj : AdjH hd tg v w := ⟨q, by omega, by omega, hw⟩
  have hwn := (G.adj_lt v w hadj).2
  have hlt : x.st.Vis.length < n := by
    have hnd : (x.st.Vis ++ [w]).Nodup := by
      rw [List.nodup_append]
      refine ⟨I.vis_nd, by simp, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      exact fun e => hwV (e ▸ ha)
    have hsub : (x.st.Vis ++ [w]) ⊆ List.range n := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_range.mpr (I.vis_lt a h)
      · simp at h; subst h; exact List.mem_range.mpr hwn
    have := List.Nodup.length_le_of_subset hnd hsub
    simp at this
    omega
  have hspn : x.st.sp < n := by have := I.sp_le; omega
  refine ⟨inv_push G I hsp hv hq hit hw hwU, ?_, ?_, ?_⟩
  · exact LR_push hd R hvn hwn hspn (i32_of_lt _ (by omega)) (i32_of_lt _ (by omega)) (i32_of_lt _ (by omega)) hit1
      (i32_of_lt _ hhd)
  · intro a ha
    show a ∈ x.st.Vis ++ [w]
    exact List.mem_append.mpr (Or.inl ha)
  · exact phi_push n hd x.st v w hvn hvV hwV hlt hrng.1 (by omega)


theorem step_adv {n : Nat} {hd tg : Nat → Nat} (G : GH n hd tg) {x : XS} (I : MInv n hd tg x.st) (R : LR n x)
    {v w q : Nat} (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v)
    (hit : (q : Int) < (hd (v + 1) : Int)) (hw : tg q = w) (hwv : 0 ≤ x.st.O w) (hpar : x.st.P v = (w : Int))
    (hit1 : i32.valid (x.st.It v + 1) = true) : StepOK n hd tg x (advX x v) := by
  have hvm := I.sk_mem (x.st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn := I.vis_lt v hvV
  have hrng := I.it_rng v hvV
  refine ⟨?_, LR_adv R hvn hit1, fun a ha => ha, phi_scan n hd x.st v x.st.L hvn hvV hrng.1 (by omega)⟩
  exact inv_scan I x.st.L hvV hfv hq hit hw hwv (fun u => Int.le_refl _) (fun u _ => rfl) (I.low_le v hvV).1
    (Or.inl rfl) (fun h => absurd hpar h)

theorem step_back {n : Nat} {hd tg : Nat → Nat} (G : GH n hd tg) {x : XS} (I : MInv n hd tg x.st) (R : LR n x)
    {v w q : Nat} (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hq : (q : Int) = x.st.It v)
    (hit : (q : Int) < (hd (v + 1) : Int)) (hw : tg q = w) (hwv : 0 ≤ x.st.O w) (hpar : x.st.P v ≠ (w : Int))
    (hit1 : i32.valid (x.st.It v + 1) = true) : StepOK n hd tg x (backX x v w) := by
  have hvm := I.sk_mem (x.st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn := I.vis_lt v hvV
  have hwV := I.vis_of_nn hwv
  have hrng := I.it_rng v hvV
  have hLv := I.low_le v hvV
  have hm : i32.valid (min (x.st.L v) (x.st.O w)) = true := by
    have a1 : i32.valid (x.st.L v) = true := by
      rw [R.fL v]; exact rd_valid R.vL (by rw [R.lL]; exact hvn)
    have a2 : i32.valid (x.st.O w) = true := by
      have := I.vis_lt w hwV
      rw [R.fO w, getD_dflt x.Ol w (by rw [R.lO]; exact this) (-1) 0]
      exact rd_valid R.vO (by rw [R.lO]; exact this)
    by_cases hle : x.st.L v ≤ x.st.O w
    · rw [Int.min_eq_left hle]; exact a1
    · rw [Int.min_eq_right (by omega)]; exact a2
  refine ⟨?_, LR_back R hvn hit1 hm, fun a ha => ha, phi_scan n hd x.st v _ hvn hvV hrng.1 (by omega)⟩
  refine inv_scan I (upd x.st.L v (min (x.st.L v) (x.st.O w))) hvV hfv hq hit hw hwv ?_ ?_ ?_ ?_ ?_
  · intro u
    by_cases huv : u = v
    · subst huv; rw [upd_same]; exact Int.min_le_left _ _
    · rw [upd_ne _ _ _ _ huv]
  · intro u hu; exact upd_ne _ _ _ _ hu
  · rw [upd_same]; omega
  · by_cases hle : x.st.L v ≤ x.st.O w
    · left; rw [upd_same, Int.min_eq_left hle]
    · right; refine ⟨hpar, ?_⟩; rw [upd_same, Int.min_eq_right (by omega)]
  · intro _; rw [upd_same]; exact Int.min_le_right _ _


theorem step_pop {n : Nat} {hd tg : Nat → Nat} {x : XS} (I : MInv n hd tg x.st) (R : LR n x) {v : Nat}
    (hsp : 0 < x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hit : x.st.It v = (hd (v + 1) : Int)) (hn1 : n + 1 < M31) :
    StepOK n hd tg x (popX x v) := by
  have hvm := I.sk_mem (x.st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn := I.vis_lt v hvV
  have hLvalid : ∀ u, u < n → i32.valid (x.st.L u) = true := by
    intro u hu
    rw [R.fL u]; exact rd_valid R.vL (by rw [R.lL]; exact hu)
  refine ⟨inv_pop I hsp hv hit, ?_, fun a ha => ha, phi_pop n hd x.st v hsp⟩
  apply LR_pop R
  · intro p hp
    exact I.vis_lt p (I.par_ok p v hp).1
  · intro p hp
    have hpn := I.vis_lt p (I.par_ok p v hp).1
    have a1 := hLvalid p hpn
    have a2 := hLvalid v hvn
    by_cases hle : x.st.L p ≤ x.st.L v
    · rw [Int.min_eq_left hle]; exact a1
    · rw [Int.min_eq_right (by omega)]; exact a2
  · intro p hp
    have hpV := (I.par_ok p v hp).1
    have hpn := I.vis_lt p hpV
    have h1 := I.sep_le hpV
    have h2 := I.vis_len_le
    have h3 := (i32_valid_iff _).mp (show i32.valid (x.st.Sp p) = true by
      rw [R.fS p]; exact rd_valid R.vS (by rw [R.lS]; exact hpn))
    have : n + 1 < M31 := hn1
    unfold M31 at this
    rw [i32_valid_iff]
    split <;> constructor <;> omega

end Proofs.LowlinkStep
