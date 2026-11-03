import Proofs.BeatsUpdRun
import Proofs.BeatsLoop0
import Proofs.BeatsFuel
import Proofs.BeatsExec_ApInit
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

/-- `apply_op` as a command. -/
abbrev ApplyOpCmd (o : Nat) : Command := ApInitc0 o (.sequence (ALoop o) (.sequence (ULoop o) Sk))

/-- The state after the initialisation of the stack. -/
def initB (b : BS) (n : Nat) : BS := ui3 (ui2 (ui1 b 0 0) 0 0) 0 (n : Int)

theorem initB_sk (b : BS) (n : Nat) : (initB b n).sk = b.sk.set 0 0 := rfl
theorem initB_sl (b : BS) (n : Nat) : (initB b n).sl = b.sl.set 0 0 := rfl
theorem initB_sr (b : BS) (n : Nat) : (initB b n).sr = b.sr.set 0 (n : Int) := rfl

theorem initB_sameLen (b : BS) (n : Nat) : SameLen b (initB b n) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · rw [initB_sk]; simp
  · rw [initB_sl]; simp
  · rw [initB_sr]; simp

theorem initB_valid (b : BS) (n : Nat) (hn : n < M31) (hV : ValidOK b) : ValidOK (initB b n) := by
  refine ⟨hV.v0, hV.v1, hV.v2, hV.v3, hV.v4, hV.v5, hV.v6, hV.v7, hV.v8, hV.v9, hV.v10, ?_, ?_, ?_, hV.v14⟩
  · rw [initB_sk]; exact valid_set (fun w => i32.valid w = true) _ _ _ hV.v11 (by decide)
  · rw [initB_sl]; exact valid_set (fun w => i32.valid w = true) _ _ _ hV.v12 (by decide)
  · rw [initB_sr]; exact valid_set (fun w => i32.valid w = true) _ _ _ hV.v13 (Proofs.BellmanFordExec.i32_valid_nat n hn)

theorem initB_stk (b : BS) (n : Nat) (hk : 0 < b.sk.length) (hl : 0 < b.sl.length) (hr : 0 < b.sr.length) :
    StkRep (initB b n) 1 [⟨0, 0, n⟩] := by
  refine ⟨rfl, ?_⟩
  intro j f hj
  cases j with
  | zero =>
    simp at hj; subst hj
    refine ⟨?_, ?_, ?_⟩
    · show (b.sk.set 0 0).getD (1 - 1 - 0) 0 = ((0 : Nat) : Int)
      exact getD_set_same _ _ _ hk
    · show (b.sl.set 0 0).getD (1 - 1 - 0) 0 = ((0 : Nat) : Int)
      exact getD_set_same _ _ _ hl
    · show (b.sr.set 0 (n : Int)).getD (1 - 1 - 0) 0 = (n : Int)
      exact getD_set_same _ _ _ hr
  | succ j => simp at hj

theorem apply0_exec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chminSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31)
:
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (ApplyOpCmd (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci 0, ci qa, ci qb, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P (pre ++ LCells inf n 0 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 ∧ r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0 := by
  have hL0 : 0 < L := by omega
  have hlk : 0 < b.sk.length := by have := hLens.lsk; omega
  have hll : 0 < b.sl.length := by have := hLens.lsl; omega
  have hlr : 0 < b.sr.length := by have := hLens.lsr; omega
  have hHI : HRel inf (initB b n) H := HRel_stable inf b (initB b n) H hH (fun i => ⟨rfl, rfl⟩) rfl
  have hlenI : LenOK (initB b n) t 0 0 n := LenOKs_of_eq (b := b) (b' := initB b n) rfl _ _ _ _ hlen
  have hSLI := initB_sameLen b n
  have hLensI := Lens_of_same hLens hSLI
  have hVI := initB_valid b n Ev.hnM hV
  have hEntI : EntRep (initB b n) 0 [] := ⟨rfl, by intro j e h; simp at h⟩
  obtain ⟨bf, nef, F1, hF1, hRun, H', Enew, hHR', hEnt, hVf, hSLf, hAg, hlenE, hIn, hStar, hSm⟩ :=
    loop0_all Ev hx t ys (initB b n) 0 H hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initB_stk b n hlk hll hlr) hEntI hsp hne hlh
  have hLensf : Lens bf L := Lens_of_same hLensI hSLf
  have hEL : ∀ e ∈ Enew, 2 * e + 2 < L := fun e he => InSks_lt t.skel 0 L e hidx (hIn e he)
  have hnefL : nef ≤ L := by have := hEnt.1; omega
  obtain ⟨bf2, F2, hF2, hRunU, hHR2, hV2, hSL2, -, -, -⟩ :=
    upd_all mv Ev.hnv pre Ev.hty Ev.hty32 P inf n 0 qa qb 0 x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM (by decide) Ev.hx L Ev.hLM
      Enew bf nef H' hEnt hVf hLensf hEL hnefL hSm hHR'
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hRunU
  have h1' := pexecM_mono mv _ _ _ r1 F1 F2 h1
  have h2' := pexecM_mono mv _ _ _ r2 F2 F1 h2
  rw [Nat.add_comm F2 F1] at h2'
  have h2'' : pexecM mv (F1 + F2) (ULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2'
  have hseq := seqM_some h1' hr1 (seqM_some h2'' hr2 (pexecM_skip mv (F1 + F2) r2.ps r2.vv))
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    ApInit_ch0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n 0 qa qb x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx hV.v11 hV.v12 hV.v13
      hlk hll hlr 1 rfl (F1 + F2) (.sequence (ALoop (mv.nv + pre.length)) (.sequence (ULoop (mv.nv + pre.length)) Sk))
      _ hseq (by simpa using hr2)
  have hlE : Enew.length ≤ innerOf t := hlenE
  refine ⟨bf2, upPhase Enew H', F1 + F2, r0, h0, hr0, ?_, ?_, ?_, ?_, hHR2, hV2, SameLen_trans hSLI (SameLen_trans hSLf hSL2), hAg⟩
  · rw [hp0]; exact hp2
  · rw [hv0]; exact hv2
  · have : r0.cost ≤ 2520 + (r1.cost + (r2.cost + 0)) := hc0
    have h3 : Enew.length * 24794 ≤ innerOf t * 24794 := Nat.mul_le_mul_right _ hlE
    omega
  · have : r0.wk ≤ 3 + (r1.wk + (r2.wk + 0)) := hw0
    have h3 : Enew.length * 6 ≤ innerOf t * 6 := Nat.mul_le_mul_right _ hlE
    omega

end Proofs.BeatsRep
