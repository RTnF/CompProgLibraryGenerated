import Proofs.BeatsExec_ApInitCh0
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem ApInit_body (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hx : s64.valid x = true) (hvl11 : ∀ w ∈ b.sk, i32.valid w = true) (hvl12 : ∀ w ∈ b.sl, i32.valid w = true) (hvl13 : ∀ w ∈ b.sr, i32.valid w = true) (hl11_0 : 0 < (b.sk).length) (hl12_1 : 0 < (b.sl).length) (hl13_2 : 0 < (b.sr).length) (X0 : Int) (hX0 : X0 = 1) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (ApInitBody (mv.nv + pre.length)) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell)] : List Cell))) (VVB b) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) ∧ r.vv = VVB (ui3 (ui2 (ui1 b 0 0) 0 0) 0 (n : Int)) ∧ r.cost ≤ 2520 ∧ r.wk ≤ 3 := by
  classical
  have vX0 : i32.valid X0 = true := by rw [hX0]; exact (by decide)
  obtain ⟨rE, hE, hrE, hpE, hvE, hcE, hwE⟩ : ∃ rE : PRM, pexecM mv fu Sk (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVB (ui3 (ui2 (ui1 b 0 0) 0 0) 0 (n : Int))) = some rE ∧
      rE.ret = none ∧ rE.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) ∧ rE.vv = VVB (ui3 (ui2 (ui1 b 0 0) 0 0) 0 (n : Int)) ∧ rE.cost ≤ 0 ∧ rE.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨c0, hc_0, hrc_0, hpc_0, hvc_0, hcc_0, hwc_0⟩ := ApInit_ch0 mv hnv pre hty hty32 b P inf n op qa qb x hinf hnM hopM hqaM hqbM hx hvl11 hvl12 hvl13 hl11_0 hl12_1 hl13_2 X0 hX0 fu Sk rE hE hrE
  clear hX0
  refine ⟨c0, hc_0, hrc_0, ?_, ?_, ?_, ?_⟩
  · rw [hpc_0, hpE]
  · rw [hvc_0, hvE]
  · omega
  · omega

end Proofs.BeatsExec
