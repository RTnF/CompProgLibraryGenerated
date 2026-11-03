import Proofs.BeatsCalcRun
import Proofs.BeatsExec_CalcLoopIterS
import Proofs.BeatsExec_CalcLoopIterW0
import Proofs.BeatsExec_CalcLoopIterW1
import Proofs.BeatsExec_CalcLoopIterDset
import Proofs.BeatsExec_CalcLoopIterDadd
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

theorem cstep_stop {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOK b inf sp 0 L W0 W1 W2 S [] H) (hstop : qb ≤ W1 ∨ W2 ≤ qa) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_stop mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hstop H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_whole0 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOK b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hcov : qa ≤ W1 ∧ W2 ≤ qb) (hop0 : op = 0) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp (if x < b.mxv.getD W0 0 then b.mxv.getD W0 0 else x) b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_whole0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hnot hcov hop0 H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_whole1 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOK b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hcov : qa ≤ W1 ∧ W2 ≤ qb) (hop1 : op = 1) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp (if b.mnv.getD W0 0 < x then b.mnv.getD W0 0 else x) b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_whole1 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hnot hcov hop1 H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_down_set {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOK b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hnotc : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) (hmode : b.lval.getD W0 0 ≠ inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)) (hint : b.len.getD W0 0 ≠ 1) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1 + 2) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_down_set mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent
    hnot hnotc hne1 hsp2 Ev.hinfI hmode hlenL hlenR hmode H St.hH hint
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_down_add {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOK b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hnotc : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) (hmode : b.lval.getD W0 0 = inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int))
    (hZ3 : b.mxv.getD W0 0 ≠ inf) (hZ5 : b.mnv.getD W0 0 ≠ inf)
    (hlv1 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0 ≠ inf)
    (hlv2 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0 ≠ inf)
    (hint : b.len.getD W0 0 ≠ 1)
    (hS0 : s64.valid (b.mxv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS1 : b.smx.getD (2 * W0 + 1) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS2 : s64.valid (b.mnv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS3 : b.smn.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS4 : (b.lval.getD (2 * W0 + 1) 0 = inf ∧ b.len.getD (2 * W0 + 1) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS5 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS6 : s64.valid (b.mxv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS7 : b.smx.getD (2 * W0 + 2) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS8 : s64.valid (b.mnv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS9 : b.smn.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS10 : (b.lval.getD (2 * W0 + 2) 0 = inf ∧ b.len.getD (2 * W0 + 2) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS11 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1 + 2) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_down_add mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent
    hnot hnotc hne1 hsp2 Ev.hinfI hmode hlenL hlenR hZ3 hZ5 hlv1 hlv2 H St.hH hint hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9 hS10 hS11
  exact ⟨b', h6, h1, h2, h4, h5⟩

end Proofs.BeatsRep
