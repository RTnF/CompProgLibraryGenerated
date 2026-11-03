import Proofs.BeatsLoopExec
import Proofs.BeatsRepInv
import Proofs.BeatsExec_ApplyLoopIterW0
import Proofs.BeatsExec_ApplyLoopIterDset
import Proofs.BeatsExec_ApplyLoopIterDadd
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

/-- One iteration of the loop body, from `(b, sp, ne)` to `(b', sp', ne')`, for every fuel. -/
def Iter (mv : MV) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp ne : Nat) (b' : BS) (sp' ne' : Nat) : Prop :=
  ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (ApplyLoopBody (mv.nv + pre.length))) Sk)
      (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r ∧ r.ret = none ∧
    r.ps = gS P (pre ++ LCells inf n op qa qb x sp' ne') ∧ r.vv = VVB b' ∧ r.cost ≤ 117610 ∧ r.wk ≤ 47

/-- The loop run from `(b, sp, ne)` ends in `(bf, nef)`. -/
def RunsE (mv : MV) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp ne : Nat) (bf : BS) (nef C W : Nat) : Prop :=
  RunsF mv fu P pre inf n op qa qb x b sp ne (gS P (pre ++ LCells inf n op qa qb x 0 nef)) (VVB bf) C W

theorem runs_of_iter (mv : MV) (hnv : mv.nv = 15) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b b' : BS)
    (sp ne sp' ne' : Nat) (hspM : sp < M31) (hsp : 0 < sp) (hit : Iter mv P pre inf n op qa qb x b sp ne b' sp' ne')
    (F : Nat) (bf : BS) (nef C W : Nat) (hrest : RunsE mv F P pre inf n op qa qb x b' sp' ne' bf nef C W) :
    RunsE mv (F + 1) P pre inf n op qa qb x b sp ne bf nef (117614 + C) (47 + W) := by
  obtain ⟨r1, h1, hret, hps, hvv, hc, hw⟩ := hit (F + 1)
  have := runs_step mv hnv F P pre inf n op qa qb x b b' sp ne sp' ne' hspM hsp r1 h1 hret hps hvv 117610 47 hc hw _ _ C W hrest
  unfold RunsE
  have e : 4 + 117610 + C = 117614 + C := by omega
  rw [e] at this
  exact this

/-- The constants of one operation on one tree. -/
structure Env (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (L : Nat) : Prop where
  hnv : mv.nv = 15
  hty : ∀ v, v < 9 → mv.ty v = s64
  hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32
  hinf : s64.valid inf = true
  hninf : s64.valid (-inf) = true
  hnM : n < M31
  hopM : op < M31
  hqaM : qa < M31
  hqbM : qb < M31
  hx : s64.valid x = true
  hLM : L < M31
  hinfI : inf = INF

/-- The facts about the current state that every iteration needs. -/
structure StateOK (b : BS) (inf : Int) (sp ne : Nat) (L : Nat) (W0 W1 W2 : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop where
  hV : ValidOK b
  hLens : Lens b L
  hk : 2 * W0 + 2 < L
  hsp : 0 < sp
  hspL : sp + 2 ≤ L
  hneL : ne + 1 < L
  hlohi : W1 + W2 < M31
  hstk : StkRep b sp (⟨W0, W1, W2⟩ :: S)
  hent : EntRep b ne E
  hH : HRel inf b H

theorem step_stop {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOK b inf sp ne L W0 W1 W2 S E H) (hstop : stopP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧
      ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_stop mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hstop hop H St.hH
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_whole0 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOK b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hwhole : wholeP op qa qb x (decNd b W0) W1 W2) (hop0 : op = 0) (hxne : x ≠ inf) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' (H.set W0 (Cellh.capMaxC x (H W0))) ∧
      StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_whole0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hnot hwhole hop0 hxne H St.hH
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_down_set {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOK b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hnotw : ¬ wholeP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) (hmode : b.lval.getD W0 0 ≠ inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)) (hint : b.len.getD W0 0 ≠ 1) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1 + 2) (ne + 1) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧
      EntRep b' (ne + 1) (W0 :: E) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : ne + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_down_set mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent
    hnot hnotw hop hne1 hsp2 Ev.hinfI hmode hlenL hlenR hmode H St.hH hint
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_down_add {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOK b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hnotw : ¬ wholeP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) (hmode : b.lval.getD W0 0 = inf)
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
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1 + 2) (ne + 1) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧
      EntRep b' (ne + 1) (W0 :: E) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : ne + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hLM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_down_add mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent
    hnot hnotw hop hne1 hsp2 Ev.hinfI hmode hlenL hlenR hZ3 hZ5 hlv1 hlv2 H St.hH hint hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9 hS10 hS11
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

end Proofs.BeatsRep
