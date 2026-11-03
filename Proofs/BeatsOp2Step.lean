import Proofs.BeatsStep
import Proofs.BeatsExec_ApplyLoopIterW2
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

theorem step_whole2 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOK b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hwhole : wholeP op qa qb x (decNd b W0) W1 W2) (hop2 : op = 2) (hxne : x ≠ inf) (hadd7 : (b.lval.getD W0 0) ≠ inf → (b.lval.getD W0 0) + x ≠ inf)
    (hS0 : s64.valid ((b.mxv.getD W0 0) + x) = true) (hS1 : (((b.smx.getD W0 0) ≠ (-inf))) → s64.valid ((b.smx.getD W0 0) + x) = true)
    (hS2 : s64.valid ((b.mnv.getD W0 0) + x) = true) (hS3 : (((b.smn.getD W0 0) ≠ inf)) → s64.valid ((b.smn.getD W0 0) + x) = true)
    (hS4 : ((((b.lval.getD W0 0) = inf) ∧ ((b.len.getD W0 0) ≠ 1))) → s64.valid ((b.ladd.getD W0 0) + x) = true)
    (hS5 : ((((b.lval.getD W0 0) ≠ inf) ∧ ((b.len.getD W0 0) ≠ 1))) → s64.valid ((b.lval.getD W0 0) + x) = true) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' (H.set W0 (Cellh.addC x (H W0))) ∧
      StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_whole2 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hnot hwhole hop2 hxne Ev.hinfI hadd7 H St.hH hS0 hS1 hS2 hS3 hS4 hS5
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩


end Proofs.BeatsRep
