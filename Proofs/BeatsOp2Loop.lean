import Proofs.BeatsOp2FrameD
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

/-- Whole `apply_op` loop for chmin (op 0), started at the root. -/
theorem loop2_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (ne : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : addSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hstk : StkRep b 1 [⟨0, 0, n⟩]) (hent : EntRep b 0 []) (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L)
    (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ bf nef F, F ≤ 1 + nodesOf t ∧ RunsE mv F P pre inf n 2 qa qb x b 1 0 bf nef (nodesOf t * 117614 + 4) (nodesOf t * 47 + 0) ∧
      ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp2 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H' := by
  have key := frame2_all Ev hx (fun bf nef => ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp2 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H') t.height t (le_refl _) 1 4 0
  have := key 0 0 n ys b 1 0 [] [] H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh
    (by
      intro bK neK H' Enew hH' hst hen hV' hSL hStar _ hIn hSm _ hAg hlen'
      refine ⟨bK, neK, 1, le_refl _, ?_, H', Enew, hH', by simpa using hen, hV', hSL, hAg, hlen', hIn, by simpa using hStar, by simpa using hSm⟩
      exact runs_exit mv Ev.hnv 0 P pre inf n 2 qa qb x bK neK)
  exact this
end Proofs.BeatsRep
