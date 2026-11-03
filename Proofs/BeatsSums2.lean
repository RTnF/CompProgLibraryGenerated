import Proofs.BeatsSums
import Proofs.BeatsAssemble
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

theorem rangeMin_length (lo a b : Nat) (x : Int) (ys : List Int) : (rangeMin lo a b x ys).length = ys.length := by
  unfold rangeMin; simp

/-- At a node whose two children have been fully processed, `update` computes valid sums. -/
theorem sumOK_node (qa qb : Nat) (x : Int) (hx1 : -INF < x) (nd : Nd) (tg : Tag) (l r : BT) (k lo hi : Nat) (xl xr : List Int)
    (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (hshl : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel) (hshr : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel)
    (hsafel : chminSafe qa qb x (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : chminSafe qa qb x (applyTag tg nd r) ((lo + hi) / 2) hi) (hlh : lo ≤ hi ∧ 2 * hi < M31) (G : Heap)
    (hgl : Agree G (travBT (clsMin qa qb x) (capMaxBT x) (applyTag tg nd l) lo ((lo + hi) / 2)) (2 * k + 1))
    (hgr : Agree G (travBT (clsMin qa qb x) (capMaxBT x) (applyTag tg nd r) ((lo + hi) / 2) hi) (2 * k + 2)) :
    SumOK G k := by
  have il := BeatsModel.Inv.chmin qa qb x hx1 _ lo ((lo + hi) / 2) xl hinvl hshl hsafel
  have ir := BeatsModel.Inv.chmin qa qb x hx1 _ ((lo + hi) / 2) hi xr hinvr hshr hsafer
  rw [chminBT_eq] at il ir
  have dl : Desc (G (2 * k + 1)).1 (rangeMin lo qa qb x xl) := by rw [agree_root G _ _ hgl]; exact il.desc
  have dr : Desc (G (2 * k + 2)).1 (rangeMin ((lo + hi) / 2) qa qb x xr) := by rw [agree_root G _ _ hgr]; exact ir.desc
  refine SumOK_of_desc G k _ _ dl dr ?_
  rw [rangeMin_length, rangeMin_length, Inv.size hinvl, Inv.size hinvr, BT.size_skel, BT.size_skel, skel_applyTag, skel_applyTag]
  have h1 := hshl.size
  have h2 := hshr.size
  rw [skel_applyTag] at h1 h2
  have := hlh.1; have := hlh.2
  omega

end Proofs.BeatsRep
