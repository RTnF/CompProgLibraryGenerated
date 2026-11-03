import Proofs.BeatsSums2
import Proofs.BeatsAssemble
import Proofs.BeatsAddSet
import Proofs.BeatsLoop6
import Proofs.BeatsRepInv
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

theorem rangeMapA_length (f : Int → Int) (lo a b : Nat) (ys : List Int) : (rangeMap f lo a b ys).length = ys.length := by
  unfold rangeMap; simp

theorem addSafeRec_down (a b : Nat) (x : Int) (nd : Nd) (tg : Tag) (l r : BT) (lo hi : Nat)
    (hc : clsRange a b nd lo hi = Cls.down) (h : addSafeRec a b x (.node nd tg l r) lo hi) :
    PushSafe (.node nd tg l r) ∧ addSafeRec a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      addSafeRec a b x (applyTag tg nd r) ((lo + hi) / 2) hi := by
  unfold clsRange at hc
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · rw [if_pos h1] at hc; cases hc
  · rw [if_neg h1] at hc
    by_cases h2 : a ≤ lo ∧ hi ≤ b
    · rw [if_pos h2] at hc; cases hc
    · unfold addSafeRec at h
      rw [if_neg h1, if_neg h2] at h
      exact h

theorem addSafe_of_whole (a b : Nat) (x : Int) (t : BT) (lo hi : Nat) (hc : clsRange a b t.nd lo hi = Cls.whole)
    (h : addSafeRec a b x t lo hi) : AddSafe x t := by
  unfold clsRange at hc
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · rw [if_pos h1] at hc; cases hc
  · rw [if_neg h1] at hc
    by_cases h2 : a ≤ lo ∧ hi ≤ b
    · cases t with
      | leaf nd => unfold addSafeRec at h; rw [if_neg h1] at h; exact h
      | node nd tg l r => unfold addSafeRec at h; rw [if_neg h1, if_pos h2] at h; exact h
    · rw [if_neg h2] at hc; cases hc

/-- At a node whose two children have been fully processed, `update` computes valid sums. -/
theorem sumOK_node2 (qa qb : Nat) (x : Int) (hx1 : -INF < x ∧ x < INF) (nd : Nd) (tg : Tag) (l r : BT) (k lo hi : Nat) (xl xr : List Int)
    (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (hshl : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel) (hshr : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel)
    (hsafel : addSafeRec qa qb x (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : addSafeRec qa qb x (applyTag tg nd r) ((lo + hi) / 2) hi) (hlh : lo ≤ hi ∧ 2 * hi < M31) (G : Heap)
    (hgl : Agree G (travBT (clsRange qa qb) (addBT x) (applyTag tg nd l) lo ((lo + hi) / 2)) (2 * k + 1))
    (hgr : Agree G (travBT (clsRange qa qb) (addBT x) (applyTag tg nd r) ((lo + hi) / 2) hi) (2 * k + 2)) :
    SumOK G k := by
  have il := BeatsModel.Inv.add_range qa qb x _ lo ((lo + hi) / 2) xl hinvl hshl hsafel
  have ir := BeatsModel.Inv.add_range qa qb x _ ((lo + hi) / 2) hi xr hinvr hshr hsafer
  rw [addRec_eq] at il ir
  have dl : Desc (G (2 * k + 1)).1 (rangeMap (fun v => v + x) lo qa qb xl) := by rw [agree_root G _ _ hgl]; exact il.desc
  have dr : Desc (G (2 * k + 2)).1 (rangeMap (fun v => v + x) ((lo + hi) / 2) qa qb xr) := by rw [agree_root G _ _ hgr]; exact ir.desc
  refine SumOK_of_desc G k _ _ dl dr ?_
  rw [rangeMapA_length, rangeMapA_length, Inv.size hinvl, Inv.size hinvr, BT.size_skel, BT.size_skel, skel_applyTag, skel_applyTag]
  have h1 := hshl.size
  have h2 := hshr.size
  rw [skel_applyTag] at h1 h2
  have := hlh.1; have := hlh.2
  omega

end Proofs.BeatsRep
