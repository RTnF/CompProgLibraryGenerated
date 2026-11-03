import Proofs.BeatsCtorPhase2
import Proofs.BeatsCtorBase
import Proofs.BeatsRep
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

theorem getD_set_ite (l : List Int) (i : Nat) (v : Int) (hi : i < l.length) (j : Nat) :
    (l.set i v).getD j 0 = if j = i then v else l.getD j 0 := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl]; exact getD_set_same l j v hi
  · rw [if_neg h]; exact getD_set_diff l i j v (Ne.symm h)

/-- The arrays of the constructor at the head of the first loop (index `k`, `ne` entered nodes). -/
structure CtInv (a : List Int) (n : Nat) (inf : Int) (b : BS) (k ne : Nat) : Prop where
  hent : EntRep b ne (LLr n k)
  hlo : ∀ j, b.lo.getD j 0 = (((if j ≤ 2 * k then (rngOf n j).1 else 0 : Nat)) : Int)
  hhi : ∀ j, b.hi.getD j 0 = (((if j ≤ 2 * k then (rngOf n j).2 else 0 : Nat)) : Int)
  hlen : ∀ j, b.len.getD j 0 = if j < k then (((rngOf n j).2 - (rngOf n j).1 : Nat) : Int) else 0
  hmx : ∀ j, b.mxv.getD j 0 = if j < k ∧ isLeafAt n j then a.getD (rngOf n j).1 0 else 0
  hmn : ∀ j, b.mnv.getD j 0 = if j < k ∧ isLeafAt n j then a.getD (rngOf n j).1 0 else 0
  hsmx : ∀ j, b.smx.getD j 0 = if j < k ∧ isLeafAt n j then -inf else 0
  hsmn : ∀ j, b.smn.getD j 0 = if j < k ∧ isLeafAt n j then inf else 0
  hmc : ∀ j, b.mxc.getD j 0 = if j < k ∧ isLeafAt n j then 1 else 0
  hmnc : ∀ j, b.mnc.getD j 0 = if j < k ∧ isLeafAt n j then 1 else 0
  hladd : ∀ j, b.ladd.getD j 0 = 0
  hlval : ∀ j, j < b.lval.length → b.lval.getD j 0 = inf

end Proofs.BeatsRep
