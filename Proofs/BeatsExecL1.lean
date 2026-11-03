import Proofs.BeatsExecL0
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec

theorem den_idx_lit0 (mv : MV) (P L : List Cell) :
    (NExpr.cast u64 (NExpr.literal i32 (0 : Int))).denote (penvN mv.nv (gS P L)) = some ((0 : Nat) : Int) := by
  rw [den_cast, den_literal, if_pos (by decide : i32.valid (0 : Int) = true), Option.bind_some]
  rw [convert_u64]; rfl

end Proofs.BeatsExec
