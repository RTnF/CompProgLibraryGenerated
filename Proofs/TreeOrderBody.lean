import Proofs.TreeFullDpBody
import Proofs.Generated.TreeOrder

namespace Proofs.TreeOrderBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.TreeFullDpBody (vI rdI incI isChild)

/-! ### `tree_order` (nv = 4: head, target, parent, ord). Cells: 0 = root, 1 = n, 2 = cnt, 3 = i, 4 = v, 5 = p, 6 = w. -/

abbrev TOact (nv : Nat) : Command :=
  .sequence (.primitive (.write (.local 3) i32 (.cast u64 (vI nv 2)) (vI nv 6))) (.sequence (.primitive (incI nv 2)) Sk)
abbrev TOiter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 1 (vI nv 5))))
    (.sequence (.branch (isChild nv 4 6) (.sequence (.scope (TOact nv)) Sk) Sk) Sk)
abbrev TObody (nv : Nat) : Command := .sequence (.scope (TOiter nv)) (.sequence (.primitive (incI nv 5)) Sk)
abbrev TOcond (nv : Nat) : NExpr := .binary bT .lt (vI nv 5) (rdI 0 (.binary i32 .add (vI nv 4) Proofs.TreeFullDpBody.lit1))
abbrev TOinner (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 0 (vI nv 4)))) (.sequence (.whileLoop (TOcond nv) (TObody nv)) Sk)
abbrev TOstep (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 3 (vI nv 3)))) (.sequence (.scope (TOinner nv)) Sk)
abbrev TOouterBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (.binary bT .lt (vI nv 3) (vI nv 2)) (.sequence (.scope (TOstep nv)) Sk) Sk) Sk))
    (.sequence (.primitive (incI nv 3)) Sk)
abbrev TOouter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0)))
    (.sequence (.whileLoop (.binary bT .lt (vI nv 3) (vI nv 1)) (TOouterBody nv)) Sk)
abbrev bodyTO (nv : Nat) : Command :=
  .sequence (.primitive (.write (.local 3) i32 (.cast u64 (.literal i32 0)) (vI nv 0)))
    (.sequence (.primitive (.declare i32 true (.literal i32 1))) (.sequence (.scope (TOouter nv)) Sk))

theorem body_eqTO : Proofs.TreeOrderInstance.tree_order.body = bodyTO 4 := rfl

end Proofs.TreeOrderBody
