import Proofs.MatMulGen

namespace Proofs.MatPowBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.MatMulGen (BiG)

/-! ### `mat_pow` (nv = 4: a, r, y, t).  Cells: 0 = n, 1 = e, 2 = m. -/

abbrev ixC (nv p : Nat) : NExpr := .cast u64 (.variable i32 (nv + p))
/-- `dst[i] = src[i]` for `i < m`. -/
abbrev copyF (nv p bnd dst src : Nat) : Command :=
  forStmtB nv p bnd (.sequence (.primitive (.write (.local dst) u64 (ixC nv p) (.read u64 (.local src) (ixC nv p)))) (.primitive .skip))
/-- `dst[i] = 0` for `i < m`. -/
abbrev zeroF (nv p bnd dst : Nat) : Command :=
  forStmtB nv p bnd (.sequence (.primitive (.write (.local dst) u64 (ixC nv p) (.cast u64 (.literal i32 0)))) (.primitive .skip))
/-- `dst[i * n + i] = 1` for `i < n`. -/
abbrev diagF (nv p bnd dst : Nat) : Command :=
  forStmtB nv p bnd (.sequence (.primitive (.write (.local dst) u64
    (.cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (nv + p)) (.variable i32 (nv + bnd))) (.variable i32 (nv + p))))
    (.cast u64 (.literal i32 1)))) (.primitive .skip))
abbrev oddCond (nv : Nat) : NExpr :=
  .binary bT .eq (.divrem u64 true (.variable u64 (nv + 1)) (.cast u64 (.literal i32 2))) (.cast u64 (.literal i32 1))
abbrev halveE (nv : Nat) : NStmt :=
  .assign (nv + 1) u64 (.divrem u64 false (.variable u64 (nv + 1)) (.cast u64 (.literal i32 2)))
/-- `mat_mul(ia, ib, ic, n)` inlined, followed by the copy `dst[i] = t[i]`. -/
abbrev mulCopy (nv ia ib ic dst : Nat) (rest : Command) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + 0))))
    (.sequence (forStmtB nv 4 3 (BiG nv 3 ia ib ic)) (.sequence (copyF nv 4 2 dst ic) rest))
abbrev powLoopBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (oddCond nv) (.sequence (.scope (mulCopy nv 1 2 3 1 Sk)) Sk) Sk)
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 0))))
      (.sequence (forStmtB nv 4 3 (BiG nv 3 2 2 3)) (.sequence (copyF nv 4 2 2 3)
        (.sequence (.primitive (halveE nv)) Sk)))))) Sk
abbrev bodyPow (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .mul (.variable i32 (nv + 0)) (.variable i32 (nv + 0)))))
    (.sequence (copyF nv 3 2 2 0) (.sequence (zeroF nv 3 2 1) (.sequence (diagF nv 3 0 1)
      (.sequence (.whileLoop (.binary bT .ne (.variable u64 (nv + 1)) (.cast u64 (.literal i32 0))) (powLoopBody nv)) Sk))))

theorem body_eqPow : Proofs.SquareMatrixInstance.mat_pow_std_vector_unsigned_long_long.body = bodyPow 4 := rfl

end Proofs.MatPowBody
