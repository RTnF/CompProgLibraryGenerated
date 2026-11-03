import Proofs.SegmentTreeExec
import Proofs.Generated.IsPrime

namespace Proofs.IsPrimeBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)

abbrev zU : NExpr := .cast u64 (.literal i32 0)
abbrev oU : NExpr := .cast u64 (.literal i32 1)
abbrev tU : NExpr := .cast u64 (.literal i32 2)
abbrev vU (nv k : Nat) : NExpr := .variable u64 (nv + k)
abbrev oddE (nv k : Nat) : NExpr := .binary bT .eq (.divrem u64 true (vU nv k) tU) oU
abbrev halfS (nv k : Nat) : NStmt := .assign (nv + k) u64 (.divrem u64 false (vU nv k) tU)

/-- `mul_mod_u64` with the parameters `a', b', m'` in the cells `b, b + 1, b + 2`; `rest` follows the loop. -/
abbrev mulAdd (nv b u v : Nat) : Command :=
  .sequence (.primitive (.declare u64 true (.binary u64 .add (vU nv u) (vU nv v))))
    (.sequence (.branch (.binary bT .ge (vU nv u) (.binary u64 .sub (vU nv (b + 2)) (vU nv v)))
      (.sequence (.scope (.sequence (.primitive (.assign (nv + (b + 6)) u64
        (.binary u64 .sub (vU nv u) (.binary u64 .sub (vU nv (b + 2)) (vU nv v))))) Sk)) Sk) Sk) Sk)
abbrev mulLoop (nv b : Nat) : Command :=
  .sequence (.scope (.sequence
    (.branch (oddE nv (b + 5))
      (.sequence (.scope (.sequence (.primitive (.declare u64 true (.binary u64 .add (vU nv (b + 3)) (vU nv (b + 4)))))
        (.sequence (.branch (.binary bT .ge (vU nv (b + 3)) (.binary u64 .sub (vU nv (b + 2)) (vU nv (b + 4))))
          (.sequence (.scope (.sequence (.primitive (.assign (nv + (b + 6)) u64
            (.binary u64 .sub (vU nv (b + 3)) (.binary u64 .sub (vU nv (b + 2)) (vU nv (b + 4)))))) Sk)) Sk) Sk)
          (.sequence (.primitive (.assign (nv + (b + 3)) u64 (vU nv (b + 6)))) Sk)))) Sk) Sk)
    (.sequence (.primitive (.declare u64 true (.binary u64 .add (vU nv (b + 4)) (vU nv (b + 4)))))
      (.sequence (.branch (.binary bT .ge (vU nv (b + 4)) (.binary u64 .sub (vU nv (b + 2)) (vU nv (b + 4))))
        (.sequence (.scope (.sequence (.primitive (.assign (nv + (b + 6)) u64
          (.binary u64 .sub (vU nv (b + 4)) (.binary u64 .sub (vU nv (b + 2)) (vU nv (b + 4)))))) Sk)) Sk) Sk)
        (.sequence (.primitive (.assign (nv + (b + 4)) u64 (vU nv (b + 6))))
          (.sequence (.primitive (halfS nv (b + 5))) Sk)))))) Sk
abbrev mulBody (nv b : Nat) (rest : Command) : Command :=
  .sequence (.primitive (.declare u64 true zU))
    (.sequence (.primitive (.declare u64 true (vU nv b)))
      (.sequence (.primitive (.declare u64 true (vU nv (b + 1))))
        (.sequence (.whileLoop (.binary bT .ne (vU nv (b + 5)) zU) (mulLoop nv b)) rest)))

/-- The inlined call `tgt = mul_mod_u64(cell ia, cell ib, cell im)`, followed by `K`. -/
abbrev callMul (nv bB ia ib im tgt : Nat) (K : Command) : Command :=
  .sequence (.primitive (.declare u64 true (vU nv ia))) (.sequence (.primitive (.declare u64 true (vU nv ib)))
    (.sequence (.primitive (.declare u64 true (vU nv im)))
      (mulBody nv bB (.sequence (.primitive (.declare u64 true (vU nv (bB + 3))))
        (.sequence (.primitive (.declare u64 true (vU nv (bB + 6))))
          (.sequence (.primitive (.assign (nv + tgt) u64 (vU nv (bB + 7)))) K))))))

abbrev powLoop (nv b : Nat) : Command :=
  .sequence (.scope (.sequence
    (.branch (oddE nv (b + 5)) (.sequence (.scope (callMul nv (b + 6) (b + 3) (b + 4) (b + 2) (b + 3) Sk)) Sk) Sk)
    (callMul nv (b + 6) (b + 4) (b + 4) (b + 2) (b + 4) (.sequence (.primitive (halfS nv (b + 5))) Sk)))) Sk
abbrev powBody (nv b : Nat) (rest : Command) : Command :=
  .sequence (.primitive (.declare u64 true oU))
    (.sequence (.primitive (.declare u64 true (vU nv b)))
      (.sequence (.primitive (.declare u64 true (vU nv (b + 1))))
        (.sequence (.whileLoop (.binary bT .ne (vU nv (b + 5)) zU) (powLoop nv b)) rest)))

theorem body_eqPowMod : Proofs.IsPrimeInstance.pow_mod_u64.body = powBody 0 0 (.sequence (.primitive (.ret (vU 0 3))) Sk) := rfl

theorem body_eqMul : Proofs.IsPrimeInstance.mul_mod_u64.body = mulBody 0 0 (.sequence (.primitive (.ret (vU 0 3))) Sk) := rfl

/-- The inlined call `T x = mul_mod_u64(cell ia, cell ib, cell im)` (the result is the new cell `bB + 7`), followed by `K`. -/
abbrev callMulD (nv bB ia ib im : Nat) (K : Command) : Command :=
  .sequence (.primitive (.declare u64 true (vU nv ia))) (.sequence (.primitive (.declare u64 true (vU nv ib)))
    (.sequence (.primitive (.declare u64 true (vU nv im)))
      (mulBody nv bB (.sequence (.primitive (.declare u64 true (vU nv (bB + 3))))
        (.sequence (.primitive (.declare u64 true (vU nv (bB + 6)))) K)))))
abbrev callPowD (nv bB ix iy im : Nat) (K : Command) : Command :=
  .sequence (.primitive (.declare u64 true (vU nv ix))) (.sequence (.primitive (.declare u64 true (vU nv iy)))
    (.sequence (.primitive (.declare u64 true (vU nv im)))
      (powBody nv bB (.sequence (.primitive (.declare u64 true (vU nv (bB + 3))))
        (.sequence (.primitive (.declare u64 true (vU nv (bB + 6)))) K)))))

abbrev witLoop (nv : Nat) : Command :=
  .sequence (.scope (callMulD nv 15 12 12 0
    (.sequence (.primitive (.assign (nv + 12) u64 (vU nv 22)))
      (.sequence (.branch (.binary bT .eq (vU nv 12) (.binary u64 .sub (vU nv 0) oU))
        (.sequence (.scope (.sequence (.primitive (.assign (nv + 13) bT (.literal bT 0))) Sk)) Sk) Sk)
      (.sequence (.primitive (.assign (nv + 14) i32 (.binary i32 .add (.variable i32 (nv + 14)) (.literal i32 1)))) Sk))))) Sk
abbrev witW2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 1)))
    (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.whileLoop (.logical true (.binary bT .lt (.variable i32 (nv + 14)) (.binary i32 .sub (.variable i32 (nv + 2)) (.literal i32 1)))
          (.variable bT (nv + 13))) (witLoop nv))
        (.sequence (.branch (.variable bT (nv + 13))
          (.sequence (.scope (.sequence (.primitive (.assign (nv + 4) bT (.literal bT 1))) Sk)) Sk) Sk) Sk)))
abbrev witBody (nv : Nat) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 0)))
    (callPowD nv 5 3 1 0
      (.sequence (.branch (.binary bT .ne (vU nv 12) oU)
        (.sequence (.scope (.sequence (.branch (.binary bT .ne (vU nv 12) (.binary u64 .sub (vU nv 0) oU))
          (.sequence (.scope (witW2 nv)) Sk) Sk) Sk)) Sk) Sk)
        (.sequence (.primitive (.ret (.variable bT (nv + 4)))) Sk)))

theorem body_eqWit : Proofs.IsPrimeInstance.mr_witness.body = witBody 0 := rfl

end Proofs.IsPrimeBody

