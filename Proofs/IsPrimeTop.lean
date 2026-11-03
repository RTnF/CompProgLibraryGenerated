import Proofs.IsPrimeWit
import Proofs.Generated.IsPrime

namespace Proofs.IsPrimeTop
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.CppState (Cell)
open Proofs.ForLoopB
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.IsPrimeBody Proofs.IsPrimeExec Proofs.IsPrimeWit

abbrev cU (k : Int) : NExpr := .cast u64 (.literal i32 k)
abbrev blk (ss : Command) : Command := .sequence (.scope ss) Sk
abbrev assignP (nv cp : Nat) (v : Int) : Command := blk (.sequence (.primitive (.assign (nv + cp) u64 (cU v))) Sk)
abbrev baseIf (nv ci cp : Nat) (k v : Int) (rest : Command) : Command :=
  .sequence (.branch (.binary bT .eq (.variable i32 (nv + ci)) (.literal i32 k)) (assignP nv cp v) Sk) rest
abbrev baseTbl : List (Int × Int) := [(0, 2), (1, 3), (2, 5), (3, 7), (4, 11), (5, 13), (6, 17), (7, 19), (8, 23), (9, 29), (10, 31)]
abbrev baseChain (nv ci cp : Nat) (rest : Command) : Command :=
  baseTbl.foldr (fun kv acc => baseIf nv ci cp kv.1 kv.2 acc) rest

abbrev mrBaseBody (nv : Nat) : Command :=
  .sequence (.primitive (.declare u64 true (cU 37)))
    (baseChain nv 0 1 (.sequence (.primitive (.ret (.variable u64 (nv + 1)))) Sk))

theorem body_eqBase : Proofs.IsPrimeInstance.mr_base.body = mrBaseBody 0 := rfl


abbrev iV (nv k : Nat) : NExpr := .variable i32 (nv + k)
abbrev bV (nv k : Nat) : NExpr := .variable bT (nv + k)
abbrev assign1 (nv : Nat) (v : Int) : Command := blk (.sequence (.primitive (.assign (nv + 1) bT (.literal bT v))) Sk)

abbrev witR (nv : Nat) : Command :=
  .sequence (.primitive (.declare bT true (bV nv 13)))
    (.sequence (.primitive (.declare bT true (bV nv 22)))
      (.sequence (.branch (bV nv 23) (assign1 nv 0) Sk) Sk))

abbrev witInl (nv : Nat) : Command :=
  .sequence (.primitive (.declare u64 true (vU nv 0)))
    (.sequence (.primitive (.declare u64 true (vU nv 3)))
      (.sequence (.primitive (.declare i32 true (iV nv 2)))
        (.sequence (.primitive (.declare u64 true (vU nv 8))) (witPreK nv 9 (witR nv)))))

abbrev incI (nv c : Nat) : Command :=
  .primitive (.assign (nv + c) i32 (.binary i32 .add (iV nv c) (.literal i32 1)))

abbrev iterStmts (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (iV nv 4)))
    (.sequence (.primitive (.declare u64 true (cU 37)))
      (baseChain nv 5 6
        (.sequence (.primitive (.declare u64 true (vU nv 6)))
          (.sequence (.primitive (.declare u64 true (vU nv 7)))
            (.sequence (.branch (.binary bT .le (vU nv 8) (.binary u64 .sub (vU nv 0) (cU 2))) (blk (witInl nv)) Sk)
              Sk)))))

abbrev forLoop (nv : Nat) : Command :=
  .scope (.sequence (.primitive (.declare i32 true (.literal i32 0)))
    (.sequence (.whileLoop (.binary bT .lt (iV nv 4) (.literal i32 12)) (.sequence (.scope (iterStmts nv)) (.sequence (incI nv 4) Sk))) Sk))

abbrev decLoop (nv : Nat) : Command :=
  .whileLoop (.binary bT .eq (.divrem u64 true (vU nv 3) (cU 2)) (cU 0))
    (blk (.sequence (.primitive (.assign (nv + 3) u64 (.divrem u64 false (vU nv 3) (cU 2))))
      (.sequence (incI nv 2) Sk)))

abbrev else2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0)))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (vU nv 0) (cU 1))))
      (.sequence (decLoop nv) (.sequence (forLoop nv) Sk)))

abbrev isBodyT (nv : Nat) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 1)))
    (.sequence (.branch (.binary bT .eq (vU nv 0) (cU 2)) (assign1 nv 1)
        (blk (.sequence (.branch (.logical false (.binary bT .eq (.divrem u64 true (vU nv 0) (cU 2)) (cU 0))
              (.binary bT .le (vU nv 0) (cU 1))) (assign1 nv 0) (blk (else2 nv))) Sk)))
      (.sequence (.primitive (.ret (bV nv 1))) Sk))


theorem body_eqIsPrime : Proofs.IsPrimeInstance.is_prime.body = isBodyT 0 := rfl

end Proofs.IsPrimeTop
