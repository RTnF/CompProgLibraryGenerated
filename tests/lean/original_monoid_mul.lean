namespace OriginalMonoidMulAudit
open Proofs
open Proofs.CppNestedProgram Proofs.CppNestedCall
theorem new0 : Original_monoid_mul.MonoidMul_long_long_new0 = Proofs.MonoidInstance.MonoidMul_long_long_new0 := rfl
theorem call_new0 (fuel : Nat) (caller : NState) (args : List NArgument) : Original_monoid_mul.MonoidMul_long_long_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMul_long_long_new0.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) new0
theorem e : Original_monoid_mul.MonoidMul_long_long_e = Proofs.MonoidInstance.MonoidMul_long_long_e := rfl
theorem call_e (fuel : Nat) (caller : NState) (args : List NArgument) : Original_monoid_mul.MonoidMul_long_long_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMul_long_long_e.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) e
theorem op : Original_monoid_mul.MonoidMul_long_long_op = Proofs.MonoidInstance.op_MonoidMul_long_long := rfl
theorem call_op (fuel : Nat) (caller : NState) (args : List NArgument) : Original_monoid_mul.MonoidMul_long_long_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMul_long_long.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) op
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedSim
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.GroupCall
open Proofs.ModIntCall Proofs.MonoidCall Proofs.ExtremaCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.DoublingNested
theorem default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Original_monoid_mul.MonoidMul_long_long_new1.parameters [] = some Sinit ∧
      Original_monoid_mul.MonoidMul_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.GroupCall.default_correct _ false (.cast s64 (.literal i32 1)) 1 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base
end OriginalMonoidMulAudit
