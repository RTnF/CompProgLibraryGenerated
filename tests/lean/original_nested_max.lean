namespace NestedMaxAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall

theorem new0 : OriginalNestedMax.RangeMax_new0 = Proofs.MonoidInstance.MonoidMax_long_long_new0 := rfl
theorem call_new0 (fuel : Nat) (caller : NState) (args : List NArgument) : OriginalNestedMax.RangeMax_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new0.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) new0
theorem new1 : OriginalNestedMax.RangeMax_new1 = Proofs.MonoidInstance.MonoidMax_long_long_new1 := rfl
theorem call_new1 (fuel : Nat) (caller : NState) (args : List NArgument) : OriginalNestedMax.RangeMax_new1.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new1.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) new1
theorem e : OriginalNestedMax.RangeMax_e = Proofs.MonoidInstance.MonoidMax_long_long_e := rfl
theorem call_e (fuel : Nat) (caller : NState) (args : List NArgument) : OriginalNestedMax.RangeMax_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_e.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) e
theorem op : OriginalNestedMax.RangeMax_op = Proofs.MonoidInstance.op_MonoidMax_long_long := rfl
theorem call_op (fuel : Nat) (caller : NState) (args : List NArgument) : OriginalNestedMax.RangeMax_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMax_long_long.callFuel fuel caller args := congrArg (fun p : NProgram => p.callFuel fuel caller args) op
theorem default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedMax.RangeMax_new1.parameters [] = some Sinit ∧
      OriginalNestedMax.RangeMax_new1.callFuel fuel caller [] = .finished (res,.scalar (-9223372036854775808)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  simpa only [new1] using Proofs.MonoidCall.max_default_correct caller valid lengths strict base
theorem new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedMax.RangeMax_new0.parameters [.value e] = some Sinit ∧
      OriginalNestedMax.RangeMax_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  simpa only [new0] using Proofs.MonoidCall.max_new_correct caller e v hs hty value hv valid lengths strict base
theorem e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedMax.RangeMax_e.parameters [] = some Sinit ∧
      OriginalNestedMax.RangeMax_e.callFuel fuel caller [] = .finished (res,.scalar (-9223372036854775808)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  simpa only [e] using Proofs.MonoidCall.max_e_correct caller valid lengths strict base
theorem op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedMax.RangeMax_op.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      OriginalNestedMax.RangeMax_op.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((if x < y then y else x))) ∧
      ScalarPost2 caller Sinit res 0 100 caller.scalars.memory := by
  simpa only [op] using Proofs.MonoidCall.max_op_correct caller sa sb ba bb x y hxv hyv ca cb valid lengths strict base
end NestedMaxAudit
