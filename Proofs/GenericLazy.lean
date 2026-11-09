import Proofs.GenericCall
import Proofs.MonoidLazyCall

/-! `monoid_lazy` results for an arbitrary scalar value type `T` (`Ty`).
`RangeSum.size` is always `int`, so `op_size` is already `T`-independent. -/

namespace Proofs.GenericLazy
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.ModIntCall
open Proofs.PexecKit Proofs.GroupCall Proofs.DoublingCall Proofs.QuotientSearch
open Proofs.IntervalCall Proofs.ScalarRefs Proofs.GenericCall Proofs.MonoidLazyCall Proofs.DoublingNested Proofs.IntSim Proofs.ExtremaCall
open Proofs.CppState (Cell)

/-- `friend RangeSum op(a, b)`, `.x` component, for `RangeSum<T>`. -/
def sumOpX (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar i32 true false, .scalar ty true false, .scalar i32 true false], .scalar ty,
    (.sequence (.primitive (.ret (.binary ty .add (.variable ty 0) (.variable ty 2)))) (.primitive .skip))⟩

theorem sumOpX_s64 : sumOpX s64 = Proofs.MonoidLazyInstance.RangeSum_long_long_op_x := rfl

theorem rangesum_op_x_gen (ty : Ty) (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : ty.valid v1 = true) (g3 : ty.valid v3 = true) (gs : ty.valid (v1 + v3) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (sumOpX ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      (sumOpX ty).callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v1 + v3)) ∧
      ScalarPost2 caller Sinit res 0 72 caller.scalars.memory := by
  refine refs4t_correct _ ty ty i32 ty i32 rfl rfl (by simp [sumOpX, Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4
    b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v1 + v3) gs 12 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 ty = some v1 :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v1⟩ rfl (P_cell_ty caller s1 ty b1 v1 c1) rfl g1
  have e2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 2 ty = some v3 :=
    penv_ok _ 2 ty ⟨b3.address,false⟩ ⟨ty,v3⟩ rfl (P_cell_ty caller s3 ty b3 v3 c3) rfl g3
  have den : (NExpr.binary ty .add (.variable ty 0) (.variable ty 2)).denote
      (penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩) = some (v1 + v3) := by
    rw [den_binary, den_variable, den_variable, e0, e2]
    simp only [Option.bind_some]
    exact convG ty _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen (.binary ty .add (.variable ty 0) (.variable ty 2)) (v1 + v3) _ den (by simp [NExpr.nodes])
  exact ⟨r, h1, h2, h3, by simp at h4; omega, by rw [h5]; exact take_callerP caller⟩

end Proofs.GenericLazy
