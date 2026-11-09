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

/-- `RangeSet<T>::compose`, value component: `noop ? f.v : g.v`-shaped selection. -/
def setComposeV (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar bl true false, .scalar ty true false, .scalar bl true false], .scalar ty,
    (selRet (.variable bl 1) (.variable ty 2) (.variable ty 0))⟩

def setComposeNoop (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar bl true false, .scalar ty true false, .scalar bl true false], .scalar bl,
    (selRet (.variable bl 1) (.variable bl 3) (.variable bl 1))⟩

theorem setComposeV_s64 : setComposeV s64 = Proofs.MonoidLazyInstance.RangeSet_long_long_compose_v := rfl
theorem setComposeNoop_s64 : setComposeNoop s64 = Proofs.MonoidLazyInstance.RangeSet_long_long_compose_noop := rfl

theorem rangeset_compose_v_gen (ty : Ty) (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 n1 v2 n2 : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v1⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,n1⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,v2⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,n2⟩))
    (g1 : ty.valid v1 = true) (g2 : bl.valid n1 = true) (g3 : ty.valid v2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (setComposeV ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      (setComposeV ty).callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if n1 ≠ 0 then v2 else v1)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs4t_correct _ ty ty bl ty bl rfl rfl (selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 n1 v2 n2 c1 c2 c3 c4 valid lengths strict base 1
    (if n1 ≠ 0 then v2 else v1) (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 ty = some v1 :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v1⟩ rfl (P_cell_ty caller s1 ty b1 v1 c1) rfl g1
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 bl = some n1 :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,n1⟩ rfl (P_cell_ty caller s2 bl b2 n1 c2) rfl g2
  have e2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 2 ty = some v2 :=
    penv_ok _ 2 ty ⟨b3.address,false⟩ ⟨ty,v2⟩ rfl (P_cell_ty caller s3 ty b3 v2 c3) rfl g3
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable ty 2) (.variable ty 0) _ n1 v2 v1
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) (by rw [den_variable]; exact e0)
  exact ⟨r, h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_callerP caller⟩

theorem rangeset_compose_noop_gen (ty : Ty) (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 n1 v2 n2 : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v1⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,n1⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,v2⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,n2⟩))
    (g2 : bl.valid n1 = true) (g4 : bl.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (setComposeNoop ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      (setComposeNoop ty).callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if n1 ≠ 0 then n2 else n1)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs4t_correct _ bl ty bl ty bl rfl rfl (selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 n1 v2 n2 c1 c2 c3 c4 valid lengths strict base 1
    (if n1 ≠ 0 then n2 else n1) (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 bl = some n1 :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,n1⟩ rfl (P_cell_ty caller s2 bl b2 n1 c2) rfl g2
  have e3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 3 bl = some n2 :=
    penv_ok _ 3 bl ⟨b4.address,false⟩ ⟨bl,n2⟩ rfl (P_cell_ty caller s4 bl b4 n2 c4) rfl g4
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable bl 3) (.variable bl 1) _ n1 n2 n1
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e3) (by rw [den_variable]; exact e1)
  exact ⟨r, h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_callerP caller⟩

end Proofs.GenericLazy
