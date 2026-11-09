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
open Proofs.IntervalCall Proofs.ScalarRefs Proofs.GenericCall Proofs.MonoidLazyCall Proofs.DoublingNested Proofs.IntSim Proofs.ExtremaCall Proofs.ScalarRefsV
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

abbrev raExtG (ty : Ty) : NExpr := .binary ty .add (.variable ty 1) (.variable ty 0)
abbrev raSumG (ty : Ty) : NExpr :=
  .binary ty .add (.variable ty 1) (.binary ty .mul (.cast ty (.variable i32 2)) (.variable ty 0))

/-- `RangeAdd<T>::apply` to a max/min node: `x + v`. -/
def addApplyExt (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar ty false true], .scalar ty, .sequence (.primitive (.ret (raExtG ty))) (.primitive .skip)⟩

/-- `RangeAdd<T>::apply` to a sum node: `x + size * v`. -/
def addApplySum (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar ty false true, .scalar i32 false true], .scalar ty,
    .sequence (.primitive (.ret (raSumG ty))) (.primitive .skip)⟩

theorem addApplyExt_s64 : addApplyExt s64 = Proofs.MonoidLazyInstance.RangeAdd_long_long_applyExtremum := rfl
theorem addApplySum_s64 : addApplySum s64 = Proofs.MonoidLazyInstance.RangeAdd_long_long_applySumX := rfl

theorem rangeadd_applyExt_gen (ty : Ty) (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v⟩)) (e : NExpr) (m : Int) (hs : e.scalarOnly = true)
    (ht : e.resultType = ty) (value : e.denote (envOf caller) = some m) (gv : ty.valid v = true)
    (gm : ty.valid m = true) (gs : ty.valid (m + v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (addApplyExt ty).parameters [.scalarReference s1,.value e] = some Sinit ∧
      (addApplyExt ty).callFuel fuel caller [.scalarReference s1,.value e] = .finished (res,.scalar (m + v)) ∧
      ScalarPost2 caller Sinit res (1 + e.nodes) 110 caller.scalars.memory := by
  refine R1V1_correct _ ty ty ty rfl rfl (by simp [addApplyExt, Scalar, NExpr.scalarOnly])
    caller s1 b1 v e m c1 hs ht value gm valid lengths strict base 1 (m + v) gs 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 0 ty = some v :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v⟩ rfl (refVal caller s1 ty b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 1 ty = some m :=
    penv_ok _ 1 ty ⟨(callerP caller).length+0,true⟩ ⟨ty,m⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,m⟩] 0) rfl gm
  have den : (raExtG ty).denote (penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩) =
      some (m + v) := by
    rw [den_binary, den_variable, den_variable, e1, e0]
    simp only [Option.bind_some]
    exact convG ty _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen (raExtG ty) (m + v) _ den (by simp [NExpr.nodes])
  exact ⟨r, h1, h2, by omega, by simp at h4 ⊢; omega, by rw [h5]; exact Proofs.MonoidCallCore.take_P caller _⟩

theorem rangeadd_applySum_gen (ty : Ty) (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v⟩)) (e1 e2 : NExpr) (x sz : Int)
    (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = ty) (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : ty.valid v = true) (gx : ty.valid x = true) (gz : i32.valid sz = true) (gzt : ty.valid sz = true)
    (gm : ty.valid (sz * v) = true) (gs : ty.valid (x + sz * v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (addApplySum ty).parameters [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
      (addApplySum ty).callFuel fuel caller [.scalarReference s1,.value e1,.value e2] =
        .finished (res,.scalar (x + sz * v)) ∧
      ScalarPost2 caller Sinit res (1 + e1.nodes + e2.nodes) 110 caller.scalars.memory := by
  refine R1V2_correct _ ty ty ty i32 rfl rfl (by simp [addApplySum, Scalar, NExpr.scalarOnly])
    caller s1 b1 v e1 x e2 sz c1 hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1 (x + sz * v) gs 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 0 ty = some v :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v⟩ rfl (refVal caller s1 ty b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 1 ty = some x :=
    penv_ok _ 1 ty ⟨(callerP caller).length+0,true⟩ ⟨ty,x⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,x⟩,⟨i32,sz⟩] 0) rfl gx
  have e2 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 2 i32 = some sz :=
    penv_ok _ 2 i32 ⟨(callerP caller).length+1,true⟩ ⟨i32,sz⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,x⟩,⟨i32,sz⟩] 1) rfl gz
  have den : (raSumG ty).denote (penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩) =
      some (x + sz * v) := by
    rw [den_binary, den_variable, den_binary, den_cast, den_variable, den_variable, e1, e2, e0]
    simp only [Option.bind_some]
    rw [convG ty _ gzt]
    simp only [Option.bind_some]
    have m1 : binaryValue .mul sz v = sz * v := rfl
    rw [m1, convG ty _ gm]
    simp only [Option.bind_some]
    have m2 : binaryValue .add x (sz * v) = x + sz * v := rfl
    rw [m2]; exact convG ty _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen (raSumG ty) (x + sz * v) _ den (by simp [NExpr.nodes])
  exact ⟨r, h1, h2, by omega, by simp at h4 ⊢; omega, by rw [h5]; exact Proofs.MonoidCallCore.take_P caller _⟩

/-- `RangeSet<T>::apply` to a max/min node. -/
def setApplyExt (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar bl true false, .scalar ty false true], .scalar ty,
    selRet (.variable bl 1) (.variable ty 2) (.variable ty 0)⟩

/-- `RangeSet<T>::apply` to a sum node: `noop ? x : v * size`. -/
def setApplySum (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar bl true false, .scalar ty false true, .scalar i32 false true], .scalar ty,
    selRet (.variable bl 1) (.variable ty 2) (.binary ty .mul (.variable ty 0) (.cast ty (.variable i32 3)))⟩

theorem setApplyExt_s64 : setApplyExt s64 = Proofs.MonoidLazyInstance.RangeSet_long_long_applyExtremum := rfl
theorem setApplySum_s64 : setApplySum s64 = Proofs.MonoidLazyInstance.RangeSet_long_long_applySumX := rfl

theorem rangeset_applyExtremum_gen (ty : Ty) (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v noop : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,noop⟩))
    (e : NExpr) (m : Int) (hs : e.scalarOnly = true) (ht : e.resultType = ty)
    (value : e.denote (envOf caller) = some m) (gv : ty.valid v = true) (gn : bl.valid noop = true)
    (gm : ty.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (setApplyExt ty).parameters
        [.scalarReference s1,.scalarReference s2,.value e] = some Sinit ∧
      (setApplyExt ty).callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e] =
        .finished (res,.scalar (if noop ≠ 0 then m else v)) ∧
      ScalarPost2 caller Sinit res (2 + e.nodes) 110 caller.scalars.memory := by
  refine R2V1_correct _ ty ty bl ty rfl rfl (by exact selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 b1 b2 v noop e m c1 c2 hs ht value gm valid lengths strict base 1 (if noop ≠ 0 then m else v)
    (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 0 ty = some v :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v⟩ rfl (refVal caller s1 ty b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 1 bl = some noop :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,noop⟩ rfl (refVal caller s2 bl b2 noop c2 _) rfl gn
  have e2 : penv ⟨callerP caller ++ [(⟨ty,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 2 ty = some m :=
    penv_ok _ 2 ty ⟨(callerP caller).length+0,true⟩ ⟨ty,m⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,m⟩] 0) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable ty 2) (.variable ty 0) _ noop m v
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) (by rw [den_variable]; exact e0)
  refine ⟨r, h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact Proofs.MonoidCallCore.take_P caller _⟩

theorem rangeset_applySumX_gen (ty : Ty) (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v noop : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,noop⟩))
    (e1 e2 : NExpr) (x sz : Int) (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = ty)
    (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : ty.valid v = true) (gn : bl.valid noop = true) (gx : ty.valid x = true) (gz : i32.valid sz = true) (gzt : ty.valid sz = true)
    (gm : ty.valid (v * sz) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (setApplySum ty).parameters
        [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
      (setApplySum ty).callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.value e1,.value e2] =
        .finished (res,.scalar (if noop ≠ 0 then x else v * sz)) ∧
      ScalarPost2 caller Sinit res (2 + e1.nodes + e2.nodes) 110 caller.scalars.memory := by
  refine R2V2_correct _ ty ty bl ty i32 rfl rfl
    (by exact selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 b1 b2 v noop e1 x e2 sz c1 c2 hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1
    (if noop ≠ 0 then x else v * sz) (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 0 ty = some v :=
    penv_ok _ 0 ty ⟨b1.address,false⟩ ⟨ty,v⟩ rfl (refVal caller s1 ty b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 1 bl = some noop :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,noop⟩ rfl (refVal caller s2 bl b2 noop c2 _) rfl gn
  have e2 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 2 ty = some x :=
    penv_ok _ 2 ty ⟨(callerP caller).length+0,true⟩ ⟨ty,x⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,x⟩,⟨i32,sz⟩] 0) rfl gx
  have e3 : penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 3 i32 = some sz :=
    penv_ok _ 3 i32 ⟨(callerP caller).length+1,true⟩ ⟨i32,sz⟩ rfl (by simpa using get_tail (callerP caller) [⟨ty,x⟩,⟨i32,sz⟩] 1) rfl gz
  have hb : (NExpr.binary ty .mul (.variable ty 0) (.cast ty (.variable i32 3))).denote
      (penv ⟨callerP caller ++ [(⟨ty,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩) =
      some (v * sz) := by
    rw [den_binary, den_variable, den_cast, den_variable, e0, e3]
    simp only [Option.bind_some]
    rw [convG ty _ gzt]
    simp only [Option.bind_some]
    exact convG ty _ gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable ty 2)
    (.binary ty .mul (.variable ty 0) (.cast ty (.variable i32 3))) _ noop x (v * sz)
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) hb
  refine ⟨r, h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact Proofs.MonoidCallCore.take_P caller _⟩

end Proofs.GenericLazy
