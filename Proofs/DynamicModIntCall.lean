import Proofs.ScalarRefs
import Proofs.ShiftN
import Proofs.PowModCall
import Proofs.ScalarRefsV
import Proofs.Generated.DynamicModInt

namespace Proofs.DynamicModIntCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall Proofs.IntervalCall Proofs.ScalarRefs
open Proofs.CppState (Cell)

/-- `(u32)(inner % m) % m` where `m` is variable 0. -/
abbrev wrapE (inner : NExpr) : NExpr :=
  .divrem u32 true (.cast u32 (.divrem u64 true inner (.cast u64 (.variable u32 0)))) (.variable u32 0)

theorem u32_valid_of (v : Int) (h0 : 0 ≤ v) (h1 : v < 4294967296) : u32.valid v = true := by
  rw [show u32 = ⟨32,false,false⟩ from rfl]
  simp [Ty.valid]
  omega

theorem u32_range (v : Int) (h : u32.valid v = true) : 0 ≤ v ∧ v < 4294967296 := by
  rw [valid_u32] at h
  exact of_decide_eq_true h

theorem cast64_den (env : Nat → Ty → Option Int) (k : Nat) (v : Int) (h : env k u32 = some v) (h0 : 0 ≤ v)
    (h1 : v < 4294967296) : (NExpr.cast u64 (.variable u32 k)).denote env = some v := by
  rw [den_cast, den_variable, h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt h0 (by omega)

theorem wrap_den (env : Nat → Ty → Option Int) (inner : NExpr) (S m : Int) (hm : 0 < m) (hm32 : m < 4294967296)
    (hS0 : 0 ≤ S) (hS : S < 18446744073709551616) (hin : inner.denote env = some S) (h0 : env 0 u32 = some m) :
    (wrapE inner).denote env = some (S % m) := by
  have hc := cast64_den env 0 m h0 (by omega) hm32
  have hmod0 : 0 ≤ S % m := Int.emod_nonneg S (by omega)
  have hmod1 : S % m < m := Int.emod_lt_of_pos S hm
  rw [den_divrem, den_cast, den_divrem, hin, Option.bind_some, hc, Option.bind_some, den_variable, h0]
  have e1 : checkedDivRem u64 true S m = some (S % m) := by
    unfold checkedDivRem
    have hd : u64.valid (S.tdiv m) = true := by
      rw [valid_u64]
      have : 0 ≤ S.tdiv m := Int.tdiv_nonneg hS0 (by omega)
      have : S.tdiv m ≤ S := by
        rw [Int.tdiv_eq_ediv_of_nonneg hS0]; exact Int.ediv_le_self _ hS0
      simp; omega
    have hb : (m == 0) = false := by simp; omega
    rw [hb, if_neg (by simp), if_neg (by simp [hd])]
    rw [if_pos rfl, Int.tmod_eq_emod_of_nonneg hS0, convert_u64]
    congr 1
    exact Int.emod_eq_of_lt hmod0 (by omega)
  rw [e1, Option.bind_some, convert_u32, Option.bind_some, Option.bind_some]
  have e2 : (S % m) % 4294967296 = S % m := Int.emod_eq_of_lt hmod0 (by omega)
  rw [e2]
  have e3 : checkedDivRem u32 true (S % m) m = some (S % m) := by
    unfold checkedDivRem
    have hd : u32.valid ((S % m).tdiv m) = true := by
      rw [Int.tdiv_eq_ediv_of_nonneg hmod0, Int.ediv_eq_zero_of_lt hmod0 hmod1]
      exact u32_valid_of _ (by omega) (by omega)
    have hb : (m == 0) = false := by simp; omega
    rw [hb, if_neg (by simp), if_neg (by simp [hd])]
    rw [if_pos rfl, Int.tmod_eq_emod_of_nonneg hmod0, convert_u32]
    congr 1
    rw [Int.emod_emod_of_dvd _ (Int.dvd_refl m)]
    exact Int.emod_eq_of_lt (Int.emod_nonneg _ (by omega)) (by omega)
  rw [e3]

theorem wrap_den_g (env : Nat → Ty → Option Int) (inner dv : NExpr) (S m : Int) (hm : 0 < m) (hm32 : m < 4294967296)
    (hS0 : 0 ≤ S) (hS : S < 18446744073709551616) (hin : inner.denote env = some S) (hdv : dv.denote env = some m) (h0 : env 0 u32 = some m) :
    (NExpr.divrem u32 true (.cast u32 (.divrem u64 true inner dv)) (.variable u32 0)).denote env = some (S % m) := by
  have hmod0 : 0 ≤ S % m := Int.emod_nonneg S (by omega)
  have hmod1 : S % m < m := Int.emod_lt_of_pos S hm
  rw [den_divrem, den_cast, den_divrem, hin, Option.bind_some, hdv, Option.bind_some, den_variable, h0]
  have e1 : checkedDivRem u64 true S m = some (S % m) := by
    unfold checkedDivRem
    have hd : u64.valid (S.tdiv m) = true := by
      rw [valid_u64]
      have : 0 ≤ S.tdiv m := Int.tdiv_nonneg hS0 (by omega)
      have : S.tdiv m ≤ S := by
        rw [Int.tdiv_eq_ediv_of_nonneg hS0]; exact Int.ediv_le_self _ hS0
      simp; omega
    have hb : (m == 0) = false := by simp; omega
    rw [hb, if_neg (by simp), if_neg (by simp [hd])]
    rw [if_pos rfl, Int.tmod_eq_emod_of_nonneg hS0, convert_u64]
    congr 1
    exact Int.emod_eq_of_lt hmod0 (by omega)
  rw [e1, Option.bind_some, convert_u32, Option.bind_some, Option.bind_some]
  have e2 : (S % m) % 4294967296 = S % m := Int.emod_eq_of_lt hmod0 (by omega)
  rw [e2]
  have e3 : checkedDivRem u32 true (S % m) m = some (S % m) := by
    unfold checkedDivRem
    have hd : u32.valid ((S % m).tdiv m) = true := by
      rw [Int.tdiv_eq_ediv_of_nonneg hmod0, Int.ediv_eq_zero_of_lt hmod0 hmod1]
      exact u32_valid_of _ (by omega) (by omega)
    have hb : (m == 0) = false := by simp; omega
    rw [hb, if_neg (by simp), if_neg (by simp [hd])]
    rw [if_pos rfl, Int.tmod_eq_emod_of_nonneg hmod0, convert_u32]
    congr 1
    rw [Int.emod_emod_of_dvd _ (Int.dvd_refl m)]
    exact Int.emod_eq_of_lt (Int.emod_nonneg _ (by omega)) (by omega)
  rw [e3]

theorem ret_exec_big (e : NExpr) (v : Int) (ps : PS) (hden : e.denote (penv ps) = some v) (hn : e.nodes ≤ 40) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret e)) Sk) ps = some r ∧ r.ret = some v ∧ r.cost ≤ 42 ∧
      r.need ≤ ps.mem.length + ps.bs.length + 44 ∧ r.ps = ps := by
  refine ⟨_, exec_ret 1 ps e v hden, rfl, ?_, ?_, rfl⟩
  · simp; omega
  · simp; omega

theorem wrap_scalar (inner : NExpr) (h : inner.scalarOnly = true) : (wrapE inner).scalarOnly = true := by
  simp [NExpr.scalarOnly, h]

theorem wrap_nodes (inner : NExpr) : (wrapE inner).nodes = inner.nodes + 6 := by
  simp [NExpr.nodes]

/-- A method of `DModInt` with four read-only `unsigned int` references (m, x of both operands) whose body returns
`(inner % m) % m`. -/
theorem dm4_correct (prog : NProgram) (inner : NExpr) (hp : prog.parameters = [.scalar u32 true false,.scalar u32 true false,.scalar u32 true false,.scalar u32 true false])
    (hr : prog.result = ResultKind.scalar u32) (hbody : prog.body = .sequence (.primitive (.ret (wrapE inner))) Sk)
    (hin_s : inner.scalarOnly = true) (hin_n : inner.nodes ≤ 30)
    (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,v1⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,v2⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,v3⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,v4⟩))
    (hm : 0 < v1) (hm32 : v1 < 4294967296) (g2 : u32.valid v2 = true) (g3 : u32.valid v3 = true) (g4 : u32.valid v4 = true)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < 18446744073709551616)
    (hin : ∀ env : Nat → Ty → Option Int, env 0 u32 = some v1 → env 1 u32 = some v2 → env 2 u32 = some v3 →
      env 3 u32 = some v4 → inner.denote env = some S)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (S % v1)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  have g1 : u32.valid v1 = true := u32_valid_of v1 (by omega) hm32
  have hmod0 : 0 ≤ S % v1 := Int.emod_nonneg S (by omega)
  have hmod1 : S % v1 < v1 := Int.emod_lt_of_pos S hm
  refine refs4t_correct prog u32 u32 u32 u32 u32 hp hr (by rw [hbody]; simp [Scalar]; exact wrap_scalar inner hin_s)
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (S % v1)
    (u32_valid_of _ hmod0 (by omega)) 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 u32 = some v1 :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,v1⟩ rfl (P_cell_ty caller s1 u32 b1 v1 c1) rfl g1
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 u32 = some v2 :=
    penv_ok _ 1 u32 ⟨b2.address,false⟩ ⟨u32,v2⟩ rfl (P_cell_ty caller s2 u32 b2 v2 c2) rfl g2
  have e2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 2 u32 = some v3 :=
    penv_ok _ 2 u32 ⟨b3.address,false⟩ ⟨u32,v3⟩ rfl (P_cell_ty caller s3 u32 b3 v3 c3) rfl g3
  have e3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 3 u32 = some v4 :=
    penv_ok _ 3 u32 ⟨b4.address,false⟩ ⟨u32,v4⟩ rfl (P_cell_ty caller s4 u32 b4 v4 c4) rfl g4
  have den := wrap_den _ inner S v1 hm hm32 hS0 hS (hin _ e0 e1 e2 e3) e0
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (wrapE inner) (S % v1) _ den (by rw [wrap_nodes]; omega)
  refine ⟨r, by rw [hbody]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

theorem dm2_correct (prog : NProgram) (inner : NExpr) (hp : prog.parameters = [.scalar u32 true false,.scalar u32 true false])
    (hr : prog.result = ResultKind.scalar u32) (hbody : prog.body = .sequence (.primitive (.ret (wrapE inner))) Sk)
    (hin_s : inner.scalarOnly = true) (hin_n : inner.nodes ≤ 30)
    (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v1 v2 : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,v1⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,v2⟩))
    (hm : 0 < v1) (hm32 : v1 < 4294967296) (g2 : u32.valid v2 = true)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < 18446744073709551616)
    (hin : ∀ env : Nat → Ty → Option Int, env 0 u32 = some v1 → env 1 u32 = some v2 → inner.denote env = some S)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2] = .finished (res,.scalar (S % v1)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  have g1 : u32.valid v1 = true := u32_valid_of v1 (by omega) hm32
  have hmod0 : 0 ≤ S % v1 := Int.emod_nonneg S (by omega)
  have hmod1 : S % v1 < v1 := Int.emod_lt_of_pos S hm
  refine refs2t_correct prog u32 u32 u32 hp hr (by rw [hbody]; simp [Scalar]; exact wrap_scalar inner hin_s)
    caller s1 s2 b1 b2 v1 v2 c1 c2 valid lengths strict base 1 (S % v1)
    (u32_valid_of _ hmod0 (by omega)) 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩]⟩ 0 u32 = some v1 :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,v1⟩ rfl (P_cell_ty caller s1 u32 b1 v1 c1) rfl g1
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩]⟩ 1 u32 = some v2 :=
    penv_ok _ 1 u32 ⟨b2.address,false⟩ ⟨u32,v2⟩ rfl (P_cell_ty caller s2 u32 b2 v2 c2) rfl g2
  have den := wrap_den _ inner S v1 hm hm32 hS0 hS (hin _ e0 e1) e0
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (wrapE inner) (S % v1) _ den (by rw [wrap_nodes]; omega)
  refine ⟨r, by rw [hbody]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

abbrev addIn : NExpr := .binary u64 .add (.cast u64 (.variable u32 1)) (.cast u64 (.variable u32 3))
abbrev subIn : NExpr := .binary u64 .sub (.binary u64 .add (.cast u64 (.variable u32 1)) (.cast u64 (.variable u32 0)))
  (.cast u64 (.variable u32 3))
abbrev mulIn : NExpr := .binary u64 .mul (.cast u64 (.variable u32 1)) (.cast u64 (.variable u32 3))
abbrev negIn : NExpr := .binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.variable u32 1))

theorem add_m_body : Proofs.DynamicModIntInstance.DModInt_add_m.body = .sequence (.primitive (.ret (.variable u32 0))) Sk := rfl
theorem add_body : Proofs.DynamicModIntInstance.DModInt_add_x.body = .sequence (.primitive (.ret (wrapE addIn))) Sk := rfl
theorem sub_m_body : Proofs.DynamicModIntInstance.DModInt_sub_m.body = .sequence (.primitive (.ret (.variable u32 0))) Sk := rfl
theorem sub_body : Proofs.DynamicModIntInstance.DModInt_sub_x.body = .sequence (.primitive (.ret (wrapE subIn))) Sk := rfl
theorem mul_m_body : Proofs.DynamicModIntInstance.DModInt_mul_m.body = .sequence (.primitive (.ret (.variable u32 0))) Sk := rfl
theorem mul_body : Proofs.DynamicModIntInstance.DModInt_mul_x.body = .sequence (.primitive (.ret (wrapE mulIn))) Sk := rfl
theorem neg_body : Proofs.DynamicModIntInstance.DModInt_neg_x.body = .sequence (.primitive (.ret (wrapE negIn))) Sk := rfl

theorem u64_bin (env : Nat → Ty → Option Int) (op : Binary) (a b : NExpr) (x y : Int) (ha : a.denote env = some x)
    (hb : b.denote env = some y) (r : Int) (hr : binaryValue op x y = r) (h0 : 0 ≤ r) (h1 : r < 18446744073709551616) :
    (NExpr.binary u64 op a b).denote env = some r := by
  rw [den_binary, ha, hb]
  simp only [Option.bind_some]
  rw [hr, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt h0 h1

theorem add_inner (env : Nat → Ty → Option Int) (x y : Int) (h1 : env 1 u32 = some x) (h3 : env 3 u32 = some y)
    (gx : 0 ≤ x ∧ x < 4294967296) (gy : 0 ≤ y ∧ y < 4294967296) : addIn.denote env = some (x + y) :=
  u64_bin env .add _ _ x y (cast64_den env 1 x h1 gx.1 gx.2) (cast64_den env 3 y h3 gy.1 gy.2) (x + y) rfl
    (by omega) (by omega)

theorem sub_inner (env : Nat → Ty → Option Int) (x y m : Int) (h1 : env 1 u32 = some x) (h3 : env 3 u32 = some y)
    (h0 : env 0 u32 = some m) (gx : 0 ≤ x ∧ x < 4294967296) (gy : 0 ≤ y ∧ y < 4294967296)
    (gm : 0 ≤ m ∧ m < 4294967296) (hle : y ≤ x + m) : subIn.denote env = some (x + m - y) :=
  u64_bin env .sub _ _ (x + m) y
    (u64_bin env .add _ _ x m (cast64_den env 1 x h1 gx.1 gx.2) (cast64_den env 0 m h0 gm.1 gm.2) (x + m) rfl
      (by omega) (by omega))
    (cast64_den env 3 y h3 gy.1 gy.2) (x + m - y) rfl (by omega) (by omega)

theorem mul_inner (env : Nat → Ty → Option Int) (x y : Int) (h1 : env 1 u32 = some x) (h3 : env 3 u32 = some y)
    (gx : 0 ≤ x ∧ x < 4294967296) (gy : 0 ≤ y ∧ y < 4294967296) : mulIn.denote env = some (x * y) :=
  u64_bin env .mul _ _ x y (cast64_den env 1 x h1 gx.1 gx.2) (cast64_den env 3 y h3 gy.1 gy.2) (x * y) rfl
    (Int.mul_nonneg gx.1 gy.1)
    (by
      have : x * y ≤ 4294967295 * 4294967295 := Int.mul_le_mul (by omega) (by omega) gy.1 (by omega)
      omega)

theorem neg_inner (env : Nat → Ty → Option Int) (x m : Int) (h1 : env 1 u32 = some x) (h0 : env 0 u32 = some m)
    (gx : 0 ≤ x ∧ x < 4294967296) (gm : 0 ≤ m ∧ m < 4294967296) (hle : x ≤ m) : negIn.denote env = some (m - x) :=
  u64_bin env .sub _ _ m x (cast64_den env 0 m h0 gm.1 gm.2) (cast64_den env 1 x h1 gx.1 gx.2) (m - x) rfl
    (by omega) (by omega)

theorem dmodint_add_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (hm : 0 < m) (hm32 : m < 4294967296) (gx : u32.valid x = true) (gm' : u32.valid m' = true) (gy : u32.valid y = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_add_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_add_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar ((x + y) % m)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory :=
  dm4_correct _ addIn rfl rfl add_body rfl (by decide) caller s1 s2 s3 s4 b1 b2 b3 b4 m x m' y c1 c2 c3 c4 hm hm32 gx gm' gy
    (x + y) (by have := u32_range x gx; have := u32_range y gy; omega) (by have := u32_range x gx; have := u32_range y gy; omega)
    (fun env e0 e1 e2 e3 => add_inner env x y e1 e3 (u32_range x gx) (u32_range y gy)) valid lengths strict base

theorem dmodint_sub_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (hm : 0 < m) (hm32 : m < 4294967296) (gx : u32.valid x = true) (gm' : u32.valid m' = true) (gy : u32.valid y = true)
    (hle : y ≤ x + m) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_sub_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_sub_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar ((x + m - y) % m)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory :=
  dm4_correct _ subIn rfl rfl sub_body rfl (by decide) caller s1 s2 s3 s4 b1 b2 b3 b4 m x m' y c1 c2 c3 c4 hm hm32 gx gm' gy
    (x + m - y) (by have := u32_range x gx; have := u32_range y gy; omega) (by have := u32_range x gx; have := u32_range y gy; omega)
    (fun env e0 e1 e2 e3 => sub_inner env x y m e1 e3 e0 (u32_range x gx) (u32_range y gy) ⟨by omega, hm32⟩ hle) valid lengths strict base

theorem dmodint_mul_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (hm : 0 < m) (hm32 : m < 4294967296) (gx : u32.valid x = true) (gm' : u32.valid m' = true) (gy : u32.valid y = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_mul_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_mul_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar ((x * y) % m)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory :=
  dm4_correct _ mulIn rfl rfl mul_body rfl (by decide) caller s1 s2 s3 s4 b1 b2 b3 b4 m x m' y c1 c2 c3 c4 hm hm32 gx gm' gy
    (x * y) (Int.mul_nonneg (u32_range x gx).1 (u32_range y gy).1) (by have := u32_range x gx; have := u32_range y gy; have : x * y ≤ 4294967295 * 4294967295 := Int.mul_le_mul (by omega) (by omega) this.1 (by omega); omega)
    (fun env e0 e1 e2 e3 => mul_inner env x y e1 e3 (u32_range x gx) (u32_range y gy)) valid lengths strict base

theorem dmodint_add_m_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (gm : u32.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_add_m.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_add_m.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar m) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  refine refs4t_correct _ u32 u32 u32 u32 u32 rfl rfl (by rw [add_m_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    m x m' y c1 c2 c3 c4 valid lengths strict base 1 m gm 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 u32 = some m :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,m⟩ rfl (P_cell_ty caller s1 u32 b1 m c1) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (.variable u32 0) m _ (by rw [den_variable]; exact e0) (by decide)
  refine ⟨r, by rw [add_m_body]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

theorem dmodint_sub_m_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (gm : u32.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_sub_m.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_sub_m.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar m) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  refine refs4t_correct _ u32 u32 u32 u32 u32 rfl rfl (by rw [sub_m_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    m x m' y c1 c2 c3 c4 valid lengths strict base 1 m gm 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 u32 = some m :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,m⟩ rfl (P_cell_ty caller s1 u32 b1 m c1) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (.variable u32 0) m _ (by rw [den_variable]; exact e0) (by decide)
  refine ⟨r, by rw [sub_m_body]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

theorem dmodint_mul_m_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (gm : u32.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_mul_m.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_mul_m.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar m) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  refine refs4t_correct _ u32 u32 u32 u32 u32 rfl rfl (by rw [mul_m_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    m x m' y c1 c2 c3 c4 valid lengths strict base 1 m gm 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 u32 = some m :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,m⟩ rfl (P_cell_ty caller s1 u32 b1 m c1) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (.variable u32 0) m _ (by rw [den_variable]; exact e0) (by decide)
  refine ⟨r, by rw [mul_m_body]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

theorem neg_m_body : Proofs.DynamicModIntInstance.DModInt_neg_m.body = .sequence (.primitive (.ret (.variable u32 0))) Sk := rfl
theorem eq_body : Proofs.DynamicModIntInstance.DModInt_equal.body =
    .sequence (.primitive (.ret (.binary bl .eq (.variable u32 1) (.variable u32 3)))) Sk := rfl

theorem dmodint_neg_x_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (hm : 0 < m) (hm32 : m < 4294967296) (gx : u32.valid x = true) (hle : x ≤ m)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_neg_x.parameters
        [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_neg_x.callFuel fuel caller [.scalarReference s1,.scalarReference s2] =
        .finished (res,.scalar ((m - x) % m)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory :=
  dm2_correct _ negIn rfl rfl neg_body rfl (by decide) caller s1 s2 b1 b2 m x c1 c2 hm hm32 gx (m - x)
    (by have := u32_range x gx; omega) (by have := u32_range x gx; omega)
    (fun env e0 e1 => neg_inner env x m e1 e0 (u32_range x gx) ⟨by omega, hm32⟩ hle) valid lengths strict base

theorem dmodint_neg_m_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (gm : u32.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_neg_m.parameters
        [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_neg_m.callFuel fuel caller [.scalarReference s1,.scalarReference s2] =
        .finished (res,.scalar m) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  refine refs2t_correct _ u32 u32 u32 rfl rfl (by rw [neg_m_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 b1 b2
    m x c1 c2 valid lengths strict base 1 m gm 42 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩]⟩ 0 u32 = some m :=
    penv_ok _ 0 u32 ⟨b1.address,false⟩ ⟨u32,m⟩ rfl (P_cell_ty caller s1 u32 b1 m c1) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big (.variable u32 0) m _ (by rw [den_variable]; exact e0) (by decide)
  refine ⟨r, by rw [neg_m_body]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩

theorem dmodint_equal_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x m' y : Int)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,m⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,x⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,m'⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,y⟩))
    (gx : u32.valid x = true) (gy : u32.valid y = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_equal.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_equal.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if x = y then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 102 caller.scalars.memory := by
  refine refs4t_correct _ bl u32 u32 u32 u32 rfl rfl (by rw [eq_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4
    b1 b2 b3 b4 m x m' y c1 c2 c3 c4 valid lengths strict base 1 (if x = y then 1 else 0)
    (by split <;> rfl) 42 ?_
  intro P hP
  subst hP
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 u32 = some x :=
    penv_ok _ 1 u32 ⟨b2.address,false⟩ ⟨u32,x⟩ rfl (P_cell_ty caller s2 u32 b2 x c2) rfl gx
  have e3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 3 u32 = some y :=
    penv_ok _ 3 u32 ⟨b4.address,false⟩ ⟨u32,y⟩ rfl (P_cell_ty caller s4 u32 b4 y c4) rfl gy
  have den : (NExpr.binary bl .eq (.variable u32 1) (.variable u32 3)).denote
      (penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩) =
      some (if x = y then 1 else 0) := by
    rw [den_binary, den_variable, den_variable, e1, e3]
    simp only [Option.bind_some]
    have : binaryValue .eq x y = if x = y then 1 else 0 := by
      show (if (x == y) = true then 1 else 0) = _
      by_cases h : x = y <;> simp [h]
    rw [this, convert_bl]
    by_cases h : x = y <;> simp [h]
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_big _ _ _ den (by decide)
  refine ⟨r, by rw [eq_body]; exact h1, h2, h3, by simp at h4 ⊢; omega, by rw [h5]; exact take_callerP caller⟩


section Pow
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ShiftN Proofs.IntSim Proofs.DoublingNested Proofs.Mod61Body
open Proofs.CppState (Cell)

/-- The state `mk P vs` with the bindings `B` in front. -/
def shPS (B : List CppState.Binding) (ps : PS) : PS := ⟨ps.mem, B ++ ps.bs⟩

theorem shifted_decl (k : Nat) (B : List CppState.Binding) (hB : B.length = k) (fu : Nat) (P : List Cell) (vs : List Nat) (e : NExpr) (x : Nat)
    (hx : x < 18446744073709551616) (h : e.denote (penv (mk P vs)) = some (x : Int)) :
    pexec fu (.primitive (.declare u64 true (e.shN k))) (shPS B (mk P vs)) =
      some ⟨shPS B (mk P (vs ++ [x])), none, e.nodes + 1, P.length + 2 * vs.length + e.nodes + 4 + k⟩ := by
  have h1 := pstmt_sh (.declare u64 true e) (mk P vs).mem (mk P vs).bs B
  rw [hB] at h1
  have h2 := mk_decl P vs e x hx h
  have h3 : pstmt (.declare u64 true (e.shN k)) ⟨(mk P vs).mem, B ++ (mk P vs).bs⟩ =
      (pstmt (.declare u64 true e) ⟨(mk P vs).mem, (mk P vs).bs⟩).map (shR B) := h1
  rw [pexec_prim]
  show pstmt (.declare u64 true (e.shN k)) ⟨(mk P vs).mem, B ++ (mk P vs).bs⟩ = _
  rw [h3]
  have : (⟨(mk P vs).mem, (mk P vs).bs⟩ : PS) = mk P vs := rfl
  rw [this, h2]
  simp [shR, shPS, hB]

theorem shifted_loop (k : Nat) (B : List CppState.Binding) (hB : B.length = k) (fu : Nat) (P : List Cell) (vs : List Nat) :
    pexec fu (LoopCmd.shN k) (shPS B (mk P vs)) = (pexec fu LoopCmd (mk P vs)).map (shR B) := by
  have h1 := pexec_sh fu LoopCmd (mk P vs) B
  rw [hB] at h1
  exact h1

abbrev retPowE : NExpr := .divrem u32 true (.cast u32 (.variable u64 6)) (.variable u32 0)

theorem power_body : Proofs.DynamicModIntInstance.DModInt_power_x.body =
    .sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
    (.sequence (.primitive (.declare u64 true (.variable u64 2)))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0))))
    (.sequence (.primitive (.declare u64 true (initR.shN 3)))
    (.sequence (.primitive (.declare u64 true (initB.shN 3)))
    (.sequence (.primitive (.declare u64 true (initE.shN 3)))
    (.sequence (LoopCmd.shN 3) (.sequence (.primitive (.ret retPowE)) Sk))))))) := rfl

open Proofs.DynamicModIntCall (cast64_den u32_range)

theorem ret_den (env : Nat → Ty → Option Int) (r m : Int) (h6 : env 6 u64 = some r) (h0 : env 0 u32 = some m)
    (hr0 : 0 ≤ r) (hrm : r < m) (hm32 : m < 4294967296) : retPowE.denote env = some r := by
  have hm : 0 < m := by omega
  rw [den_divrem, den_cast, den_variable, h6, Option.bind_some, den_variable, h0]
  have c : u32.convert r = some r := by
    rw [convert_u32]; congr 1; exact Int.emod_eq_of_lt hr0 (by omega)
  rw [c, Option.bind_some, Option.bind_some]
  unfold checkedDivRem
  have hb : (m == 0) = false := by simp; omega
  have hd : u32.valid (r.tdiv m) = true := by
    rw [Int.tdiv_eq_ediv_of_nonneg hr0, Int.ediv_eq_zero_of_lt hr0 hrm]
    exact DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  rw [hb, if_neg (by simp), if_neg (by simp [hd]), if_pos rfl, Int.tmod_eq_emod_of_nonneg hr0, convert_u32]
  congr 1
  rw [Int.emod_eq_of_lt hr0 hrm]
  exact Int.emod_eq_of_lt hr0 (by omega)

theorem power_tail (k : Nat) (hk : k ≤ 4) (P' : List Cell) (B : List CppState.Binding) (hB : B.length = k) (x e m : Nat) (hm : 0 < m)
    (hmle : m ≤ 4294967296) (hx64 : x < 18446744073709551616) (he : e < 18446744073709551616) (retE : NExpr) (v : Int)
    (hn : retE.nodes ≤ 10)
    (hden : ∀ bF : Nat, bF < m →
      retE.denote (penv (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)))) = some v) :
    ∃ rF : PR, pexec 70 (.sequence (.primitive (.declare u64 true (initR.shN k)))
        (.sequence (.primitive (.declare u64 true (initB.shN k)))
        (.sequence (.primitive (.declare u64 true (initE.shN k)))
        (.sequence (LoopCmd.shN k) (.sequence (.primitive (.ret retE)) Sk)))))
        (shPS B (mk P' [x,e,m])) = some rF ∧
      rF.ret = some v ∧ rF.cost ≤ 3050 ∧ rF.need ≤ P'.length + 60 ∧ ∃ L, rF.ps.mem = P' ++ L := by
  have hexp : e < 2 ^ 64 := by simpa using he
  have hm64 : m < 18446744073709551616 := by omega
  have env3 := PowModCall.env3 P' x e m hx64 he hm64
  have d1R := initR_value (penv (mk P' [x,e,m])) m hm hm64 env3.2.2
  have x1 : 1 % m < 18446744073709551616 := by have := Nat.mod_le 1 m; omega
  have t1 := shifted_decl k B hB 70 P' [x,e,m] initR (1 % m) x1 d1R
  have hv4 : ∀ y ∈ [x,e,m,1 % m], y < 18446744073709551616 := by
    intro y hy; simp at hy; omega
  have k4 := penv_mk P' [x,e,m,1 % m] hv4
  have d2B := initB_value (penv (mk P' [x,e,m,1 % m])) x m hm hx64 (k4 0 (by simp)) (k4 2 (by simp))
  have x2 : x % m < 18446744073709551616 := by have := Nat.mod_le x m; omega
  have t2 := shifted_decl k B hB 70 P' [x,e,m,1 % m] initB (x % m) x2 d2B
  have hv5 : ∀ y ∈ [x,e,m,1 % m,x % m], y < 18446744073709551616 := by
    intro y hy; simp at hy; omega
  have k5 := penv_mk P' [x,e,m,1 % m,x % m] hv5
  have d3E := initE_value (penv (mk P' [x,e,m,1 % m,x % m])) e (k5 1 (by simp))
  have t3 := shifted_decl k B hB 70 P' [x,e,m,1 % m,x % m] initE e he d3E
  have hok : Ok x e m (1 % m) (x % m) e := ⟨hx64,he,hm,hmle,Nat.mod_lt _ hm,Nat.mod_lt _ hm,he⟩
  obtain ⟨rl,bF,hl,hlps,hbF,hlret,hlcost,hlneed⟩ := loop_exec P' 64 70 (by omega) hok hexp
  have t4 := shifted_loop k B hB 70 P' (sv x e m (1 % m) (x % m) e)
  have hlsh : pexec 70 (LoopCmd.shN k) (shPS B (mk P' [x,e,m,1 % m,x % m,e])) = some (shR B rl) := by
    have : mk P' [x,e,m,1 % m,x % m,e] = mk P' (sv x e m (1 % m) (x % m) e) := rfl
    rw [this, t4, hl]; rfl
  have hrFlt : pw m 64 (1 % m) (x % m) e < m := by
    rw [pw_spec m hm 64 _ _ _ hexp (Nat.mod_lt _ hm)]; exact Nat.mod_lt _ hm
  have hsF : shR B rl = ⟨shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)), rl.ret, rl.cost, rl.need + k⟩ := by
    simp only [shR, shPS]
    rw [hlps, hB]
  have rr := pstmt_ret_ok (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))) retE v (hden bF hbF)
  have p5 := seq_ret (fu := 70) (b := Sk) (a := .primitive (.ret retE))
    (ps := shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))) (by rw [pexec_prim]; exact rr) rfl
  obtain ⟨rF, p5'⟩ : ∃ rF, pexec 70 (.sequence (.primitive (.ret retE)) Sk) (shR B rl).ps = some rF :=
    ⟨_, by rw [hsF]; exact p5⟩
  have c5 := seq_some hlsh (by simp [shR, hlret]) p5'
  have c4 := seq_some t3 rfl c5
  have c3 := seq_some t2 rfl c4
  have c2 := seq_some t1 rfl c3
  have hrF : rF = ⟨shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)), some v, retE.nodes + 1,
      (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))).mem.length +
        (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))).bs.length + retE.nodes + 2⟩ := by
    have h := p5'
    rw [hsF] at h
    exact (Option.some.inj (p5.symm.trans h)).symm
  subst hrF
  refine ⟨_, c2, rfl, ?_, ?_, ⟨_, rfl⟩⟩
  · dsimp only
    simp only [NExpr.nodes, shR]
    omega
  · dsimp only
    simp only [NExpr.nodes, mk_size, shPS, sv, shR, List.length_append, List.length_cons, List.length_nil]
    have hms := mk_size P' [x, e, m, pw m 64 (1 % m) (x % m) e, bF, 0]
    simp only [List.length_cons, List.length_nil] at hms
    omega

abbrev tailCmd (k : Nat) (retE : NExpr) : Command :=
  .sequence (.primitive (.declare u64 true (initR.shN k)))
    (.sequence (.primitive (.declare u64 true (initB.shN k)))
    (.sequence (.primitive (.declare u64 true (initE.shN k)))
    (.sequence (LoopCmd.shN k) (.sequence (.primitive (.ret retE)) Sk))))

/-- Three declarations `base`, `exp`, `mm` followed by the `pow_mod` loop and a return. -/
theorem three_decl_tail (k : Nat) (hk : k ≤ 4) (P' : List Cell) (B : List CppState.Binding) (hB : B.length = k)
    (c1 c2 c3 : NExpr) (x e m : Nat) (hm : 0 < m) (hmle : m ≤ 4294967296) (hx64 : x < 18446744073709551616)
    (he : e < 18446744073709551616)
    (v1 : c1.denote (penv ⟨P',B⟩) = some (x : Int))
    (v2 : c2.denote (penv ⟨P' ++ [(⟨u64,(x : Int)⟩ : Cell)], B ++ [⟨P'.length,true⟩]⟩) = some (e : Int))
    (v3 : c3.denote (penv ⟨P' ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,(e : Int)⟩ : Cell)],
      B ++ [⟨P'.length,true⟩] ++ [⟨(P' ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩]⟩) = some (m : Int))
    (retE : NExpr) (v : Int) (hn : retE.nodes ≤ 10) (hc1 : c1.nodes ≤ 10) (hc2 : c2.nodes ≤ 10) (hc3 : c3.nodes ≤ 10)
    (hden : ∀ bF : Nat, bF < m →
      retE.denote (penv (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)))) = some v) :
    ∃ r : PR, pexec 70 (.sequence (.primitive (.declare u64 true c1)) (.sequence (.primitive (.declare u64 true c2))
        (.sequence (.primitive (.declare u64 true c3)) (tailCmd k retE)))) ⟨P',B⟩ = some r ∧
      r.ret = some v ∧ r.cost ≤ 3100 ∧ r.need ≤ P'.length + 64 ∧ ∃ L, r.ps.mem = P' ++ L := by
  have hx : x < 18446744073709551616 := hx64
  have s1 := pstmt_declare_ok ⟨P',B⟩ u64 true c1 (x : Int) v1 (x : Int) (Ty.convert_of_valid _ _ (u64_lt _ hx64))
  have q1 := (pexec_prim 70 _ _).trans s1
  have s2 := pstmt_declare_ok ⟨P' ++ [(⟨u64,(x : Int)⟩ : Cell)], B ++ [⟨P'.length,true⟩]⟩ u64 true c2 (e : Int) v2 (e : Int)
    (Ty.convert_of_valid _ _ (u64_lt _ he))
  have q2 := (pexec_prim 70 _ _).trans s2
  have s3 := pstmt_declare_ok ⟨P' ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,(e : Int)⟩ : Cell)],
      B ++ [⟨P'.length,true⟩] ++ [⟨(P' ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩]⟩ u64 true c3 (m : Int) v3 (m : Int)
    (Ty.convert_of_valid _ _ (u64_lt _ (by omega)))
  have q3 := (pexec_prim 70 _ _).trans s3
  have heq : (⟨P' ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(m : Int)⟩ : Cell)],
      B ++ [⟨P'.length,true⟩] ++ [⟨(P' ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩] ++
        [⟨(P' ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,(e : Int)⟩ : Cell)]).length,true⟩]⟩ : PS) =
      shPS B (mk P' [x,e,m]) := by
    simp [shPS, mk, cm, bmd, List.range_succ]
  obtain ⟨rF, ht, hret, hcost, hneed, L, hmem⟩ := power_tail k hk P' B hB x e m hm hmle hx64 he retE v hn hden
  have c1' := seq_some q3 rfl (by rw [heq]; exact ht)
  have b2 := seq_some q2 rfl c1'
  have b1 := seq_some q1 rfl b2
  refine ⟨_, b1, ?_, ?_, ?_, ⟨L, ?_⟩⟩
  · simpa using hret
  · dsimp only
    omega
  · dsimp only
    simp only [List.length_append, List.length_cons, List.length_nil, hB] at *
    omega
  · simpa using hmem

abbrev retPowAt (i : Nat) : NExpr := .divrem u32 true (.cast u32 (.variable u64 i)) (.variable u32 0)

theorem ret_den_at (i : Nat) (env : Nat → Ty → Option Int) (r m : Int) (h6 : env i u64 = some r)
    (h0 : env 0 u32 = some m) (hr0 : 0 ≤ r) (hrm : r < m) (hm32 : m < 4294967296) :
    (retPowAt i).denote env = some r := by
  have hm : 0 < m := by omega
  rw [den_divrem, den_cast, den_variable, h6, Option.bind_some, den_variable, h0]
  have c : u32.convert r = some r := by
    rw [convert_u32]; congr 1; exact Int.emod_eq_of_lt hr0 (by omega)
  rw [c, Option.bind_some, Option.bind_some]
  unfold checkedDivRem
  have hb : (m == 0) = false := by simp; omega
  have hd : u32.valid (r.tdiv m) = true := by
    rw [Int.tdiv_eq_ediv_of_nonneg hr0, Int.ediv_eq_zero_of_lt hr0 hrm]
    exact DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  rw [hb, if_neg (by simp), if_neg (by simp [hd]), if_pos rfl, Int.tmod_eq_emod_of_nonneg hr0, convert_u32]
  congr 1
  rw [Int.emod_eq_of_lt hr0 hrm]
  exact Int.emod_eq_of_lt hr0 (by omega)

/-- The value returned by the loop part: the `result` cell is read at index `k + 3`. -/
theorem res_env (k : Nat) (P' : List Cell) (B : List CppState.Binding) (hB : B.length = k) (x e m bF : Nat)
    (hok : Ok x e m (pw m 64 (1 % m) (x % m) e) bF 0) :
    penv (shPS B (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))) (3 + k) u64 =
      some ((pw m 64 (1 % m) (x % m) e : Nat) : Int) := by
  obtain ⟨_,_,_,e3,_,_⟩ := env_sv P' hok
  have := penv_sh (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)).mem
    (mk P' (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)).bs B 3 u64
  rw [hB] at this
  exact this.trans e3

theorem hok_of (m x e bF : Nat) (hm : 0 < m) (hmle : m ≤ 4294967296) (hx64 : x < 18446744073709551616)
    (he : e < 18446744073709551616) (hbF : bF < m) : Ok x e m (pw m 64 (1 % m) (x % m) e) bF 0 := by
  have hexp : e < 2 ^ 64 := by simpa using he
  have hrFlt : pw m 64 (1 % m) (x % m) e < m := by
    rw [pw_spec m hm 64 _ _ _ hexp (Nat.mod_lt _ hm)]; exact Nat.mod_lt _ hm
  exact ⟨hx64,he,hm,hmle,hrFlt,hbF,by omega⟩

theorem power_m_body : Proofs.DynamicModIntInstance.DModInt_power_m.body =
    .sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
    (.sequence (.primitive (.declare u64 true (.variable u64 2)))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0)))) (tailCmd 3 (.variable u32 0)))) := rfl

theorem power_core (P0 : List Cell) (a1 a2 m x e : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm : 0 < m) (hm32 : m < 4294967296) (hx : x < 4294967296)
    (he : e < 18446744073709551616) (retE : NExpr) (v : Int) (hn : retE.nodes ≤ 10)
    (hden : ∀ bF : Nat, bF < m → retE.denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]
      (mk (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)))) = some v) :
    ∃ r : PR, pexec 70 (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
        (.sequence (.primitive (.declare u64 true (.variable u64 2)))
        (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0)))) (tailCmd 3 retE))))
        ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)],[⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]⟩ = some r ∧
      r.ret = some v ∧ r.cost ≤ 3100 ∧ r.need ≤ P0.length + 70 ∧
      ∃ L, r.ps.mem = P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L := by
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have l2 : a2 < P0.length := (List.getElem?_eq_some_iff.mp h2).1
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x < 18446744073709551616 := by omega
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have xv32 : u32.valid (x : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have ev64 : u64.valid (e : Int) = true := u64_lt _ he
  have hP'len : (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]).length = P0.length + 1 := by simp
  let B : List CppState.Binding := [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]
  have hB : B.length = 3 := rfl
  have Env : ∀ (mem : List Cell) (Bs : List CppState.Binding), (∃ L, mem = P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L) →
      (∃ Y, Bs = B ++ Y) → penv ⟨mem, Bs⟩ 0 u32 = some (m : Int) ∧ penv ⟨mem, Bs⟩ 1 u32 = some (x : Int) ∧
        penv ⟨mem, Bs⟩ 2 u64 = some (e : Int) := by
    rintro mem Bs ⟨L, rfl⟩ ⟨Y, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
      show (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L)[a1]? = _
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left l1]; exact h1
    · refine penv_ok _ 1 u32 ⟨a2,false⟩ ⟨u32,(x : Int)⟩ rfl ?_ rfl xv32
      show (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L)[a2]? = _
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left l2]; exact h2
    · refine penv_ok _ 2 u64 ⟨P0.length+0,true⟩ ⟨u64,(e : Int)⟩ rfl ?_ rfl ev64
      show (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L)[P0.length+0]? = _
      rw [List.getElem?_append_left (by simp)]
      simp
  have E0 := Env (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ []) B ⟨[], rfl⟩ ⟨[], by simp⟩
  have v1 : (NExpr.cast u64 (.variable u32 1)).denote (penv ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)], B⟩) = some (x : Int) := by
    have E := Env (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) B ⟨[], by simp⟩ ⟨[], by simp⟩
    exact cast64_den _ 1 (x : Int) E.2.1 (by omega) (by omega)
  have v2 : (NExpr.variable u64 2).denote (penv ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)],
      B ++ [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]).length,true⟩]⟩) = some (e : Int) := by
    have E := Env (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)])
      (B ++ [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]).length,true⟩]) ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [den_variable]; exact E.2.2
  have v3 : (NExpr.cast u64 (.variable u32 0)).denote (penv ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)] ++
      [(⟨u64,(e : Int)⟩ : Cell)], B ++ [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]).length,true⟩] ++
      [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩]⟩) = some (m : Int) := by
    have E := Env (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,(e : Int)⟩ : Cell)])
      (B ++ [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]).length,true⟩] ++
        [⟨(P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩])
      ⟨[(⟨u64,(x : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell)], by simp⟩ ⟨_, rfl⟩
    exact cast64_den _ 0 (m : Int) E.1 (by omega) (by omega)
  obtain ⟨r, ht, hret, hcost, hneed, L, hmem⟩ := three_decl_tail 3 (by omega) (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) B hB _ _ _ x e m hm
    hmle hx64 he v1 v2 v3 retE v hn (by decide) (by decide) (by decide) hden
  exact ⟨r, ht, hret, hcost, by omega, L, hmem⟩

theorem power_exec (P0 : List Cell) (a1 a2 m x e : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm : 0 < m) (hm32 : m < 4294967296) (hx : x < 4294967296)
    (he : e < 18446744073709551616) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_power_x.body
        ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)],[⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]⟩ = some r ∧
      r.ret = some ((x ^ e % m : Nat) : Int) ∧ r.cost ≤ 3100 ∧ r.need ≤ P0.length + 70 ∧
      ∃ L, r.ps.mem = P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L := by
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x < 18446744073709551616 := by omega
  have hexp : e < 2 ^ 64 := by simpa using he
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have hden : ∀ bF : Nat, bF < m →
      retPowE.denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]
        (mk (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)))) =
      some ((pw m 64 (1 % m) (x % m) e : Nat) : Int) := by
    intro bF hbF
    have hokF := hok_of m x e bF hm hmle hx64 he hbF
    have e6 := res_env 3 (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩] rfl x e m bF hokF
    have eF0 : penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]
        (mk (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0))) 0 u32 = some (m : Int) := by
      refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
      show (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ cm ((sv x e m (pw m 64 (1 % m) (x % m) e) bF 0).map Nat.cast))[a1]? = _
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left l1]; exact h1
    exact ret_den_at 6 _ _ _ e6 eF0 (Int.natCast_nonneg _) (by exact_mod_cast hokF.r_lt) (by omega)
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := power_core P0 a1 a2 m x e h1 h2 hm hm32 hx he retPowE _ (by decide) hden
  rw [PowModCall.pow_mod_spec x e m hm hexp] at h2'
  exact ⟨r, by rw [power_body]; exact h1', h2', h3', h4', L, h5'⟩

theorem power_m_exec (P0 : List Cell) (a1 a2 m x e : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm : 0 < m) (hm32 : m < 4294967296) (hx : x < 4294967296)
    (he : e < 18446744073709551616) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_power_m.body
        ⟨P0 ++ [(⟨u64,(e : Int)⟩ : Cell)],[⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]⟩ = some r ∧
      r.ret = some (m : Int) ∧ r.cost ≤ 3100 ∧ r.need ≤ P0.length + 70 ∧
      ∃ L, r.ps.mem = P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ L := by
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have hden : ∀ bF : Nat, bF < m →
      (NExpr.variable u32 0).denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨P0.length+0,true⟩]
        (mk (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)]) (sv x e m (pw m 64 (1 % m) (x % m) e) bF 0)))) = some (m : Int) := by
    intro bF hbF
    rw [den_variable]
    refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
    show (P0 ++ [(⟨u64,(e : Int)⟩ : Cell)] ++ cm ((sv x e m (pw m 64 (1 % m) (x % m) e) bF 0).map Nat.cast))[a1]? = _
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left l1]; exact h1
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := power_core P0 a1 a2 m x e h1 h2 hm hm32 hx he (.variable u32 0) _ (by decide) hden
  exact ⟨r, by rw [power_m_body]; exact h1', h2', h3', h4', L, h5'⟩

abbrev chkNZ (i : Nat) : NStmt := .check (.binary bl .ne (.variable u32 i) (.cast u32 (.literal i32 0)))

theorem inv_body : Proofs.DynamicModIntInstance.DModInt_inv_x.body =
    .sequence (.primitive (chkNZ 1))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0))))
    (tailCmd 2 (retPowAt 5))))) := rfl

theorem inv_m_body : Proofs.DynamicModIntInstance.DModInt_inv_m.body =
    .sequence (.primitive (chkNZ 1))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0))))
    (tailCmd 2 (.variable u32 0))))) := rfl

theorem div_m_body : Proofs.DynamicModIntInstance.DModInt_div_m.body =
    .sequence (.primitive (chkNZ 3))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 3))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0))))
    (tailCmd 4 (.variable u32 0))))) := rfl

theorem chk_den (env : Nat → Ty → Option Int) (i : Nat) (x : Int) (h : env i u32 = some x) (hx0 : x ≠ 0)
    (hx32 : 0 ≤ x ∧ x < 4294967296) :
    (NExpr.binary bl .ne (.variable u32 i) (.cast u32 (.literal i32 0))).denote env = some 1 := by
  rw [den_binary, den_variable, h, Option.bind_some, den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl),
    Option.bind_some, convert_u32, Option.bind_some]
  have : binaryValue .ne x (0 % 4294967296) = 1 := by
    show (if (x != 0 % 4294967296) = true then 1 else 0) = _
    have : (x != 0 % 4294967296) = true := by simp [hx0]
    rw [if_pos this]
  rw [this]
  rfl

theorem inv_core (P0 : List Cell) (a1 a2 m x : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx : x < 4294967296) (hx0 : x ≠ 0) (retE : NExpr) (v : Int) (hn : retE.nodes ≤ 10)
    (hden : ∀ bF : Nat, bF < m → retE.denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩]
      (mk P0 (sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0)))) = some v) :
    ∃ r : PR, pexec 70 (.sequence (.primitive (chkNZ 1))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 1))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0)))) (tailCmd 2 retE)))))
      ⟨P0,[⟨a1,false⟩,⟨a2,false⟩]⟩ = some r ∧
      r.ret = some v ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧ ∃ L, r.ps.mem = P0 ++ L := by
  have hm : 0 < m := by omega
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x < 18446744073709551616 := by omega
  have he : m - 2 < 18446744073709551616 := by omega
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have l2 : a2 < P0.length := (List.getElem?_eq_some_iff.mp h2).1
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have xv32 : u32.valid (x : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  let B : List CppState.Binding := [⟨a1,false⟩,⟨a2,false⟩]
  have hB : B.length = 2 := rfl
  have E1 : penv ⟨P0,B⟩ 1 u32 = some (x : Int) := penv_ok ⟨P0,B⟩ 1 u32 ⟨a2,false⟩ ⟨u32,(x : Int)⟩ rfl h2 rfl xv32
  have chk := chk_den (penv ⟨P0,B⟩) 1 (x : Int) E1 (by exact_mod_cast hx0) ⟨by omega, by omega⟩
  have sc : pstmt (chkNZ 1) ⟨P0,B⟩ = some ⟨⟨P0,B⟩, none,
      (NExpr.binary bl .ne (.variable u32 1) (.cast u32 (.literal i32 0))).nodes + 1,
      P0.length + B.length + (NExpr.binary bl .ne (.variable u32 1) (.cast u32 (.literal i32 0))).nodes + 2⟩ := by
    simp [pstmt, chkNZ, chk]
  have qc := (pexec_prim 70 _ _).trans sc
  have v1 : (NExpr.cast u64 (.variable u32 1)).denote (penv ⟨P0,B⟩) = some (x : Int) :=
    cast64_den _ 1 (x : Int) E1 (by omega) (by omega)
  have E0b : ∀ L : List Cell, ∀ Bx : List CppState.Binding,
      penv ⟨P0 ++ L, B ++ Bx⟩ 0 u32 = some (m : Int) := by
    intro L Bx
    refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
    show (P0 ++ L)[a1]? = _
    rw [List.getElem?_append_left l1]; exact h1
  have E0c : ∀ (mem : List Cell) (Bs : List CppState.Binding), (∃ L, mem = P0 ++ L) → (∃ Y, Bs = B ++ Y) →
      penv ⟨mem, Bs⟩ 0 u32 = some (m : Int) := by
    rintro mem Bs ⟨L, rfl⟩ ⟨Y, rfl⟩
    exact E0b L Y
  have v2 : (NExpr.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2))).denote
      (penv ⟨P0 ++ [(⟨u64,(x : Int)⟩ : Cell)], B ++ [⟨P0.length,true⟩]⟩) = some ((m - 2 : Nat) : Int) := by
    have h0 := cast64_den (penv ⟨P0 ++ [(⟨u64,(x : Int)⟩ : Cell)], B ++ [⟨P0.length,true⟩]⟩) 0 (m : Int)
      (E0b [(⟨u64,(x : Int)⟩ : Cell)] [⟨P0.length,true⟩]) (by omega) (by omega)
    have h2' : (NExpr.cast u64 (.literal i32 2)).denote (penv ⟨P0 ++ [(⟨u64,(x : Int)⟩ : Cell)], B ++ [⟨P0.length,true⟩]⟩) = some 2 := by
      rw [den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, convert_u64]
      rfl
    refine DynamicModIntCall.u64_bin _ .sub _ _ (m : Int) 2 h0 h2' ((m - 2 : Nat) : Int) ?_ (Int.natCast_nonneg _) (by omega)
    show (m : Int) - 2 = _
    omega
  have v3 : (NExpr.cast u64 (.variable u32 0)).denote
      (penv ⟨P0 ++ [(⟨u64,(x : Int)⟩ : Cell)] ++ [(⟨u64,((m - 2 : Nat) : Int)⟩ : Cell)],
        B ++ [⟨P0.length,true⟩] ++ [⟨(P0 ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩]⟩) = some (m : Int) :=
    cast64_den _ 0 (m : Int) (E0c _ _ ⟨[(⟨u64,(x : Int)⟩ : Cell),(⟨u64,((m - 2 : Nat) : Int)⟩ : Cell)], by simp⟩
      ⟨[⟨P0.length,true⟩,⟨(P0 ++ [(⟨u64,(x : Int)⟩ : Cell)]).length,true⟩], by simp⟩) (by omega) (by omega)
  obtain ⟨r, ht, hret, hcost, hneed, L, hmem⟩ := three_decl_tail 2 (by omega) P0 B hB _ _ _ x (m - 2) m hm hmle hx64 he
    v1 v2 v3 retE v hn (by decide) (by decide) (by decide) hden
  have b0 := seq_some qc rfl ht
  have hnn : (NExpr.binary bl .ne (.variable u32 1) (.cast u32 (.literal i32 0))).nodes ≤ 10 := by decide
  refine ⟨_, b0, ?_, ?_, ?_, ⟨L, ?_⟩⟩
  · simpa using hret
  · simp
    omega
  · simp [hB]
    omega
  · simpa using hmem


theorem inv_exec (P0 : List Cell) (a1 a2 m x : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx : x < 4294967296) (hx0 : x ≠ 0) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_inv_x.body ⟨P0,[⟨a1,false⟩,⟨a2,false⟩]⟩ = some r ∧
      r.ret = some ((x ^ (m - 2) % m : Nat) : Int) ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧ ∃ L, r.ps.mem = P0 ++ L := by
  have hm : 0 < m := by omega
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x < 18446744073709551616 := by omega
  have he : m - 2 < 18446744073709551616 := by omega
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have hden : ∀ bF : Nat, bF < m → (retPowAt 5).denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩]
      (mk P0 (sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0)))) = some ((pw m 64 (1 % m) (x % m) (m - 2) : Nat) : Int) := by
    intro bF hbF
    have hokF := hok_of m x (m - 2) bF hm hmle hx64 he hbF
    have e5 := res_env 2 P0 [⟨a1,false⟩,⟨a2,false⟩] rfl x (m - 2) m bF hokF
    have eF0 : penv (shPS [⟨a1,false⟩,⟨a2,false⟩] (mk P0 (sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0))) 0 u32 = some (m : Int) := by
      refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
      show (P0 ++ cm ((sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0).map Nat.cast))[a1]? = _
      rw [List.getElem?_append_left l1]; exact h1
    exact ret_den_at 5 _ _ _ e5 eF0 (Int.natCast_nonneg _) (by exact_mod_cast hokF.r_lt) (by omega)
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := inv_core P0 a1 a2 m x h1 h2 hm2 hm32 hx hx0 (retPowAt 5) _ (by decide) hden
  rw [PowModCall.pow_mod_spec x (m - 2) m hm (by simpa using he)] at h2'
  exact ⟨r, by rw [inv_body]; exact h1', h2', h3', h4', L, h5'⟩

theorem inv_m_exec (P0 : List Cell) (a1 a2 m x : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x : Int)⟩) (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx : x < 4294967296) (hx0 : x ≠ 0) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_inv_m.body ⟨P0,[⟨a1,false⟩,⟨a2,false⟩]⟩ = some r ∧
      r.ret = some (m : Int) ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧ ∃ L, r.ps.mem = P0 ++ L := by
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have hden : ∀ bF : Nat, bF < m → (NExpr.variable u32 0).denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩]
      (mk P0 (sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0)))) = some (m : Int) := by
    intro bF hbF
    rw [den_variable]
    refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
    show (P0 ++ cm ((sv x (m - 2) m (pw m 64 (1 % m) (x % m) (m - 2)) bF 0).map Nat.cast))[a1]? = _
    rw [List.getElem?_append_left l1]; exact h1
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := inv_core P0 a1 a2 m x h1 h2 hm2 hm32 hx hx0 (.variable u32 0) _ (by decide) hden
  exact ⟨r, by rw [inv_m_body]; exact h1', h2', h3', h4', L, h5'⟩

abbrev retDivE : NExpr :=
  .divrem u32 true (.cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 1)) (.variable u64 7))
    (.variable u64 6))) (.variable u32 0)

theorem div_body : Proofs.DynamicModIntInstance.DModInt_div_x.body =
    .sequence (.primitive (chkNZ 3))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 3))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0))))
    (tailCmd 4 retDivE)))) := rfl

theorem div_core (P0 : List Cell) (a1 a2 a3 a4 m x1 m2 x2 : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x1 : Int)⟩) (h3 : P0[a3]? = some ⟨u32,(m2 : Int)⟩) (h4 : P0[a4]? = some ⟨u32,(x2 : Int)⟩)
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx1 : x1 < 4294967296) (hx2 : x2 < 4294967296) (hx0 : x2 ≠ 0)
    (retE : NExpr) (v : Int) (hn : retE.nodes ≤ 10)
    (hden : ∀ bF : Nat, bF < m → retE.denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]
      (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)))) = some v) :
    ∃ r : PR, pexec 70 (.sequence (.primitive (chkNZ 3))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 3))))
    (.sequence (.primitive (.declare u64 true (.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2)))))
    (.sequence (.primitive (.declare u64 true (.cast u64 (.variable u32 0)))) (tailCmd 4 retE)))))
      ⟨P0,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some v ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧
      ∃ L, r.ps.mem = P0 ++ L := by
  have hm : 0 < m := by omega
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x2 < 18446744073709551616 := by omega
  have he : m - 2 < 18446744073709551616 := by omega
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have l2 : a2 < P0.length := (List.getElem?_eq_some_iff.mp h2).1
  have l4 : a4 < P0.length := (List.getElem?_eq_some_iff.mp h4).1
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have x1v32 : u32.valid (x1 : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have x2v32 : u32.valid (x2 : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  let B : List CppState.Binding := [⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]
  have hB : B.length = 4 := rfl
  -- environment facts valid in every state whose memory starts with `P0` and bindings with `B`
  have Env : ∀ (mem : List Cell) (Bs : List CppState.Binding), (∃ L, mem = P0 ++ L) → (∃ Y, Bs = B ++ Y) →
      penv ⟨mem, Bs⟩ 0 u32 = some (m : Int) ∧ penv ⟨mem, Bs⟩ 1 u32 = some (x1 : Int) ∧
      penv ⟨mem, Bs⟩ 3 u32 = some (x2 : Int) := by
    rintro mem Bs ⟨L, rfl⟩ ⟨Y, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
      show (P0 ++ L)[a1]? = _
      rw [List.getElem?_append_left l1]; exact h1
    · refine penv_ok _ 1 u32 ⟨a2,false⟩ ⟨u32,(x1 : Int)⟩ rfl ?_ rfl x1v32
      show (P0 ++ L)[a2]? = _
      rw [List.getElem?_append_left l2]; exact h2
    · refine penv_ok _ 3 u32 ⟨a4,false⟩ ⟨u32,(x2 : Int)⟩ rfl ?_ rfl x2v32
      show (P0 ++ L)[a4]? = _
      rw [List.getElem?_append_left l4]; exact h4
  have E0 := Env P0 B ⟨[], by simp⟩ ⟨[], by simp⟩
  have chk := chk_den (penv ⟨P0,B⟩) 3 (x2 : Int) E0.2.2 (by exact_mod_cast hx0) ⟨by omega, by omega⟩
  have sc : pstmt (chkNZ 3) ⟨P0,B⟩ = some ⟨⟨P0,B⟩, none,
      (NExpr.binary bl .ne (.variable u32 3) (.cast u32 (.literal i32 0))).nodes + 1,
      P0.length + B.length + (NExpr.binary bl .ne (.variable u32 3) (.cast u32 (.literal i32 0))).nodes + 2⟩ := by
    simp [pstmt, chkNZ, chk]
  have qc := (pexec_prim 70 _ _).trans sc
  have v1 : (NExpr.cast u64 (.variable u32 3)).denote (penv ⟨P0,B⟩) = some (x2 : Int) :=
    cast64_den _ 3 (x2 : Int) E0.2.2 (by omega) (by omega)
  have lit2 : ∀ env : Nat → Ty → Option Int, (NExpr.cast u64 (.literal i32 2)).denote env = some 2 := by
    intro env
    rw [den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have v2 : (NExpr.binary u64 .sub (.cast u64 (.variable u32 0)) (.cast u64 (.literal i32 2))).denote
      (penv ⟨P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)], B ++ [⟨P0.length,true⟩]⟩) = some ((m - 2 : Nat) : Int) := by
    have E := Env (P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)]) (B ++ [⟨P0.length,true⟩]) ⟨_, rfl⟩ ⟨_, rfl⟩
    have h0 := cast64_den _ 0 (m : Int) E.1 (by omega) (by omega)
    refine DynamicModIntCall.u64_bin _ .sub _ _ (m : Int) 2 h0 (lit2 _) ((m - 2 : Nat) : Int) ?_ (Int.natCast_nonneg _) (by omega)
    show (m : Int) - 2 = _
    omega
  have v3 : (NExpr.cast u64 (.variable u32 0)).denote
      (penv ⟨P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)] ++ [(⟨u64,((m - 2 : Nat) : Int)⟩ : Cell)],
        B ++ [⟨P0.length,true⟩] ++ [⟨(P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)]).length,true⟩]⟩) = some (m : Int) := by
    have E := Env (P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)] ++ [(⟨u64,((m - 2 : Nat) : Int)⟩ : Cell)])
      (B ++ [⟨P0.length,true⟩] ++ [⟨(P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)]).length,true⟩])
      ⟨[(⟨u64,(x2 : Int)⟩ : Cell),(⟨u64,((m - 2 : Nat) : Int)⟩ : Cell)], by simp⟩
      ⟨[⟨P0.length,true⟩,⟨(P0 ++ [(⟨u64,(x2 : Int)⟩ : Cell)]).length,true⟩], by simp⟩
    exact cast64_den _ 0 (m : Int) E.1 (by omega) (by omega)
  obtain ⟨r, ht, hret, hcost, hneed, L, hmem⟩ := three_decl_tail 4 (by omega) P0 B hB _ _ _ x2 (m - 2) m hm hmle hx64 he
    v1 v2 v3 retE v hn (by decide) (by decide) (by decide) hden
  have b0 := seq_some qc rfl ht
  have hnn : (NExpr.binary bl .ne (.variable u32 3) (.cast u32 (.literal i32 0))).nodes ≤ 10 := by decide
  refine ⟨_, b0, ?_, ?_, ?_, ⟨L, ?_⟩⟩
  · simpa using hret
  · simp
    omega
  · simp [hB]
    omega
  · simpa using hmem


theorem div_exec (P0 : List Cell) (a1 a2 a3 a4 m x1 m2 x2 : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x1 : Int)⟩) (h3 : P0[a3]? = some ⟨u32,(m2 : Int)⟩) (h4 : P0[a4]? = some ⟨u32,(x2 : Int)⟩)
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx1 : x1 < 4294967296) (hx2 : x2 < 4294967296) (hx0 : x2 ≠ 0) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_div_x.body ⟨P0,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some ((x1 * (x2 ^ (m - 2) % m) % m : Nat) : Int) ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧
      ∃ L, r.ps.mem = P0 ++ L := by
  have hm : 0 < m := by omega
  have hmle : m ≤ 4294967296 := by omega
  have hx64 : x2 < 18446744073709551616 := by omega
  have he : m - 2 < 18446744073709551616 := by omega
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have l2 : a2 < P0.length := (List.getElem?_eq_some_iff.mp h2).1
  have l4 : a4 < P0.length := (List.getElem?_eq_some_iff.mp h4).1
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have x1v32 : u32.valid (x1 : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have x2v32 : u32.valid (x2 : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  let B : List CppState.Binding := [⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]
  have hB : B.length = 4 := rfl
  -- environment facts valid in every state whose memory starts with `P0` and bindings with `B`
  have Env : ∀ (mem : List Cell) (Bs : List CppState.Binding), (∃ L, mem = P0 ++ L) → (∃ Y, Bs = B ++ Y) →
      penv ⟨mem, Bs⟩ 0 u32 = some (m : Int) ∧ penv ⟨mem, Bs⟩ 1 u32 = some (x1 : Int) ∧
      penv ⟨mem, Bs⟩ 3 u32 = some (x2 : Int) := by
    rintro mem Bs ⟨L, rfl⟩ ⟨Y, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
      show (P0 ++ L)[a1]? = _
      rw [List.getElem?_append_left l1]; exact h1
    · refine penv_ok _ 1 u32 ⟨a2,false⟩ ⟨u32,(x1 : Int)⟩ rfl ?_ rfl x1v32
      show (P0 ++ L)[a2]? = _
      rw [List.getElem?_append_left l2]; exact h2
    · refine penv_ok _ 3 u32 ⟨a4,false⟩ ⟨u32,(x2 : Int)⟩ rfl ?_ rfl x2v32
      show (P0 ++ L)[a4]? = _
      rw [List.getElem?_append_left l4]; exact h4
  have hden : ∀ bF : Nat, bF < m → retDivE.denote (penv (shPS B (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)))) =
      some ((x1 * (pw m 64 (1 % m) (x2 % m) (m - 2)) % m : Nat) : Int) := by
    intro bF hbF
    have hokF := hok_of m x2 (m - 2) bF hm hmle hx64 he hbF
    have hrFlt := hokF.r_lt
    have hrleI : ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int) ≤ 4294967295 := by omega
    have e7 : penv (shPS B (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0))) 7 u64 =
        some ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int) := res_env 4 P0 B hB x2 (m - 2) m bF hokF
    have e6 : penv (shPS B (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0))) 6 u64 = some (m : Int) := by
      have := penv_sh (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)).mem
        (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)).bs B 2 u64
      rw [hB] at this
      exact this.trans (env_sv P0 hokF).2.2.1
    have EF := Env (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)).mem
      (B ++ (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)).bs) ⟨_, rfl⟩ ⟨_, rfl⟩
    have hinner : (NExpr.binary u64 .mul (.cast u64 (.variable u32 1)) (.variable u64 7)).denote
        (penv (shPS B (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)))) =
        some ((x1 : Int) * ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int)) := by
      refine DynamicModIntCall.u64_bin _ .mul _ _ (x1 : Int) _ (cast64_den _ 1 (x1 : Int) EF.2.1 (by omega) (by omega)) (by rw [den_variable]; exact e7) _ rfl
        (Int.mul_nonneg (by omega) (Int.natCast_nonneg _)) ?_
      have : (x1 : Int) * ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int) ≤ 4294967295 * 4294967295 :=
        Int.mul_le_mul (by omega) hrleI (Int.natCast_nonneg _) (by omega)
      omega
    have := DynamicModIntCall.wrap_den_g _ _ (.variable u64 6) ((x1 : Int) * ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int))
      (m : Int) (by omega) (by omega) (Int.mul_nonneg (by omega) (Int.natCast_nonneg _))
      (by
        have : (x1 : Int) * ((pw m 64 (1 % m) (x2 % m) (m - 2) : Nat) : Int) ≤ 4294967295 * 4294967295 :=
          Int.mul_le_mul (by omega) hrleI (Int.natCast_nonneg _) (by omega)
        omega) hinner (by rw [den_variable]; exact e6) EF.1
    rw [this]
    congr 1
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := div_core P0 a1 a2 a3 a4 m x1 m2 x2 h1 h2 h3 h4 hm2 hm32 hx1 hx2 hx0 retDivE _
    (by decide) hden
  rw [PowModCall.pow_mod_spec x2 (m - 2) m hm (by simpa using he)] at h2'
  exact ⟨r, by rw [div_body]; exact h1', h2', h3', h4', L, h5'⟩

theorem div_m_exec (P0 : List Cell) (a1 a2 a3 a4 m x1 m2 x2 : Nat) (h1 : P0[a1]? = some ⟨u32,(m : Int)⟩)
    (h2 : P0[a2]? = some ⟨u32,(x1 : Int)⟩) (h3 : P0[a3]? = some ⟨u32,(m2 : Int)⟩) (h4 : P0[a4]? = some ⟨u32,(x2 : Int)⟩)
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx1 : x1 < 4294967296) (hx2 : x2 < 4294967296) (hx0 : x2 ≠ 0) :
    ∃ r : PR, pexec 70 Proofs.DynamicModIntInstance.DModInt_div_m.body ⟨P0,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some (m : Int) ∧ r.cost ≤ 3200 ∧ r.need ≤ P0.length + 70 ∧ ∃ L, r.ps.mem = P0 ++ L := by
  have mv32 : u32.valid (m : Int) = true := DynamicModIntCall.u32_valid_of _ (by omega) (by omega)
  have l1 : a1 < P0.length := (List.getElem?_eq_some_iff.mp h1).1
  have hden : ∀ bF : Nat, bF < m → (NExpr.variable u32 0).denote (penv (shPS [⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]
      (mk P0 (sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0)))) = some (m : Int) := by
    intro bF hbF
    rw [den_variable]
    refine penv_ok _ 0 u32 ⟨a1,false⟩ ⟨u32,(m : Int)⟩ rfl ?_ rfl mv32
    show (P0 ++ cm ((sv x2 (m - 2) m (pw m 64 (1 % m) (x2 % m) (m - 2)) bF 0).map Nat.cast))[a1]? = _
    rw [List.getElem?_append_left l1]; exact h1
  obtain ⟨r, h1', h2', h3', h4', L, h5'⟩ := div_core P0 a1 a2 a3 a4 m x1 m2 x2 h1 h2 h3 h4 hm2 hm32 hx1 hx2 hx0 (.variable u32 0) _
    (by decide) hden
  exact ⟨r, by rw [div_m_body]; exact h1', h2', h3', h4', L, h5'⟩

open Proofs.ScalarRefs Proofs.ScalarRefsV Proofs.MonoidCall Proofs.IntervalCall Proofs.ScalarCall Proofs.CppNestedCall Proofs.CppNestedEval Proofs.ScalarStraight Proofs.DoublingCall

theorem dmodint_power_x_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x : Int)⟩))
    (ex : NExpr) (eN : Nat) (hs : ex.scalarOnly = true) (ht : ex.resultType = u64)
    (value : ex.denote (envOf caller) = some (eN : Int)) (he : eN < 18446744073709551616)
    (hm : 0 < m) (hm32 : m < 4294967296) (hx : x < 4294967296)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_power_x.parameters
        [.scalarReference s1,.scalarReference s2,.value ex] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_power_x.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value ex] =
        .finished (res,.scalar ((x ^ eN % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res (2 + ex.nodes) 3180 caller.scalars.memory := by
  have hres : (x ^ eN % m) < 4294967296 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) (by omega)
  refine R2V1_correct _ u32 u32 u32 u64 rfl rfl (by rw [power_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN])
    caller s1 s2 b1 b2 (m : Int) (x : Int) ex (eN : Int) c1 c2 hs ht value (u64_lt _ he) valid lengths strict base 70
    ((x ^ eN % m : Nat) : Int) (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3100 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := power_exec (callerP caller) b1.address b2.address m x eN
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x : Int) c2) hm hm32 hx he
  refine ⟨r, h1, h2, h3, by simp at h4 ⊢; omega, ?_⟩
  rw [h5]
  have := take_P caller ([(⟨u64,(eN : Int)⟩ : Cell)] ++ L)
  simpa [List.append_assoc] using this

theorem dmodint_power_m_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x : Int)⟩))
    (ex : NExpr) (eN : Nat) (hs : ex.scalarOnly = true) (ht : ex.resultType = u64)
    (value : ex.denote (envOf caller) = some (eN : Int)) (he : eN < 18446744073709551616)
    (hm : 0 < m) (hm32 : m < 4294967296) (hx : x < 4294967296)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_power_m.parameters
        [.scalarReference s1,.scalarReference s2,.value ex] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_power_m.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value ex] =
        .finished (res,.scalar (m : Int)) ∧
      ScalarPost2 caller Sinit res (2 + ex.nodes) 3180 caller.scalars.memory := by
  refine R2V1_correct _ u32 u32 u32 u64 rfl rfl
    (by rw [power_m_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN])
    caller s1 s2 b1 b2 (m : Int) (x : Int) ex (eN : Int) c1 c2 hs ht value (u64_lt _ he) valid lengths strict base 70
    (m : Int) (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3100 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := power_m_exec (callerP caller) b1.address b2.address m x eN
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x : Int) c2) hm hm32 hx he
  refine ⟨r, h1, h2, h3, by simp at h4 ⊢; omega, ?_⟩
  rw [h5]
  have := take_P caller ([(⟨u64,(eN : Int)⟩ : Cell)] ++ L)
  simpa [List.append_assoc] using this

theorem dmodint_inv_x_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x : Int)⟩))
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx : x < 4294967296) (hx0 : x ≠ 0)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_inv_x.parameters
        [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_inv_x.callFuel fuel caller [.scalarReference s1,.scalarReference s2] =
        .finished (res,.scalar ((x ^ (m - 2) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 3260 caller.scalars.memory := by
  have hres : (x ^ (m - 2) % m) < 4294967296 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  refine refs2t_correct _ u32 u32 u32 rfl rfl
    (by rw [inv_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN, chkNZ])
    caller s1 s2 b1 b2 (m : Int) (x : Int) c1 c2 valid lengths strict base 70 ((x ^ (m - 2) % m : Nat) : Int)
    (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3200 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := inv_exec (callerP caller) b1.address b2.address m x
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x : Int) c2) hm2 hm32 hx hx0
  refine ⟨r, h1, h2, h3, by omega, ?_⟩
  rw [h5]; exact take_P caller L

theorem dmodint_inv_m_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (m x : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x : Int)⟩))
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx : x < 4294967296) (hx0 : x ≠ 0)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_inv_m.parameters
        [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_inv_m.callFuel fuel caller [.scalarReference s1,.scalarReference s2] =
        .finished (res,.scalar (m : Int)) ∧
      ScalarPost2 caller Sinit res 0 3260 caller.scalars.memory := by
  refine refs2t_correct _ u32 u32 u32 rfl rfl
    (by rw [inv_m_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN, chkNZ])
    caller s1 s2 b1 b2 (m : Int) (x : Int) c1 c2 valid lengths strict base 70 (m : Int)
    (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3200 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := inv_m_exec (callerP caller) b1.address b2.address m x
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x : Int) c2) hm2 hm32 hx hx0
  refine ⟨r, h1, h2, h3, by omega, ?_⟩
  rw [h5]; exact take_P caller L

theorem dmodint_div_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x1 m2 x2 : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x1 : Int)⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,(m2 : Int)⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,(x2 : Int)⟩))
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx1 : x1 < 4294967296) (hx2 : x2 < 4294967296) (hm2' : m2 < 4294967296)
    (hx0 : x2 ≠ 0)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_div_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_div_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar ((x1 * (x2 ^ (m - 2) % m) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 3260 caller.scalars.memory := by
  have hres : (x1 * (x2 ^ (m - 2) % m) % m) < 4294967296 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  refine refs4t_correct _ u32 u32 u32 u32 u32 rfl rfl
    (by rw [div_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN, chkNZ])
    caller s1 s2 s3 s4 b1 b2 b3 b4 (m : Int) (x1 : Int) (m2 : Int) (x2 : Int) c1 c2 c3 c4 valid lengths strict base 70
    ((x1 * (x2 ^ (m - 2) % m) % m : Nat) : Int) (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3200 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := div_exec (callerP caller) b1.address b2.address b3.address b4.address m x1 m2 x2
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x1 : Int) c2)
    (P_cell_ty caller s3 u32 b3 (m2 : Int) c3) (P_cell_ty caller s4 u32 b4 (x2 : Int) c4) hm2 hm32 hx1 hx2 hx0
  refine ⟨r, h1, h2, h3, by omega, ?_⟩
  rw [h5]; exact take_P caller L

theorem dmodint_div_m_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (m x1 m2 x2 : Nat)
    (c1 : caller.scalarCell s1 u32 = some (b1,⟨u32,(m : Int)⟩)) (c2 : caller.scalarCell s2 u32 = some (b2,⟨u32,(x1 : Int)⟩))
    (c3 : caller.scalarCell s3 u32 = some (b3,⟨u32,(m2 : Int)⟩)) (c4 : caller.scalarCell s4 u32 = some (b4,⟨u32,(x2 : Int)⟩))
    (hm2 : 2 ≤ m) (hm32 : m < 4294967296) (hx1 : x1 < 4294967296) (hx2 : x2 < 4294967296) (hx0 : x2 ≠ 0)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.DynamicModIntInstance.DModInt_div_m.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.DynamicModIntInstance.DModInt_div_m.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (m : Int)) ∧
      ScalarPost2 caller Sinit res 0 3260 caller.scalars.memory := by
  refine refs4t_correct _ u32 u32 u32 u32 u32 rfl rfl
    (by rw [div_m_body]; simp [Scalar, NExpr.scalarOnly, Command.shN, NExpr.shN, NStmt.shN, chkNZ])
    caller s1 s2 s3 s4 b1 b2 b3 b4 (m : Int) (x1 : Int) (m2 : Int) (x2 : Int) c1 c2 c3 c4 valid lengths strict base 70
    (m : Int) (DynamicModIntCall.u32_valid_of _ (by omega) (by omega)) 3200 ?_
  intro P hP
  subst hP
  obtain ⟨r, h1, h2, h3, h4, L, h5⟩ := div_m_exec (callerP caller) b1.address b2.address b3.address b4.address m x1 m2 x2
    (P_cell_ty caller s1 u32 b1 (m : Int) c1) (P_cell_ty caller s2 u32 b2 (x1 : Int) c2)
    (P_cell_ty caller s3 u32 b3 (m2 : Int) c3) (P_cell_ty caller s4 u32 b4 (x2 : Int) c4) hm2 hm32 hx1 hx2 hx0
  refine ⟨r, h1, h2, h3, by omega, ?_⟩
  rw [h5]; exact take_P caller L


end Pow

end Proofs.DynamicModIntCall
