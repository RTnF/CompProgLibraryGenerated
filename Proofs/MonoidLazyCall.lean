import Proofs.ScalarRefsV
import Proofs.Generated.MonoidLazy

namespace Proofs.MonoidLazyCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall Proofs.IntervalCall Proofs.ScalarRefs Proofs.ScalarRefsV
open Proofs.CppState (Cell)

theorem conv_signed (t : Ty) (hs : t.boolean = false) (hg : t.signed = true) (v : Int) (h : t.valid v = true) :
    t.convert v = some v := by
  unfold Ty.convert
  simp [hs, hg, h]

theorem s64_of_i32 (x : Int) (h : i32.valid x = true) : s64.valid x = true := by
  have h' := h
  simp [Ty.valid, i32] at h'
  rw [valid_s64]
  simp
  omega

/-- `if (c) { return a; } return b;` -/
abbrev selRet (c a b : NExpr) : Command :=
  .sequence (.branch c (.sequence (.scope (.sequence (.primitive (.ret a)) Sk)) Sk) Sk) (.sequence (.primitive (.ret b)) Sk)

theorem selRet_exec (c a b : NExpr) (ps : PS) (cv x y : Int) (hc : c.denote (penv ps) = some cv)
    (ha : a.denote (penv ps) = some x) (hb : b.denote (penv ps) = some y) :
    ∃ r, pexec 1 (selRet c a b) ps = some r ∧ r.ret = some (if cv ≠ 0 then x else y) ∧
      r.cost ≤ c.nodes + a.nodes + b.nodes + 6 ∧ r.need ≤ ps.mem.length + ps.bs.length + c.nodes + a.nodes + b.nodes + 6 ∧
      r.ps.mem = ps.mem := by
  have rb := exec_ret 1 ps b y hb
  by_cases hz : cv = 0
  · subst hz
    have br := pexec_branch_false 1 c (.sequence (.scope (.sequence (.primitive (.ret a)) Sk)) Sk) Sk ps hc _ (pexec_skip 1 ps)
    have t := seq_some br rfl (by simpa using rb)
    refine ⟨_, t, by simp, ?_, ?_, by simp⟩
    · simp; omega
    · simp; omega
  · have ra := exec_ret 1 ps a x ha
    have sc := pexec_scope 1 _ ps _ ra
    have yes := seq_ret (b := Sk) sc rfl
    have br := pexec_branch_true 1 c _ Sk ps cv hc hz _ yes
    have t := seq_ret (b := .sequence (.primitive (.ret b)) Sk) br rfl
    refine ⟨_, t, by simp [hz], ?_, ?_, by simp⟩
    · simp; omega
    · simp; omega

theorem refVal (caller : NState) (s : Nat) (t : Ty) (b : CppState.Binding) (x : Int)
    (c : caller.scalarCell s t = some (b,⟨t,x⟩)) (extra : List Cell) :
    (callerP caller ++ extra)[b.address]? = some ⟨t,x⟩ := by
  have h := P_cell_ty caller s t b x c
  have l : b.address < (callerP caller).length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left l]; exact h

abbrev opXE : NExpr := .binary s64 .add (.variable s64 0) (.variable s64 2)
abbrev opSizeE : NExpr := .binary i32 .add (.variable i32 1) (.variable i32 3)

theorem opx_body : Proofs.MonoidLazyInstance.RangeSum_long_long_op_x.body = .sequence (.primitive (.ret opXE)) Sk := rfl
theorem ops_body : Proofs.MonoidLazyInstance.RangeSum_long_long_op_size.body = .sequence (.primitive (.ret opSizeE)) Sk := rfl

theorem ret_exec_gen (e : NExpr) (v : Int) (ps : PS) (hden : e.denote (penv ps) = some v) (hn : e.nodes ≤ 10) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret e)) Sk) ps = some r ∧ r.ret = some v ∧ r.cost ≤ 12 ∧
      r.need ≤ ps.mem.length + ps.bs.length + 14 ∧ r.ps = ps := by
  refine ⟨_, exec_ret 1 ps e v hden, rfl, ?_, ?_, rfl⟩
  · simp; omega
  · simp; omega

theorem rangesum_op_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : s64.valid v1 = true) (g3 : s64.valid v3 = true) (gs : s64.valid (v1 + v3) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSum_long_long_op_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSum_long_long_op_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v1 + v3)) ∧
      ScalarPost2 caller Sinit res 0 72 caller.scalars.memory := by
  refine refs4t_correct _ s64 s64 i32 s64 i32 rfl rfl (by rw [opx_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4
    b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v1 + v3) gs 12 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v1⟩ rfl (P_cell_ty caller s1 s64 b1 v1 c1) rfl g1
  have e2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 2 s64 = some v3 :=
    penv_ok _ 2 s64 ⟨b3.address,false⟩ ⟨s64,v3⟩ rfl (P_cell_ty caller s3 s64 b3 v3 c3) rfl g3
  have den : opXE.denote (penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩) =
      some (v1 + v3) := by
    rw [den_binary, den_variable, den_variable, e0, e2]
    simp only [Option.bind_some]
    exact convS _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen opXE (v1 + v3) _ den (by decide)
  refine ⟨r, by rw [opx_body]; exact h1, h2, h3, by simp at h4; omega, by rw [h5]; exact take_callerP caller⟩

theorem rangesum_op_size_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g2 : i32.valid v2 = true) (g4 : i32.valid v4 = true) (gs : i32.valid (v2 + v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSum_long_long_op_size.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSum_long_long_op_size.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v2 + v4)) ∧
      ScalarPost2 caller Sinit res 0 72 caller.scalars.memory := by
  refine refs4t_correct _ i32 s64 i32 s64 i32 rfl rfl (by rw [ops_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4
    b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v2 + v4) gs 12 ?_
  intro P hP
  subst hP
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 i32 = some v2 :=
    penv_ok _ 1 i32 ⟨b2.address,false⟩ ⟨i32,v2⟩ rfl (P_cell_ty caller s2 i32 b2 v2 c2) rfl g2
  have e3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 3 i32 = some v4 :=
    penv_ok _ 3 i32 ⟨b4.address,false⟩ ⟨i32,v4⟩ rfl (P_cell_ty caller s4 i32 b4 v4 c4) rfl g4
  have den : opSizeE.denote (penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩) =
      some (v2 + v4) := by
    rw [den_binary, den_variable, den_variable, e1, e3]
    simp only [Option.bind_some]
    exact conv_signed i32 rfl rfl _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen opSizeE (v2 + v4) _ den (by decide)
  refine ⟨r, by rw [ops_body]; exact h1, h2, h3, by simp at h4; omega, by rw [h5]; exact take_callerP caller⟩

theorem rsae_body : Proofs.MonoidLazyInstance.RangeSet_long_long_applyExtremum.body = selRet (.variable bl 1) (.variable s64 2) (.variable s64 0) := rfl
theorem rsas_body : Proofs.MonoidLazyInstance.RangeSet_long_long_applySumX.body =
    selRet (.variable bl 1) (.variable s64 2) (.binary s64 .mul (.variable s64 0) (.cast s64 (.variable i32 3))) := rfl
theorem rscv_body : Proofs.MonoidLazyInstance.RangeSet_long_long_compose_v.body = selRet (.variable bl 1) (.variable s64 2) (.variable s64 0) := rfl
theorem rscn_body : Proofs.MonoidLazyInstance.RangeSet_long_long_compose_noop.body = selRet (.variable bl 1) (.variable bl 3) (.variable bl 1) := rfl

theorem selRet_scalar (c a b : NExpr) (hc : c.scalarOnly = true) (ha : a.scalarOnly = true) (hb : b.scalarOnly = true) :
    Scalar (selRet c a b) = true := by
  simp [Scalar, hc, ha, hb]

theorem rangeset_applyExtremum_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v noop : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,noop⟩))
    (e : NExpr) (m : Int) (hs : e.scalarOnly = true) (ht : e.resultType = s64)
    (value : e.denote (envOf caller) = some m) (gv : s64.valid v = true) (gn : bl.valid noop = true)
    (gm : s64.valid m = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSet_long_long_applyExtremum.parameters
        [.scalarReference s1,.scalarReference s2,.value e] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSet_long_long_applyExtremum.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e] =
        .finished (res,.scalar (if noop ≠ 0 then m else v)) ∧
      ScalarPost2 caller Sinit res (2 + e.nodes) 110 caller.scalars.memory := by
  refine R2V1_correct _ s64 s64 bl s64 rfl rfl (by rw [rsae_body]; exact selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 b1 b2 v noop e m c1 c2 hs ht value gm valid lengths strict base 1 (if noop ≠ 0 then m else v)
    (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v⟩ rfl (refVal caller s1 s64 b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 1 bl = some noop :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,noop⟩ rfl (refVal caller s2 bl b2 noop c2 _) rfl gn
  have e2 : penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 2 s64 = some m :=
    penv_ok _ 2 s64 ⟨(callerP caller).length+0,true⟩ ⟨s64,m⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,m⟩] 0) rfl gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable s64 2) (.variable s64 0) _ noop m v
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) (by rw [den_variable]; exact e0)
  refine ⟨r, by rw [rsae_body]; exact h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_P caller _⟩

theorem rangeset_applySumX_correct (caller : NState) (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v noop : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,noop⟩))
    (e1 e2 : NExpr) (x sz : Int) (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = s64)
    (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : s64.valid v = true) (gn : bl.valid noop = true) (gx : s64.valid x = true) (gz : i32.valid sz = true)
    (gm : s64.valid (v * sz) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSet_long_long_applySumX.parameters
        [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSet_long_long_applySumX.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.value e1,.value e2] =
        .finished (res,.scalar (if noop ≠ 0 then x else v * sz)) ∧
      ScalarPost2 caller Sinit res (2 + e1.nodes + e2.nodes) 110 caller.scalars.memory := by
  refine R2V2_correct _ s64 s64 bl s64 i32 rfl rfl
    (by rw [rsas_body]; exact selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 b1 b2 v noop e1 x e2 sz c1 c2 hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1
    (if noop ≠ 0 then x else v * sz) (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v⟩ rfl (refVal caller s1 s64 b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 1 bl = some noop :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,noop⟩ rfl (refVal caller s2 bl b2 noop c2 _) rfl gn
  have e2 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 2 s64 = some x :=
    penv_ok _ 2 s64 ⟨(callerP caller).length+0,true⟩ ⟨s64,x⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,x⟩,⟨i32,sz⟩] 0) rfl gx
  have e3 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 3 i32 = some sz :=
    penv_ok _ 3 i32 ⟨(callerP caller).length+1,true⟩ ⟨i32,sz⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,x⟩,⟨i32,sz⟩] 1) rfl gz
  have hb : (NExpr.binary s64 .mul (.variable s64 0) (.cast s64 (.variable i32 3))).denote
      (penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩) =
      some (v * sz) := by
    rw [den_binary, den_variable, den_cast, den_variable, e0, e3]
    simp only [Option.bind_some]
    rw [conv_signed s64 rfl rfl _ (s64_of_i32 _ gz)]
    simp only [Option.bind_some]
    exact convS _ gm
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable s64 2)
    (.binary s64 .mul (.variable s64 0) (.cast s64 (.variable i32 3))) _ noop x (v * sz)
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) hb
  refine ⟨r, by rw [rsas_body]; exact h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_P caller _⟩

theorem rangeset_compose_v_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 n1 v2 n2 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,n1⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v2⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,n2⟩))
    (g1 : s64.valid v1 = true) (g2 : bl.valid n1 = true) (g3 : s64.valid v2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSet_long_long_compose_v.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSet_long_long_compose_v.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if n1 ≠ 0 then v2 else v1)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs4t_correct _ s64 s64 bl s64 bl rfl rfl (by rw [rscv_body]; exact selRet_scalar _ _ _ rfl rfl rfl)
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 n1 v2 n2 c1 c2 c3 c4 valid lengths strict base 1
    (if n1 ≠ 0 then v2 else v1) (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v1⟩ rfl (P_cell_ty caller s1 s64 b1 v1 c1) rfl g1
  have e1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 1 bl = some n1 :=
    penv_ok _ 1 bl ⟨b2.address,false⟩ ⟨bl,n1⟩ rfl (P_cell_ty caller s2 bl b2 n1 c2) rfl g2
  have e2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ 2 s64 = some v2 :=
    penv_ok _ 2 s64 ⟨b3.address,false⟩ ⟨s64,v2⟩ rfl (P_cell_ty caller s3 s64 b3 v2 c3) rfl g3
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := selRet_exec (.variable bl 1) (.variable s64 2) (.variable s64 0) _ n1 v2 v1
    (by rw [den_variable]; exact e1) (by rw [den_variable]; exact e2) (by rw [den_variable]; exact e0)
  refine ⟨r, by rw [rscv_body]; exact h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_callerP caller⟩

theorem rangeset_compose_noop_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 n1 v2 n2 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,n1⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v2⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,n2⟩))
    (g2 : bl.valid n1 = true) (g4 : bl.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeSet_long_long_compose_noop.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeSet_long_long_compose_noop.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if n1 ≠ 0 then n2 else n1)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs4t_correct _ bl s64 bl s64 bl rfl rfl (by rw [rscn_body]; exact selRet_scalar _ _ _ rfl rfl rfl)
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
  refine ⟨r, by rw [rscn_body]; exact h1, h2, by simp [NExpr.nodes] at h3; omega, by simp [NExpr.nodes] at h4 ⊢; omega,
    by rw [h5]; exact take_callerP caller⟩

theorem rangeadd_compose_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hxy : s64.valid (x+y) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.compose_RangeAdd_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.MonoidLazyInstance.compose_RangeAdd_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x+y)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x+y) hxy 20 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2 (callerP caller) ba.address bb.address x y hxv hyv (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeA_exec (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] Proofs.GroupCall.addE (x+y) hxy
    (Proofs.GroupCall.addE_den _ x y e0 e1 hxy) (by decide)
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem rangeadd_new1_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeAdd_long_long_new1.parameters [] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeAdd_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ (.cast s64 (.literal i32 0)) 0 rfl rfl rfl (fun env => R0z env) rfl (by decide) rfl caller valid
    lengths strict base

theorem rangeadd_new0_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeAdd_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeAdd_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correct _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

abbrev raExtE : NExpr := .binary s64 .add (.variable s64 1) (.variable s64 0)
abbrev raSumE : NExpr :=
  .binary s64 .add (.variable s64 1) (.binary s64 .mul (.cast s64 (.variable i32 2)) (.variable s64 0))

theorem rae_body : Proofs.MonoidLazyInstance.RangeAdd_long_long_applyExtremum.body = .sequence (.primitive (.ret raExtE)) Sk := rfl
theorem ras_body : Proofs.MonoidLazyInstance.RangeAdd_long_long_applySumX.body = .sequence (.primitive (.ret raSumE)) Sk := rfl

theorem rangeadd_applyExtremum_correct (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v⟩)) (e : NExpr) (m : Int) (hs : e.scalarOnly = true)
    (ht : e.resultType = s64) (value : e.denote (envOf caller) = some m) (gv : s64.valid v = true)
    (gm : s64.valid m = true) (gs : s64.valid (m + v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeAdd_long_long_applyExtremum.parameters
        [.scalarReference s1,.value e] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeAdd_long_long_applyExtremum.callFuel fuel caller [.scalarReference s1,.value e] =
        .finished (res,.scalar (m + v)) ∧
      ScalarPost2 caller Sinit res (1 + e.nodes) 110 caller.scalars.memory := by
  refine R1V1_correct _ s64 s64 s64 rfl rfl (by rw [rae_body]; simp [Scalar, NExpr.scalarOnly])
    caller s1 b1 v e m c1 hs ht value gm valid lengths strict base 1 (m + v) gs 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v⟩ rfl (refVal caller s1 s64 b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ 1 s64 = some m :=
    penv_ok _ 1 s64 ⟨(callerP caller).length+0,true⟩ ⟨s64,m⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,m⟩] 0) rfl gm
  have den : raExtE.denote (penv ⟨callerP caller ++ [(⟨s64,m⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩) =
      some (m + v) := by
    rw [den_binary, den_variable, den_variable, e1, e0]
    simp only [Option.bind_some]
    exact convS _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen raExtE (m + v) _ den (by decide)
  refine ⟨r, by rw [rae_body]; exact h1, h2, by omega, by simp at h4 ⊢; omega, by rw [h5]; exact take_P caller _⟩

theorem rangeadd_applySumX_correct (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v⟩)) (e1 e2 : NExpr) (x sz : Int)
    (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = s64) (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : s64.valid v = true) (gx : s64.valid x = true) (gz : i32.valid sz = true)
    (gm : s64.valid (sz * v) = true) (gs : s64.valid (x + sz * v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidLazyInstance.RangeAdd_long_long_applySumX.parameters
        [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
      Proofs.MonoidLazyInstance.RangeAdd_long_long_applySumX.callFuel fuel caller [.scalarReference s1,.value e1,.value e2] =
        .finished (res,.scalar (x + sz * v)) ∧
      ScalarPost2 caller Sinit res (1 + e1.nodes + e2.nodes) 110 caller.scalars.memory := by
  refine R1V2_correct _ s64 s64 s64 i32 rfl rfl (by rw [ras_body]; simp [Scalar, NExpr.scalarOnly])
    caller s1 b1 v e1 x e2 sz c1 hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1 (x + sz * v) gs 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨b1.address,false⟩ ⟨s64,v⟩ rfl (refVal caller s1 s64 b1 v c1 _) rfl gv
  have e1 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 1 s64 = some x :=
    penv_ok _ 1 s64 ⟨(callerP caller).length+0,true⟩ ⟨s64,x⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,x⟩,⟨i32,sz⟩] 0) rfl gx
  have e2 : penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ 2 i32 = some sz :=
    penv_ok _ 2 i32 ⟨(callerP caller).length+1,true⟩ ⟨i32,sz⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,x⟩,⟨i32,sz⟩] 1) rfl gz
  have den : raSumE.denote (penv ⟨callerP caller ++ [(⟨s64,x⟩ : Cell),(⟨i32,sz⟩ : Cell)],[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩) =
      some (x + sz * v) := by
    rw [den_binary, den_variable, den_binary, den_cast, den_variable, den_variable, e1, e2, e0]
    simp only [Option.bind_some]
    rw [conv_signed s64 rfl rfl _ (s64_of_i32 _ gz)]
    simp only [Option.bind_some]
    have m1 : binaryValue .mul sz v = sz * v := rfl
    rw [m1, convS _ gm]
    simp only [Option.bind_some]
    have m2 : binaryValue .add x (sz * v) = x + sz * v := rfl
    rw [m2]; exact convS _ gs
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := ret_exec_gen raSumE (x + sz * v) _ den (by decide)
  refine ⟨r, by rw [ras_body]; exact h1, h2, by omega, by simp at h4 ⊢; omega, by rw [h5]; exact take_P caller _⟩

end Proofs.MonoidLazyCall
