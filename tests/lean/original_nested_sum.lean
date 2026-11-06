namespace NestedSumAudit
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


theorem prepare_values2t (ty1 ty2 : Ty) (caller : NState) (params : List Proofs.CppVectorBindings.Parameter)
    (hp : params = [.scalar ty1 false true, .scalar ty2 false true]) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = ty1) (t2ty : e2.resultType = ty2)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : ty1.valid v1 = true) (n2 : ty2.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller params [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨ty1,v1⟩,⟨ty2,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a,b]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a,b]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a,b]
  have res1 : resolve caller (.scalar ty1 false true) (.value e1) = some (t1,.scalar ty1 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar ty2 false true) (.value e2) = some (t2,.scalar ty2 true v2) := by
    simp [resolve,t2ty,ran2]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  omega

theorem value2t_correct (prog : NProgram) (second : Bool)
    (hp : prog.parameters = [.scalar s64 false true,.scalar i32 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable (if second then i32 else s64) (if second then 1 else 0)))) Sk)
    (hr : prog.result = ResultKind.scalar (if second then i32 else s64)) (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : i32.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (if second then y else x)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_values2t s64 i32 caller _ hp e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 valid hx hy
  let P := callerP caller
  let M := P ++ [(⟨s64,x⟩ : Cell),⟨i32,y⟩]
  let bs : List CppState.Binding := [⟨P.length,true⟩,⟨P.length+1,true⟩]
  have ev : penv ⟨M,bs⟩ (if second then 1 else 0) (if second then i32 else s64) = some (if second then y else x) := by
    cases second
    · exact penv_ok _ 0 s64 ⟨P.length,true⟩ ⟨s64,x⟩ rfl
        (by simp [M,P]) rfl hx
    · exact penv_ok _ 1 i32 ⟨P.length+1,true⟩ ⟨i32,y⟩ rfl
        (by simp [M,P]) rfl hy
  have takeM : M.take caller.scalars.memory.length = caller.scalars.memory := Proofs.MonoidCallCore.take_P caller _
  have q := exec_ret 1 (⟨M,bs⟩ : PS) (.variable (if second then i32 else s64) (if second then 1 else 0)) (if second then y else x)
    (by rw [den_variable]; exact ev)
  rw [← hb] at q
  have hexec := q
  have peak1 := g1.2.2.2.2.1
  have peak2 := g2.2.2.2.2.1
  have work1 := g1.2.2.1
  have work2 := g2.2.2.1
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [P,callerP]
  have hpost := call_scalar caller prog [.value e1,.value e2] Sinit M bs
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [M]; omega) (by rw [takeM]) valid lengths strict base
    (by rw [hb]; simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl (if second then i32 else s64) hr
    (by cases second <;> assumption) (by simp [M,bs,P,NExpr.nodes]) (by simp [M,bs,P])
    (e1.nodes+e2.nodes) 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [takeM] using post⟩

theorem const_t_correct (ty : Ty) (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar ty)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : ty.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have q := exec_ret 1 ⟨callerP caller,[]⟩ e v (he _)
  have hexec : pexec 1 prog.body ⟨callerP caller,[]⟩ = some ⟨⟨callerP caller,[]⟩,some v,e.nodes+1,
      (callerP caller).length+0+e.nodes+2⟩ := by rw [hb]; simpa using q
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by rw [hb]; simp [Scalar, hs]) 1 _ hexec _ rfl ty hr hv
    (by simp; omega) (by simp) 0 70 (by simp; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post


theorem e_x_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_e_x.parameters [] = some Sinit ∧
      OriginalNestedSum.RangeSum_e_x.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_t_correct s64 _ (.cast s64 (.literal i32 0)) 0 rfl rfl rfl
    (by intro env; rfl) (by decide) (by decide) (by decide)
    caller valid lengths strict base

theorem e_size_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_e_size.parameters [] = some Sinit ∧
      OriginalNestedSum.RangeSum_e_size.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_t_correct i32 _ (.literal i32 0) 0 rfl rfl rfl
    (by intro env; rfl) (by decide) (by decide) (by decide)
    caller valid lengths strict base

theorem new1_x_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_new1_x.parameters [] = some Sinit ∧
      OriginalNestedSum.RangeSum_new1_x.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_t_correct s64 _ (.cast s64 (.literal i32 0)) 0 rfl rfl rfl
    (by intro env; rfl) (by decide) (by decide) (by decide)
    caller valid lengths strict base

theorem new1_size_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_new1_size.parameters [] = some Sinit ∧
      OriginalNestedSum.RangeSum_new1_size.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_t_correct i32 _ (.literal i32 0) 0 rfl rfl rfl
    (by intro env; rfl) (by decide) (by decide) (by decide)
    caller valid lengths strict base

theorem new_x_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : i32.valid y = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_new0_x.parameters [.value e1,.value e2] = some Sinit ∧
      OriginalNestedSum.RangeSum_new0_x.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2t_correct _ false rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem new_size_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : i32.valid y = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_new0_size.parameters [.value e1,.value e2] = some Sinit ∧
      OriginalNestedSum.RangeSum_new0_size.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar y) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2t_correct _ true rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem op_x_program : OriginalNestedSum.RangeSum_op_x = Proofs.MonoidLazyInstance.RangeSum_long_long_op_x := rfl
theorem op_x_call (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalNestedSum.RangeSum_op_x.callFuel fuel caller args = Proofs.MonoidLazyInstance.RangeSum_long_long_op_x.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) op_x_program

theorem op_x_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : s64.valid v1 = true) (g3 : s64.valid v3 = true) (gs : s64.valid (v1 + v3) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_op_x.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      OriginalNestedSum.RangeSum_op_x.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v1 + v3)) ∧
      ScalarPost2 caller Sinit res 0 72 caller.scalars.memory := by
  simpa only [op_x_program] using Proofs.MonoidLazyCall.rangesum_op_x_correct
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 g1 g3 gs valid lengths strict base

theorem op_size_program : OriginalNestedSum.RangeSum_op_size = Proofs.MonoidLazyInstance.RangeSum_long_long_op_size := rfl
theorem op_size_call (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalNestedSum.RangeSum_op_size.callFuel fuel caller args = Proofs.MonoidLazyInstance.RangeSum_long_long_op_size.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) op_size_program

theorem op_size_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g2 : i32.valid v2 = true) (g4 : i32.valid v4 = true) (gs : i32.valid (v2 + v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalNestedSum.RangeSum_op_size.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      OriginalNestedSum.RangeSum_op_size.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v2 + v4)) ∧
      ScalarPost2 caller Sinit res 0 72 caller.scalars.memory := by
  simpa only [op_size_program] using Proofs.MonoidLazyCall.rangesum_op_size_correct
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 g2 g4 gs valid lengths strict base

end NestedSumAudit
