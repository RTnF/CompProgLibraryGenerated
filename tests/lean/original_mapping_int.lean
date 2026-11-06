namespace OriginalMappingIntAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall
open Proofs.CppState (Cell)

theorem prep_rrv_typed (caller : NState) (params : List CppVectorBindings.Parameter) (valueTy : Ty)
    (hp : params = [.scalar s64 true false,.scalar s64 true false,.scalar valueTy false true])
    (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v1 v2 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (e : NExpr) (n : Int) (hs : e.scalarOnly = true) (hty : e.resultType = valueTy)
    (value : e.denote (envOf caller) = some n) (valid : caller.frame.state.wellFormed = true)
    (nv : valueTy.valid n = true) :
    ∃ t, Good ((caller.charge 1 1).charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨valueTy,n⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have core2 : Core caller ((caller.charge 1 1).charge 1 1) := (core_charge caller 1 1).trans (core_charge _ 1 1)
  obtain ⟨t,ran,good⟩ := scalar_eval e ((caller.charge 1 1).charge 1 1) n hs (by rw [envOf_core core2]; exact value)
  refine ⟨t,good,?_⟩
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
  have c2' : (caller.charge 1 1).scalarCell s2 s64 = some (b2,⟨s64,v2⟩) := c2
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨s64,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨s64,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have res3 : resolve ((caller.charge 1 1).charge 1 1) (.scalar valueTy false true) (.value e) = some (t,.scalar valueTy true n) := by
    simp [resolve,hty,ran]
  have res1 : resolve caller (.scalar s64 true false) (.scalarReference s1) =
      some (caller.charge 1 1,.scalarAddress s64 b1.address false) := by simp [resolve,c1]
  have res2 : resolve (caller.charge 1 1) (.scalar s64 true false) (.scalarReference s2) =
      some ((caller.charge 1 1).charge 1 1,.scalarAddress s64 b2.address false) := by simp [resolve,c2']
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,res3]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g := good.2.2.2.2.1
  simp only [charge_scalar_peak] at g ⊢
  exact Nat.le_trans (by omega) (Nat.le_max_left _ _)

abbrev applyIntExpr : NExpr := .targetCast i32
  (.binary s64 .add (.binary s64 .mul (.variable s64 0) (.cast s64 (.variable i32 2))) (.variable s64 1))

theorem widen_input (x : Int) (h : i32.valid x = true) : s64.valid x = true := by
  have small : -(2147483648 : Int) ≤ x ∧ x < 2147483648 := by simpa [Ty.valid,i32] using h
  change decide (-(9223372036854775808 : Int) ≤ x ∧ x < 9223372036854775808) = true
  simp only [decide_eq_true_eq]
  omega

theorem apply_int_den (env : Nat → Ty → Option Int) (a b x : Int)
    (ha : env 0 s64 = some a) (hb : env 1 s64 = some b) (hx : env 2 i32 = some x)
    (hxv : i32.valid x = true) (hm : s64.valid (a*x) = true) (hsum : s64.valid (a*x+b) = true) :
    applyIntExpr.denote env = some (signedDecode 32 (a*x+b)) := by
  have castx : (NExpr.cast s64 (.variable i32 2)).denote env = some x := by
    simp only [NExpr.denote,hx,Option.bind_some]
    exact convS _ (widen_input x hxv)
  have inner : (NExpr.binary s64 .add (.binary s64 .mul (.variable s64 0)
      (.cast s64 (.variable i32 2))) (.variable s64 1)).denote env = some (a*x+b) := by
    rw [den_binary,den_binary,den_variable,ha,castx]
    simp only [Option.bind_some,binaryValue]
    rw [convS _ hm]
    simp only [Option.bind_some,den_variable,hb]
    exact convS _ hsum
  change ((NExpr.binary s64 .add (.binary s64 .mul (.variable s64 0)
    (.cast s64 (.variable i32 2))) (.variable s64 1)).denote env).bind
    (fun value => i32.targetConvert value) = _
  rw [inner]
  exact (Proofs.CppTargetCast.targetConvert_i32_valid (a*x+b)).1

theorem apply_int_body : Original_mapping.Affine_long_long_apply__template_int.body =
    .sequence (.primitive (.ret applyIntExpr)) Sk := rfl

theorem apply_int_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (a b x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,a⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,b⟩))
    (hav : s64.valid a = true) (hbv : s64.valid b = true) (hxv : i32.valid x = true)
    (hm : s64.valid (a*x) = true) (hsum : s64.valid (a*x+b) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Original_mapping.Affine_long_long_apply__template_int.parameters
        [.scalarReference sa,.scalarReference sb,.value (.literal i32 x)] = some Sinit ∧
      Original_mapping.Affine_long_long_apply__template_int.callFuel fuel caller
        [.scalarReference sa,.scalarReference sb,.value (.literal i32 x)] = .finished (res,.scalar (signedDecode 32 (a*x+b))) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrv_typed caller _ i32 rfl sa sb ba bb a b ca cb (.literal i32 x) x rfl rfl
      (by simp [NExpr.denote,hxv]) valid hxv
  let P := callerP caller ++ [⟨i32,x⟩]
  let refs : List CppState.Binding := [⟨ba.address,false⟩,⟨bb.address,false⟩,⟨(callerP caller).length,true⟩]
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length)+1 := by simp [P,callerP]; omega
  have plen : P.length = (callerP caller).length+1 := by simp [P]
  have gw := good.2.2.1
  simp only [charge_work,NExpr.nodes] at gw
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  have hPa := P_cell caller sa ba a ca
  have hPb := P_cell caller sb bb b cb
  have hPa' : P[ba.address]? = some ⟨s64,a⟩ := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hPa).1];exact hPa
  have hPb' : P[bb.address]? = some ⟨s64,b⟩ := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hPb).1];exact hPb
  have hPx : P[(callerP caller).length]? = some ⟨i32,x⟩ := by simp [P]
  have e0 : penv ⟨P,refs⟩ 0 s64 = some a := penv_ok _ 0 s64 ⟨ba.address,false⟩ ⟨s64,a⟩ rfl hPa' rfl hav
  have e1 : penv ⟨P,refs⟩ 1 s64 = some b := penv_ok _ 1 s64 ⟨bb.address,false⟩ ⟨s64,b⟩ rfl hPb' rfl hbv
  have e2 : penv ⟨P,refs⟩ 2 i32 = some x := penv_ok _ 2 i32 ⟨(callerP caller).length,true⟩ ⟨i32,x⟩ rfl hPx rfl hxv
  have result_valid := (Proofs.CppTargetCast.targetConvert_i32_valid (a*x+b)).2
  have q := exec_ret 1 ⟨P,refs⟩ applyIntExpr (signedDecode 32 (a*x+b)) (apply_int_den _ a b x e0 e1 e2 hxv hm hsum)
  have hexec : pexec 1 Original_mapping.Affine_long_long_apply__template_int.body ⟨P,refs⟩ =
      some ⟨⟨P,refs⟩,some (signedDecode 32 (a*x+b)),applyIntExpr.nodes+1,P.length+3+applyIntExpr.nodes+2⟩ := by
    rw [apply_int_body];simpa [refs] using q
  have hpost := call_scalar caller Original_mapping.Affine_long_long_apply__template_int
    [.scalarReference sa,.scalarReference sb,.value (.literal i32 x)] Sinit P refs
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame sPeak (by omega) (by rw [takeM]) valid lengths
    strict base (by rw [apply_int_body];simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl i32 rfl result_valid
    (by simp [NExpr.nodes];omega) (by simp [refs];omega) 0 80
    (by simp only [applyIntExpr,NExpr.nodes] at *;omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post
end OriginalMappingIntAudit
