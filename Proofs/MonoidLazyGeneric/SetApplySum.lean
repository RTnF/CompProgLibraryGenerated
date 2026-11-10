import Proofs.CppClassCopyCommands
import Proofs.CppConstructorMultiFinish
import Proofs.CppConstructorView
import Proofs.CppFrameResolveExtension
import Proofs.CppNestedCall
import Proofs.MemberSupport
import Proofs.GenericLazy
import Proofs.MonoidLazyCall
import Proofs.CppScalarValuePrepare
import Proofs.CppScalarContents
import Proofs.GenericExtrema
import Proofs.GenericCall
import Proofs.MonoidLazyGeneric.CopyFields
open Proofs.CppScalar
namespace GenericSetApplyAudit
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


open Proofs.MonoidLazyCall Proofs.MonoidCall

open CopiedScalarFieldsAudit
variable (ty : Ty)

def argMem (Q : List Cell) (x sz : Int) : List Cell := Q ++ [⟨ty,x⟩,⟨i32,sz⟩]
def applyRefs (Q : List Cell) (av an : Nat) : List CppState.Binding :=
  [⟨av,true⟩,⟨an,true⟩,⟨Q.length,true⟩,⟨Q.length+1,true⟩]
def condition : NExpr := .unary bl .not (.variable bl 1)
def product : NExpr := .binary ty .mul (.variable ty 0) (Proofs.GenericLazy.castTo ty i32 (.variable i32 3))
def updateBranch : Command := .branch condition
  (.sequence (.scope (.sequence (.primitive (.assign 2 ty (product ty))) Sk)) Sk) Sk
def applyBody (second : Bool) : Command :=
  .sequence (updateBranch ty) (copyBody 4 ty i32 (.variable ty 2) (.variable i32 3) second)

def gSetApply (second : Bool) : NProgram :=
  ⟨[.scalar ty true true,.scalar bl true true,.scalar ty false true,.scalar i32 false true],
    .scalar (if second then i32 else ty), applyBody ty second⟩
theorem apply_body (second : Bool) : (gSetApply ty second).body = applyBody ty second := rfl

theorem update_exec (Q : List Cell) (av an : Nat) (v n x sz : Int)
    (cv : Q[av]? = some ⟨ty,v⟩) (cn : Q[an]? = some ⟨bl,n⟩)
    (hv : ty.valid v = true) (hn : bl.valid n = true)
    (hx : ty.valid x = true) (hz : i32.valid sz = true) (hzt : ty.valid sz = true)
    (q : Int) (hcm : n = 0 → ty.convert (v*sz) = some q) :
    ∃ r, pexec 1 (updateBranch ty) ⟨argMem ty Q x sz,applyRefs Q av an⟩ = some r ∧
      r.ret = none ∧ r.cost ≤ 12 ∧ r.need ≤ Q.length+30 ∧
      r.ps = ⟨argMem ty Q (if n = 0 then q else x) sz,applyRefs Q av an⟩ := by
  let M := argMem ty Q x sz
  let R := applyRefs Q av an
  have cv' : M[av]? = some ⟨ty,v⟩ := by
    dsimp [M,argMem]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp cv).1]; exact cv
  have cn' : M[an]? = some ⟨bl,n⟩ := by
    dsimp [M,argMem]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp cn).1]; exact cn
  have ev : penv (⟨M,R⟩ : PS) 0 ty = some v := by
    simpa only [ws_nil] using ws_env_ref M R [] 0 av true ty v rfl cv' hv
  have en : penv (⟨M,R⟩ : PS) 1 bl = some n := by
    simpa only [ws_nil] using ws_env_ref M R [] 1 an true bl n rfl cn' hn
  have ez : penv (⟨M,R⟩ : PS) 3 i32 = some sz := by
    simpa only [ws_nil] using ws_env_ref M R [] 3 (Q.length+1) true i32 sz rfl (by simp [M,argMem]) hz
  by_cases zero : n = 0
  · have dc : condition.denote (penv (⟨M,R⟩ : PS)) = some 1 := by
      simp [condition,NExpr.denote,en,unaryValue,zero]
    have dm : (product ty).denote (penv (⟨M,R⟩ : PS)) = some (q) := by
      unfold product
      rw [den_binary,den_variable,Proofs.GenericLazy.castTo_den ty i32 (.variable i32 3) _ sz (by rw [den_variable]; exact ez) hzt,ev]
      simp only [Option.bind_some]
      exact hcm zero
    have st := pstmt_assign_ok (⟨M,R⟩ : PS) 2 ty (product ty) (q) dm
      ⟨Q.length,true⟩ ⟨ty,x⟩ rfl (by simp [M,argMem]) rfl hx rfl (q)
      (Proofs.GenericCall.convG ty q (Proofs.GenericCall.convert_valid ty _ _ (hcm zero)))
    have braced := pexec_braced 1 (.assign 2 ty (product ty)) (⟨M,R⟩ : PS) _ st rfl
      (by simp) rfl
    have br := pexec_branch_true 1 condition _ Sk (⟨M,R⟩ : PS) 1 dc (by decide) _ braced
    have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.variable i32 3)
    simp only [NExpr.nodes] at hn
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [product,condition,NExpr.nodes] <;> omega
    · simp [M,R,argMem,applyRefs,product,condition,NExpr.nodes] <;> omega
    · simp [M,R,argMem,zero]
  · have dc : condition.denote (penv (⟨M,R⟩ : PS)) = some 0 := by
      simp [condition,NExpr.denote,en,unaryValue,zero]
    have br := pexec_branch_false 1 condition
      (.sequence (.scope (.sequence (.primitive (.assign 2 ty (product ty))) Sk)) Sk) Sk (⟨M,R⟩ : PS) dc _ (pexec_skip 1 _)
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [condition,NExpr.nodes]
    · simp [M,R,argMem,applyRefs,condition,NExpr.nodes]
    · simp [M,R,zero]

theorem apply_exec (Q : List Cell) (av an : Nat) (v n x sz : Int) (second : Bool)
    (cv : Q[av]? = some ⟨ty,v⟩) (cn : Q[an]? = some ⟨bl,n⟩)
    (hv : ty.valid v = true) (hn : bl.valid n = true)
    (hx : ty.valid x = true) (hz : i32.valid sz = true) (hzt : ty.valid sz = true)
    (q : Int) (hcm : n = 0 → ty.convert (v*sz) = some q) :
    let w := if n = 0 then q else x
    ∃ r, pexec 1 (gSetApply ty second).body
        ⟨argMem ty Q x sz,applyRefs Q av an⟩ = some r ∧
      r.ret = some (if second then sz else w) ∧ r.cost ≤ 30 ∧ r.need ≤ Q.length+50 ∧
      r.ps.mem = argMem ty Q w sz ++ [⟨ty,w⟩,⟨i32,sz⟩] := by
  let w := if n = 0 then q else x
  let M := argMem ty Q w sz
  let R := applyRefs Q av an
  have hw : ty.valid w = true := by dsimp [w]; split <;> first | exact Proofs.GenericCall.convert_valid ty _ _ (hcm (by assumption)) | exact hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := update_exec ty Q av an v n x sz cv cn hv hn hx hz hzt q hcm
  have dx : (NExpr.variable ty 2).denote (penv (ws M R [])) = some w := by
    rw [den_variable]; exact ws_env_ref M R [] 2 Q.length true ty w rfl (by simp [M,argMem]) hw
  have dz : (NExpr.variable i32 3).denote (penv (ws M R [⟨ty,w⟩])) = some sz := by
    rw [den_variable]; exact ws_env_ref M R _ 3 (Q.length+1) true i32 sz rfl (by simp [M,argMem]) hz
  obtain ⟨c,crun,cret,ccost,cneed,cps⟩ := copy_exec M R ty i32 (.variable ty 2) (.variable i32 3) w sz second hw hz dx dz
  have tail : pexec 1 (copyBody 4 ty i32 (.variable ty 2) (.variable i32 3) second) r.ps = some c := by
    rw [ps]; simpa [R,applyRefs,ws_nil] using crun
  refine ⟨⟨c.ps,c.ret,r.cost+c.cost,max r.need c.need⟩,?_,cret,?_,?_,?_⟩
  · rw [apply_body ty]; exact seq_some ran ret tail
  · change r.cost+c.cost ≤ 30
    simp [NExpr.nodes] at ccost
    omega
  · change max r.need c.need ≤ Q.length+50
    simp [M,R,argMem,applyRefs,NExpr.nodes] at cneed
    omega
  · change c.ps.mem = _
    rw [cps]; rfl

end GenericSetApplyAudit
namespace GenericSetApplyPrepareAudit
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

theorem prep_RW2V2 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (u2 : Ty) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (hp : params = [.scalar t1 true true,.scalar t2 true true,.scalar u1 false true,.scalar u2 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (wb1 : b1.writable = true) (wb2 : b2.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 2 + e1.nodes+e2.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩,⟨u2,n2⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1))
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨q2,ran2,good2⟩ := scalar_eval e2 q1 n2 hs2 (by rw [envOf_core core1]; exact value2)
  have core2 : Core caller q2 := core1.trans good2.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core2
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have fs : q2.frame.state = caller.frame.state := by rw [cf]
  have fr : q2.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q2.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have res1 : resolve caller (.scalar t1 true true) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address true) := by simp [resolve,c1,wb1]
  have res2 : resolve (caller.charge 1 1) (.scalar t2 true true) (.scalarReference s2) =
      some (((caller.charge 1 1).charge 1 1),.scalarAddress t2 b2.address true) := by simp [resolve,c2',wb2]
  have resv1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  have resv2 : resolve q1 (.scalar u2 false true) (.value e2) = some (q2,.scalar u2 true n2) := by
    simp [resolve,hty2,ran2]
  refine ⟨q2,?_,?_⟩
  · have g1 := good1.2.2.1
    have g2 := good2.2.2.1
    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,resv1,resv2]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,nv2,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g1 := good1.2.2.2.2.1
  have g2 := good2.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 g2 ⊢
  omega

theorem RW2V2_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (u2 : Ty)
    (hp : prog.parameters = [.scalar t1 true true,.scalar t2 true true,.scalar u1 false true,.scalar u2 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (wb1 : b1.writable = true) (wb2 : b2.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (2+e1.nodes+e2.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_RW2V2 caller _ t1 t2 u1 u2 s1 s2 b1 b2 v1 v2 e1 n1 e2 n2 hp c1 c2 wb1 wb2 hs1 hty1 value1 nv1 hs2 hty2 value2 nv2 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) [⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (2+e1.nodes+e2.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

end GenericSetApplyPrepareAudit
namespace GenericSetApplyCallerAudit
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


open Proofs.MonoidLazyCall Proofs.MonoidCall

open CopiedScalarFieldsAudit

open GenericSetApplyAudit GenericSetApplyPrepareAudit
variable (ty : Ty)

theorem apply_correct (second : Bool) (caller : NState)
    (sv sn : Nat) (bv bn : CppState.Binding) (v n x sz : Int)
    (cv : caller.scalarCell sv ty = some (bv,⟨ty,v⟩))
    (cn : caller.scalarCell sn bl = some (bn,⟨bl,n⟩))
    (wv : bv.writable = true) (wn : bn.writable = true)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = ty)
    (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : ty.valid v = true) (gn : bl.valid n = true)
    (gx : ty.valid x = true) (gz : i32.valid sz = true) (gzt : ty.valid sz = true)
    (q : Int) (hcm : n = 0 → ty.convert (v*sz) = some q)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gSetApply ty second
    let w := if n = 0 then q else x
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference sv,.scalarReference sn,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sv,.scalarReference sn,.value e1,.value e2] =
        .finished (res,.scalar (if second then sz else w)) ∧
      ScalarPost2 caller Sinit res (2+e1.nodes+e2.nodes) 110 caller.scalars.memory := by
  let prog := gSetApply ty second
  let w := if n = 0 then q else x
  have gw : ty.valid w = true := by dsimp [w]; split <;> first | exact Proofs.GenericCall.convert_valid ty _ _ (hcm (by assumption)) | exact gx
  refine RW2V2_correct prog (if second then i32 else ty) ty bl ty i32
    (by cases second <;> rfl) (by cases second <;> rfl)
    (by show Scalar (applyBody ty second) = true; have h := Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 3) rfl; cases second <;> simp [applyBody, updateBranch, condition, product, copyBody, copyPicked, Scalar, NExpr.scalarOnly, h]) caller sv sn bv bn v n e1 x e2 sz cv cn wv wn
    hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1 (if second then sz else w)
    (by cases second <;> assumption) 30 ?_
  intro P hP
  subst hP
  have cv' : (callerP caller)[bv.address]? = some ⟨ty,v⟩ :=
    Proofs.IntervalCall.P_cell_ty caller sv ty bv v cv
  have cn' : (callerP caller)[bn.address]? = some ⟨bl,n⟩ :=
    Proofs.IntervalCall.P_cell_ty caller sn bl bn n cn
  obtain ⟨r,ran,ret,cost,need,mem⟩ := apply_exec ty (callerP caller) bv.address bn.address v n x sz second
    cv' cn' gv gn gx gz gzt q hcm
  refine ⟨r,?_,ret,cost,?_,?_⟩
  · simpa [prog,argMem,applyRefs] using ran
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · rw [mem]
    simpa only [argMem,List.append_assoc] using Proofs.MonoidCallCore.take_P caller
      ([⟨ty,w⟩,⟨i32,sz⟩]++[⟨ty,w⟩,⟨i32,sz⟩])

end GenericSetApplyCallerAudit

