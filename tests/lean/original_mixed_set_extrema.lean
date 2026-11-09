namespace SetExtremaPrepareAudit
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

theorem prep_RW2V1 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int)
    (hp : params = [.scalar t1 true true,.scalar t2 true true,.scalar u1 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (wb1 : b1.writable = true) (wb2 : b2.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 2 + e1.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1))
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core1
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have fs : q1.frame.state = caller.frame.state := by rw [cf]
  have fr : q1.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q1.frame.bindings = caller.frame.bindings := by rw [cf]
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
  refine ⟨q1,?_,?_⟩
  · have g1 := good1.2.2.1

    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,resv1]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g1 := good1.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 ⊢
  omega

theorem RW2V1_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (u1 : Ty)
    (hp : prog.parameters = [.scalar t1 true true,.scalar t2 true true,.scalar u1 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (wb1 : b1.writable = true) (wb2 : b2.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.value e1] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e1] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (2+e1.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_RW2V1 caller _ t1 t2 u1 s1 s2 b1 b2 v1 v2 e1 n1 hp c1 c2 wb1 wb2 hs1 hty1 value1 nv1 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.value e1] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) [⟨b1.address,true⟩,⟨b2.address,true⟩,⟨(callerP caller).length+0,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (2+e1.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

end SetExtremaPrepareAudit
namespace SetExtremaApplyAudit
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


abbrev applyMax := OriginalSetExtrema.RangeSet_apply__template_RangeSetRangeMaxMin_long_long___RangeMax
abbrev applyMin := OriginalSetExtrema.RangeSet_apply__template_RangeSetRangeMaxMin_long_long___RangeMin

theorem apply_same : applyMax = applyMin := rfl

def yesBody : Command := .sequence (.scope (.sequence (.primitive (.assign 3 s64 (.variable s64 2))) Sk)) Sk
def noBody : Command := .sequence (.scope
  (.sequence (.primitive (.declare s64 true (.variable s64 0)))
    (.sequence (.primitive (.declare s64 true (.variable s64 4)))
      (.sequence (.primitive (.assign 3 s64 (.variable s64 5))) Sk)))) Sk

theorem ws_assign_first (P : List Cell) (R : List CppState.Binding) (L : List Cell)
    (e : NExpr) (v : Int) (hv : s64.valid v = true)
    (de : e.denote (penv (ws P R (⟨s64,0⟩::L))) = some v) :
    pstmt (.assign R.length s64 e) (ws P R (⟨s64,0⟩::L)) =
      some ⟨ws P R (⟨s64,v⟩::L),none,e.nodes+1,
        P.length+R.length+2*(L.length+1)+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (ws P R (⟨s64,0⟩::L)) R.length s64 e v de
    ⟨P.length,true⟩ ⟨s64,0⟩ (by simp [ws]) (by simp [ws]) rfl rfl rfl v (Ty.convert_of_valid s64 v hv)
  have mem : (ws P R (⟨s64,0⟩::L)).mem.set P.length ⟨s64,v⟩ =
      (ws P R (⟨s64,v⟩::L)).mem := by simp [ws]
  have need : (ws P R (⟨s64,0⟩::L)).mem.length + (ws P R (⟨s64,0⟩::L)).bs.length + e.nodes + 2 =
      P.length+R.length+2*(L.length+1)+e.nodes+2 := by simp [ws]; omega
  rw [h,mem,need]
  rfl

theorem branch_exec (P : List Cell) (av an ax : Nat) (v n x : Int)
    (cv : P[av]? = some ⟨s64,v⟩) (cn : P[an]? = some ⟨bl,n⟩)
    (cx : P[ax]? = some ⟨s64,x⟩)
    (hv : s64.valid v = true) (hn : bl.valid n = true) (hx : s64.valid x = true) :
    let R : List CppState.Binding := [⟨av,true⟩,⟨an,true⟩,⟨ax,true⟩]
    ∃ r, pexec 1 (.branch (.variable bl 1) yesBody noBody) (ws P R [⟨s64,0⟩]) = some r ∧
      r.ret = none ∧ r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧
      r.ps = ws P R [⟨s64,if n ≠ 0 then x else v⟩] := by
  let R : List CppState.Binding := [⟨av,true⟩,⟨an,true⟩,⟨ax,true⟩]
  have cond : (NExpr.variable bl 1).denote (penv (ws P R [⟨s64,0⟩])) = some n := by
    rw [den_variable]; exact ws_env_ref P R _ 1 an true bl n rfl cn hn
  by_cases zero : n = 0
  · have dv : (NExpr.variable s64 0).denote (penv (ws P R [⟨s64,0⟩])) = some v := by
      rw [den_variable]; exact ws_env_ref P R _ 0 av true s64 v rfl cv hv
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [⟨s64,0⟩] s64 (.variable s64 0) v dv (Ty.convert_of_valid s64 v hv))
    have dv2 : (NExpr.variable s64 4).denote (penv (ws P R [⟨s64,0⟩,⟨s64,v⟩])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 1 ⟨s64,v⟩ s64 rfl rfl hv
    have q2 := (pexec_prim 1 _ _).trans (ws_declare P R [⟨s64,0⟩,⟨s64,v⟩] s64 (.variable s64 4) v dv2 (Ty.convert_of_valid s64 v hv))
    have dv3 : (NExpr.variable s64 5).denote (penv (ws P R [⟨s64,0⟩,⟨s64,v⟩,⟨s64,v⟩])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 2 ⟨s64,v⟩ s64 rfl rfl hv
    have q3 := (pexec_prim 1 _ _).trans (ws_assign_first P R [⟨s64,v⟩,⟨s64,v⟩] (.variable s64 5) v hv dv3)
    have body := seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (pexec_skip 1 _)))
    have scope := pexec_scope 1 _ (ws P R [⟨s64,0⟩]) _ body
    have clean : pexec 1 noBody (ws P R [⟨s64,0⟩]) =
        some ⟨ws P R [⟨s64,v⟩],none,7,P.length+12⟩ := by
      have whole := seq_some scope rfl (pexec_skip 1 _)
      simpa [noBody,ws,R,NExpr.nodes,List.take_append,List.range_succ,List.take_of_length_le,Nat.add_assoc] using whole
    have br := pexec_branch_false 1 (.variable bl 1) yesBody noBody (ws P R [⟨s64,0⟩])
      (by simpa [zero] using cond) _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [ws,R,NExpr.nodes]
    · simp [zero,R]
  · have dx : (NExpr.variable s64 2).denote (penv (ws P R [⟨s64,0⟩])) = some x := by
      rw [den_variable]; exact ws_env_ref P R _ 2 ax true s64 x rfl cx hx
    have st := ws_assign_first P R [] (.variable s64 2) x hx dx
    have b := pexec_braced 1 (.assign 3 s64 (.variable s64 2)) (ws P R [⟨s64,0⟩]) _ st rfl
      (by simp [ws]) (by simp [ws])
    have clean : pexec 1 yesBody (ws P R [⟨s64,0⟩]) =
        some ⟨ws P R [⟨s64,x⟩],none,3,P.length+8⟩ := by
      simpa [yesBody,ws,R,NExpr.nodes] using b
    have br := pexec_branch_true 1 (.variable bl 1) yesBody noBody (ws P R [⟨s64,0⟩]) n cond zero _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [ws,R,NExpr.nodes]
    · simp [zero,R]

theorem apply_exec (P : List Cell) (av an ax : Nat) (v n x : Int)
    (cv : P[av]? = some ⟨s64,v⟩) (cn : P[an]? = some ⟨bl,n⟩)
    (cx : P[ax]? = some ⟨s64,x⟩)
    (hv : s64.valid v = true) (hn : bl.valid n = true) (hx : s64.valid x = true) :
    let R : List CppState.Binding := [⟨av,true⟩,⟨an,true⟩,⟨ax,true⟩]
    ∃ r, pexec 1 applyMax.body (ws P R []) = some r ∧
      r.ret = some (if n ≠ 0 then x else v) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+50 ∧
      r.ps.mem = P ++ [⟨s64,if n ≠ 0 then x else v⟩] := by
  let R : List CppState.Binding := [⟨av,true⟩,⟨an,true⟩,⟨ax,true⟩]
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [] s64 (.literal s64 0) 0 rfl rfl)
  obtain ⟨r,ran,ret,cost,need,ps⟩ := branch_exec P av an ax v n x cv cn cx hv hn hx
  have val : s64.valid (if n ≠ 0 then x else v) = true := by split <;> assumption
  have dr : (NExpr.variable s64 3).denote (penv r.ps) = some (if n ≠ 0 then x else v) := by
    rw [ps,den_variable]; exact ws_env_loc P R _ 0 ⟨s64,if n ≠ 0 then x else v⟩ s64 rfl rfl val
  have qr := exec_ret 1 r.ps (.variable s64 3) _ dr
  have whole := seq_some q0 rfl (seq_some ran ret qr)
  refine ⟨_,whole,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]; omega
  · change max (P.length+R.length+1+4) (max r.need (r.ps.mem.length+r.ps.bs.length+1+2)) ≤ P.length+50
    rw [ps]
    simp [ws,R]
    omega
  · change r.ps.mem = _
    rw [ps]; rfl

end SetExtremaApplyAudit
namespace SetExtremaCallerAudit
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


open SetExtremaApplyAudit SetExtremaPrepareAudit

theorem apply_correct (minimum : Bool) (caller : NState)
    (sv sn : Nat) (bv bn : CppState.Binding) (v n x : Int)
    (cv : caller.scalarCell sv s64 = some (bv,⟨s64,v⟩))
    (cn : caller.scalarCell sn bl = some (bn,⟨bl,n⟩))
    (wv : bv.writable = true) (wn : bn.writable = true)
    (e : NExpr) (he : e.scalarOnly = true) (ht : e.resultType = s64)
    (value : e.denote (envOf caller) = some x)
    (gv : s64.valid v = true) (gn : bl.valid n = true) (gx : s64.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if minimum then applyMin else applyMax
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sv,.scalarReference sn,.value e] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sv,.scalarReference sn,.value e] =
        .finished (res,.scalar (if n ≠ 0 then x else v)) ∧
      ScalarPost2 caller Sinit res (2+e.nodes) 110 caller.scalars.memory := by
  let prog := if minimum then applyMin else applyMax
  refine RW2V1_correct prog s64 s64 bl s64
    (by cases minimum <;> rfl) (by cases minimum <;> rfl)
    (by cases minimum <;> decide) caller sv sn bv bn v n e x cv cn wv wn
    he ht value gx valid lengths strict base 1 (if n ≠ 0 then x else v)
    (by split <;> assumption) 30 ?_
  intro P hP
  subst hP
  let P := callerP caller ++ [(⟨s64,x⟩ : Cell)]
  have cv' : P[bv.address]? = some ⟨s64,v⟩ := refVal caller sv s64 bv v cv _
  have cn' : P[bn.address]? = some ⟨bl,n⟩ := refVal caller sn bl bn n cn _
  have cx' : P[(callerP caller).length]? = some ⟨s64,x⟩ := by simp [P]
  obtain ⟨r,ran,ret,cost,need,mem⟩ := apply_exec P bv.address bn.address (callerP caller).length v n x cv' cn' cx' gv gn gx
  refine ⟨r,?_,ret,cost,?_,?_⟩
  · cases minimum <;> simpa [prog,apply_same,ws_nil] using ran
  · change r.need ≤ P.length+100
    omega
  · rw [mem]
    simpa only [P,List.append_assoc] using Proofs.MonoidCallCore.take_P caller
      ([⟨s64,x⟩]++[⟨s64,if n ≠ 0 then x else v⟩])

end SetExtremaCallerAudit
namespace SetExtremaTransferred
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


theorem RangeMax_new0 : OriginalSetExtrema.RangeMax_new0 = Proofs.MonoidInstance.MonoidMax_long_long_new0 := rfl
theorem call_RangeMax_new0 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMax_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new0.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMax_new0

theorem RangeMax_new1 : OriginalSetExtrema.RangeMax_new1 = Proofs.MonoidInstance.MonoidMax_long_long_new1 := rfl
theorem call_RangeMax_new1 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMax_new1.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new1.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMax_new1

theorem RangeMax_e : OriginalSetExtrema.RangeMax_e = Proofs.MonoidInstance.MonoidMax_long_long_e := rfl
theorem call_RangeMax_e (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMax_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_e.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMax_e

theorem RangeMax_op : OriginalSetExtrema.RangeMax_op = Proofs.MonoidInstance.op_MonoidMax_long_long := rfl
theorem call_RangeMax_op (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMax_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMax_long_long.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMax_op

theorem RangeMin_new0 : OriginalSetExtrema.RangeMin_new0 = Proofs.MonoidInstance.MonoidMin_long_long_new0 := rfl
theorem call_RangeMin_new0 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMin_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_new0.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMin_new0

theorem RangeMin_new1 : OriginalSetExtrema.RangeMin_new1 = Proofs.MonoidInstance.MonoidMin_long_long_new1 := rfl
theorem call_RangeMin_new1 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMin_new1.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_new1.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMin_new1

theorem RangeMin_e : OriginalSetExtrema.RangeMin_e = Proofs.MonoidInstance.MonoidMin_long_long_e := rfl
theorem call_RangeMin_e (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMin_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_e.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMin_e

theorem RangeMin_op : OriginalSetExtrema.RangeMin_op = Proofs.MonoidInstance.op_MonoidMin_long_long := rfl
theorem call_RangeMin_op (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalSetExtrema.RangeMin_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMin_long_long.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) RangeMin_op

theorem set_new0 (second : Bool) :
    (if second then OriginalSetExtrema.RangeSet_new0_noop else OriginalSetExtrema.RangeSet_new0_v) = (if second then OriginalSetSum.RangeSet_new0_noop else OriginalSetSum.RangeSet_new0_v) := by cases second <;> rfl
theorem call_set_new0 (second : Bool) (fuel : Nat) (caller : NState) (args : List NArgument) :
  (if second then OriginalSetExtrema.RangeSet_new0_noop else OriginalSetExtrema.RangeSet_new0_v).callFuel fuel caller args = (if second then OriginalSetSum.RangeSet_new0_noop else OriginalSetSum.RangeSet_new0_v).callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) (set_new0 second)

theorem set_new1 (second : Bool) :
    (if second then OriginalSetExtrema.RangeSet_new1_noop else OriginalSetExtrema.RangeSet_new1_v) = (if second then OriginalSetSum.RangeSet_new1_noop else OriginalSetSum.RangeSet_new1_v) := by cases second <;> rfl
theorem call_set_new1 (second : Bool) (fuel : Nat) (caller : NState) (args : List NArgument) :
  (if second then OriginalSetExtrema.RangeSet_new1_noop else OriginalSetExtrema.RangeSet_new1_v).callFuel fuel caller args = (if second then OriginalSetSum.RangeSet_new1_noop else OriginalSetSum.RangeSet_new1_v).callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) (set_new1 second)

theorem set_id (second : Bool) :
    (if second then OriginalSetExtrema.RangeSet_id_noop else OriginalSetExtrema.RangeSet_id_v) = (if second then OriginalSetSum.RangeSet_id_noop else OriginalSetSum.RangeSet_id_v) := by cases second <;> rfl
theorem call_set_id (second : Bool) (fuel : Nat) (caller : NState) (args : List NArgument) :
  (if second then OriginalSetExtrema.RangeSet_id_noop else OriginalSetExtrema.RangeSet_id_v).callFuel fuel caller args = (if second then OriginalSetSum.RangeSet_id_noop else OriginalSetSum.RangeSet_id_v).callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) (set_id second)

theorem set_compose (second : Bool) :
    (if second then OriginalSetExtrema.RangeSet_compose_noop else OriginalSetExtrema.RangeSet_compose_v) = (if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v) := by cases second <;> rfl
theorem call_set_compose (second : Bool) (fuel : Nat) (caller : NState) (args : List NArgument) :
  (if second then OriginalSetExtrema.RangeSet_compose_noop else OriginalSetExtrema.RangeSet_compose_v).callFuel fuel caller args = (if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v).callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) (set_compose second)

end SetExtremaTransferred
