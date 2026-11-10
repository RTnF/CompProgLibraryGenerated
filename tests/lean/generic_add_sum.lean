namespace GenericAddSum
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
variable (ty : Ty)

abbrev picked (base : Nat) (second : Bool) : NExpr :=
  if second then .variable i32 (base+3) else .variable ty (base+2)

def fieldsBody (base : Nat) (xe se : NExpr) (second : Bool) : Command :=
  .sequence (.primitive (.declare ty true xe))
    (.sequence (.primitive (.declare i32 true se))
      (.sequence (.primitive (.declare ty true (.variable ty base)))
        (.sequence (.primitive (.declare i32 true (.variable i32 (base+1))))
          (.sequence (.primitive (.ret (picked ty base second))) Sk))))

theorem fields_exec (P : List Cell) (R : List CppState.Binding) (xe se : NExpr)
    (x sz : Int) (second : Bool)
    (hx : ty.valid x = true) (hsz : i32.valid sz = true)
    (dx : xe.denote (penv (ws P R [])) = some x)
    (ds : se.denote (penv (ws P R [⟨ty,x⟩])) = some sz) :
    ∃ r, pexec 1 (fieldsBody ty R.length xe se second) (ws P R []) = some r ∧
      r.ret = some (if second then sz else x) ∧ r.cost ≤ xe.nodes+se.nodes+8 ∧
      r.need ≤ P.length+R.length+xe.nodes+se.nodes+20 ∧
      r.ps.mem = P ++ [⟨ty,x⟩,⟨i32,sz⟩,⟨ty,x⟩,⟨i32,sz⟩] := by
  let L1 : List Cell := [⟨ty,x⟩]
  let L2 : List Cell := L1 ++ [⟨i32,sz⟩]
  let L3 : List Cell := L2 ++ [⟨ty,x⟩]
  let L4 : List Cell := L3 ++ [⟨i32,sz⟩]
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [] ty xe x dx (Proofs.GenericCall.convG ty _ hx))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L1 i32 se sz ds (conv_signed i32 rfl rfl _ hsz))
  have ex : penv (ws P R L2) R.length ty = some x := by
    simpa using ws_env_loc P R L2 0 ⟨ty,x⟩ ty rfl rfl hx
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L2 ty (.variable ty R.length) x
    (by rw [den_variable]; exact ex) (Proofs.GenericCall.convG ty _ hx))
  have es : penv (ws P R L3) (R.length+1) i32 = some sz :=
    ws_env_loc P R L3 1 ⟨i32,sz⟩ i32 rfl rfl hsz
  have q4 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 (R.length+1)) sz
    (by rw [den_variable]; exact es) (conv_signed i32 rfl rfl _ hsz))
  have dpick : (picked ty R.length second).denote (penv (ws P R L4)) = some (if second then sz else x) := by
    cases second
    · change (NExpr.variable ty (R.length+2)).denote (penv (ws P R L4)) = some x
      rw [den_variable]; exact ws_env_loc P R L4 2 ⟨ty,x⟩ ty rfl rfl hx
    · change (NExpr.variable i32 (R.length+3)).denote (penv (ws P R L4)) = some sz
      rw [den_variable]; exact ws_env_loc P R L4 3 ⟨i32,sz⟩ i32 rfl rfl hsz
  have qr := exec_ret 1 (ws P R L4) (picked ty R.length second) (if second then sz else x) dpick
  refine ⟨_,seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some q4 rfl qr))),rfl,?_,?_,?_⟩
  · cases second <;> simp [picked,NExpr.nodes] <;> omega
  · cases second <;> simp [picked,NExpr.nodes,ws,L1,L2,L3,L4] <;> omega
  · simp [ws,L1,L2,L3,L4]


abbrev zero64 : NExpr := Proofs.GenericLazy.castTo ty i32 (.literal i32 0)
abbrev zero32 : NExpr := .literal i32 0
abbrev opX : NExpr := .binary ty .add (.variable ty 0) (.variable ty 2)
abbrev defaultPicked (second : Bool) : NExpr := if second then .variable i32 1 else .variable ty 0
abbrev defaultBody (second : Bool) : Command :=
  .sequence (.primitive (.declare ty true (zero64 ty)))
    (.sequence (.primitive (.declare i32 true zero32))
      (.sequence (.primitive (.ret (defaultPicked ty second))) Sk))
abbrev rtype (second : Bool) : Ty := if second then i32 else ty
def gApply (second : Bool) : NProgram :=
  ⟨[.scalar ty true true, .scalar ty false true, .scalar i32 false true], .scalar (rtype ty second),
    fieldsBody ty 3 (Proofs.GenericLazy.raSumG ty) (.variable i32 2) second⟩
def gCompose : NProgram := ⟨[.scalar ty false true,.scalar ty false true],.scalar ty,(Proofs.GenericCall.composeAdd ty).body⟩
def gE (second : Bool) : NProgram := ⟨[], .scalar (rtype ty second), fieldsBody ty 0 (zero64 ty) zero32 second⟩
def gNew1 (second : Bool) : NProgram := ⟨[], .scalar (rtype ty second), defaultBody ty second⟩
def gNew0 (second : Bool) : NProgram :=
  ⟨[.scalar ty false true, .scalar i32 false true], .scalar (rtype ty second),
    fieldsBody ty 2 (.variable ty 0) (.variable i32 1) second⟩
def gOp (second : Bool) : NProgram :=
  ⟨[.scalar ty true false, .scalar i32 true false, .scalar ty true false, .scalar i32 true false],
    .scalar (rtype ty second), fieldsBody ty 4 (opX ty) opSizeE second⟩

theorem apply_body (second : Bool) :
    (gApply ty second).body =
      fieldsBody ty 3 (Proofs.GenericLazy.raSumG ty) (.variable i32 2) second := by cases second <;> rfl

theorem apply_exec (P : List Cell) (av ax az : Nat) (v x sz : Int) (second : Bool)
    (cv : P[av]? = some ⟨ty,v⟩) (cx : P[ax]? = some ⟨ty,x⟩) (cz : P[az]? = some ⟨i32,sz⟩)
    (hv : ty.valid v = true) (hx : ty.valid x = true) (hz : i32.valid sz = true) (hzt : ty.valid sz = true)
    (q s : Int) (hcp : ty.convert (sz*v) = some q) (hcs : ty.convert (x+q) = some s)
    (hsum : ty.valid s = true) :
    ∃ r, pexec 1 (gApply ty second).body
        (ws P [⟨av,true⟩,⟨ax,true⟩,⟨az,true⟩] []) = some r ∧
      r.ret = some (if second then sz else s) ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length+40 ∧
      r.ps.mem = P ++ [⟨ty,s⟩,⟨i32,sz⟩,⟨ty,s⟩,⟨i32,sz⟩] := by
  let R : List CppState.Binding := [⟨av,true⟩,⟨ax,true⟩,⟨az,true⟩]
  have e0 : penv (ws P R []) 0 ty = some v := ws_env_ref P R [] 0 av true ty v rfl cv hv
  have e1 : penv (ws P R []) 1 ty = some x := ws_env_ref P R [] 1 ax true ty x rfl cx hx
  have e2 : penv (ws P R []) 2 i32 = some sz := ws_env_ref P R [] 2 az true i32 sz rfl cz hz
  have den : (Proofs.GenericLazy.raSumG ty).denote (penv (ws P R [])) = some (s) := by
    rw [den_binary,den_variable,den_binary,Proofs.GenericLazy.castTo_den ty i32 (.variable i32 2) _ sz (by rw [den_variable]; exact e2) hzt,den_variable,e1,e0]
    simp only [Option.bind_some]
    have m1 : binaryValue .mul sz v = sz*v := rfl
    rw [m1,hcp]
    simp only [Option.bind_some]
    exact hcs
  have ds : (NExpr.variable i32 2).denote (penv (ws P R [⟨ty,s⟩])) = some sz := by
    rw [den_variable]; exact ws_env_ref P R _ 2 az true i32 sz rfl cz hz
  obtain ⟨r,ran,ret,cost,need,mem⟩ := fields_exec ty P R (Proofs.GenericLazy.raSumG ty) (.variable i32 2) (s) sz second hsum hz den ds
  rw [apply_body ty]
  have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.variable i32 2)
  simp only [NExpr.nodes] at hn
  refine ⟨r,ran,ret,?_,?_,mem⟩
  · simp [NExpr.nodes, zero64] at cost
    omega
  · simp [R,NExpr.nodes] at need
    omega

theorem prep_mutable_values2 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (u1 : Ty) (u2 : Ty) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (hp : params = [.scalar t1 true true,.scalar u1 false true,.scalar u2 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (writable : b1.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 1 + e1.nodes+e2.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩,⟨u2,n2⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller (caller.charge 1 1) := (core_charge caller 1 1)
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨q2,ran2,good2⟩ := scalar_eval e2 q1 n2 hs2 (by rw [envOf_core core1]; exact value2)
  have core2 : Core caller q2 := core1.trans good2.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core2
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1

  have fs : q2.frame.state = caller.frame.state := by rw [cf]
  have fr : q2.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q2.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have res1 : resolve caller (.scalar t1 true true) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address true) := by simp [resolve,c1,writable]
  have resv1 : resolve (caller.charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  have resv2 : resolve q1 (.scalar u2 false true) (.value e2) = some (q2,.scalar u2 true n2) := by
    simp [resolve,hty2,ran2]
  refine ⟨q2,?_,?_⟩
  · have g1 := good1.2.2.1
    have g2 := good2.2.2.1
    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,resv1,resv2]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,nv2,callerP,NState.observe,
    CppState.State.observe,h1,w1]
  have g1 := good1.2.2.2.2.1
  have g2 := good2.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 g2 ⊢
  omega

theorem mutable_values2_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (u1 : Ty) (u2 : Ty)
    (hp : prog.parameters = [.scalar t1 true true,.scalar u1 false true,.scalar u2 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (writable : b1.writable = true)
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
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.value e1,.value e2] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (1+e1.nodes+e2.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_mutable_values2 caller _ t1 u1 u2 s1 b1 v1 e1 n1 e2 n2 hp c1 writable hs1 hty1 value1 nv1 hs2 hty2 value2 nv2 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) [⟨b1.address,true⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (1+e1.nodes+e2.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post


theorem apply_correct (second : Bool) (caller : NState)
    (slot : Nat) (binding : CppState.Binding) (v x sz : Int)
    (cell : caller.scalarCell slot ty = some (binding,⟨ty,v⟩)) (writable : binding.writable = true)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (ht1 : e1.resultType = ty)
    (hs2 : e2.scalarOnly = true) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some x) (value2 : e2.denote (envOf caller) = some sz)
    (gv : ty.valid v = true) (gx : ty.valid x = true) (gz : i32.valid sz = true)
    (gzt : ty.valid sz = true) (q s : Int) (hcp : ty.convert (sz*v) = some q)
    (hcs : ty.convert (x+q) = some s) (gs : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gApply ty second
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference slot,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference slot,.value e1,.value e2] =
        .finished (res,.scalar (if second then sz else s)) ∧
      ScalarPost2 caller Sinit res (1+e1.nodes+e2.nodes) 100 caller.scalars.memory := by
  let prog := gApply ty second
  refine mutable_values2_correct prog (if second then i32 else ty) ty ty i32
    (by cases second <;> rfl) (by cases second <;> rfl)
    (by show Scalar (fieldsBody ty 3 (Proofs.GenericLazy.raSumG ty) (.variable i32 2) second) = true; have h := Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 2) rfl; cases second <;> simp [fieldsBody, picked, Scalar, NExpr.scalarOnly, Proofs.GenericLazy.raSumG, h]) caller slot binding v e1 x e2 sz cell writable
    hs1 ht1 value1 gx hs2 ht2 value2 gz valid lengths strict base 1 (if second then sz else s)
    (by cases second <;> assumption) 20 ?_
  intro P hP
  subst hP
  let P := callerP caller ++ [(⟨ty,x⟩ : Cell),⟨i32,sz⟩]
  have cv : P[binding.address]? = some ⟨ty,v⟩ := refVal caller slot ty binding v cell _
  have cx : P[(callerP caller).length]? = some ⟨ty,x⟩ := by
    simp [P]
  have cz : P[(callerP caller).length+1]? = some ⟨i32,sz⟩ := by
    simp [P]
  obtain ⟨r,ran,ret,cost,need,mem⟩ := apply_exec ty P binding.address (callerP caller).length
    ((callerP caller).length+1) v x sz second cv cx cz gv gx gz gzt q s hcp hcs gs
  refine ⟨r,?_,ret,cost,?_,?_⟩
  · cases second <;> simpa [prog,P,ws_nil] using ran
  · change r.need ≤ P.length+100
    omega
  · rw [mem]
    simpa only [P,List.append_assoc] using Proofs.MonoidCallCore.take_P caller
      ([⟨ty,x⟩,⟨i32,sz⟩]++[⟨ty,s⟩,⟨i32,sz⟩,⟨ty,s⟩,⟨i32,sz⟩])


theorem constant_body_correct (prog : NProgram) (ty : Ty) (v : Int)
    (hp : prog.parameters = []) (hr : prog.result = ResultKind.scalar ty)
    (scalar : Scalar prog.body = true) (hv : ty.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec 1 prog.body ⟨P,[]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,ran,ret,cost,need,mem⟩ := hex (callerP caller) rfl
  have post := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base scalar 1 r ran v ret ty hr hv
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [mem] using hpost⟩

theorem default_fields_exec (P : List Cell) (second : Bool) :
    ∃ r, pexec 1 (defaultBody ty second) (ws P [] []) = some r ∧ r.ret = some 0 ∧
      r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨ty,0⟩,⟨i32,0⟩] := by
  let L1 : List Cell := [⟨ty,0⟩]
  let L2 : List Cell := L1 ++ [⟨i32,0⟩]
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [] ty (zero64 ty) 0 (Proofs.GenericLazy.R0z_gen ty _) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P [] L1 i32 zero32 0 rfl rfl)
  have den : (defaultPicked ty second).denote (penv (ws P [] L2)) = some 0 := by
    cases second
    · change (NExpr.variable ty 0).denote (penv (ws P [] L2)) = some 0
      rw [den_variable]; exact ws_env_loc P [] L2 0 ⟨ty,0⟩ ty rfl rfl (Proofs.GenericLazy.valid_zero ty)
    · change (NExpr.variable i32 1).denote (penv (ws P [] L2)) = some 0
      rw [den_variable]; exact ws_env_loc P [] L2 1 ⟨i32,0⟩ i32 rfl rfl rfl
  have qr := exec_ret 1 (ws P [] L2) (defaultPicked ty second) 0 den
  have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
  simp only [NExpr.nodes] at hn
  refine ⟨_,seq_some q1 rfl (seq_some q2 rfl qr),rfl,?_,?_,?_⟩
  · cases second <;> simp [defaultPicked,NExpr.nodes,zero64] <;> omega
  · cases second <;> simp [defaultPicked,NExpr.nodes,ws,L1,L2,zero64] <;> omega
  · simp [ws,L1,L2]

theorem e_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gE ty second
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  let prog := gE ty second
  refine constant_body_correct prog (if second then i32 else ty) 0
    (by cases second <;> rfl) (by cases second <;> rfl) (by show Scalar (prog.body) = true; cases second <;> simp [prog, gE, gNew1, gNew0, gOp, fieldsBody, picked, defaultBody, defaultPicked, Scalar, NExpr.scalarOnly, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl])
    (by cases second; exact Proofs.GenericLazy.valid_zero ty; rfl) caller valid lengths strict base ?_
  intro P hP
  subst hP
  have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
  simp only [NExpr.nodes] at hn
  obtain ⟨r,ran,ret,cost,need,mem⟩ := fields_exec ty (callerP caller) [] (zero64 ty) zero32 0 0 second (Proofs.GenericLazy.valid_zero ty) rfl (Proofs.GenericLazy.R0z_gen ty _) rfl
  have body : prog.body = fieldsBody ty 0 (zero64 ty) zero32 second := by cases second <;> rfl
  refine ⟨r,?_,by simpa using ret,?_,?_,?_⟩
  · rw [body]; simpa only [ws_nil,List.length_nil] using ran
  · simp [NExpr.nodes, zero64] at cost
    omega
  · simp [NExpr.nodes, zero64] at need
    omega
  · rw [mem]; exact take_P caller _

theorem default_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gNew1 ty second
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  let prog := gNew1 ty second
  refine constant_body_correct prog (if second then i32 else ty) 0
    (by cases second <;> rfl) (by cases second <;> rfl) (by show Scalar (prog.body) = true; cases second <;> simp [prog, gE, gNew1, gNew0, gOp, fieldsBody, picked, defaultBody, defaultPicked, Scalar, NExpr.scalarOnly, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl])
    (by cases second; exact Proofs.GenericLazy.valid_zero ty; rfl) caller valid lengths strict base ?_
  intro P hP
  subst hP
  obtain ⟨r,ran,ret,cost,need,mem⟩ := default_fields_exec ty (callerP caller) second
  have body : prog.body = defaultBody ty second := by cases second <;> rfl
  refine ⟨r,?_,ret,cost,need,?_⟩
  · rw [body]; simpa only [ws_nil] using ran
  · rw [mem]; exact take_P caller _

theorem prepare_mixed_values (ty1 ty2 : Ty) (caller : NState) (params : List Proofs.CppVectorBindings.Parameter)
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


theorem two_values_body_correct (prog : NProgram) (t1 t2 tn : Ty)
    (hp : prog.parameters = [.scalar t1 false true,.scalar t2 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (e1 e2 : NExpr) (x y rv : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = t1) (ht2 : e2.resultType = t2)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : t1.valid x = true) (hy : t2.valid y = true) (hv : tn.valid rv = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hex : ∀ P : List Cell, P = callerP caller ++ [⟨t1,x⟩,⟨t2,y⟩] →
      ∃ r, pexec 1 prog.body ⟨P,[⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ = some r ∧
        r.ret = some rv ∧ r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar rv) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  obtain ⟨q1,q2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_mixed_values t1 t2 caller _ hp e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 valid hx hy
  let P := callerP caller ++ [⟨t1,x⟩,⟨t2,y⟩]
  let R : List CppState.Binding := [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
  have hlen : P.length = (callerP caller).length+2 := by simp [P]
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  obtain ⟨r,ran,ret,cost,need,mem⟩ := hex P rfl
  have peak1 := g1.2.2.2.2.1
  have peak2 := g2.2.2.2.2.1
  have work1 := g1.2.2.1
  have work2 := g2.2.2.1
  have post := call_scalar caller prog [.value e1,.value e2] Sinit P R
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [P,callerP]) (by rw [takeM]) valid lengths strict base hbody 1 r ran rv ret tn hr hv
    (by omega) (by simp [R];omega) (e1.nodes+e2.nodes) 70 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [mem] using hpost⟩

theorem new_correct (second : Bool) (caller : NState) (e1 e2 : NExpr) (x sz : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = ty) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some sz)
    (hx : ty.valid x = true) (hz : i32.valid sz = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gNew0 ty second
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (if second then sz else x)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  let prog := gNew0 ty second
  refine two_values_body_correct prog ty i32 (if second then i32 else ty)
    (by cases second <;> rfl) (by cases second <;> rfl) (by show Scalar (prog.body) = true; cases second <;> simp [prog, gE, gNew1, gNew0, gOp, fieldsBody, picked, defaultBody, defaultPicked, Scalar, NExpr.scalarOnly, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl])
    caller e1 e2 x sz (if second then sz else x) hs1 hs2 ht1 ht2 d1 d2 hx hz
    (by cases second <;> assumption) valid lengths strict base ?_
  intro P hP
  subst hP
  let P := callerP caller ++ [⟨ty,x⟩,⟨i32,sz⟩]
  let R : List CppState.Binding := [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
  have cx : P[(callerP caller).length]? = some ⟨ty,x⟩ := by simp [P]
  have cz : P[(callerP caller).length+1]? = some ⟨i32,sz⟩ := by simp [P]
  have dx : (NExpr.variable ty 0).denote (penv (ws P R [])) = some x := by
    rw [den_variable]; exact ws_env_ref P R [] 0 _ true ty x rfl cx hx
  have ds : (NExpr.variable i32 1).denote (penv (ws P R [⟨ty,x⟩])) = some sz := by
    rw [den_variable]; exact ws_env_ref P R _ 1 _ true i32 sz rfl cz hz
  obtain ⟨r,ran,ret,cost,need,mem⟩ := fields_exec ty P R (.variable ty 0) (.variable i32 1) x sz second hx hz dx ds
  have body : prog.body = fieldsBody ty 2 (.variable ty 0) (.variable i32 1) second := by cases second <;> rfl
  refine ⟨r,?_,ret,?_,?_,?_⟩
  · rw [body]; simpa [R,ws_nil] using ran
  · simp [NExpr.nodes, zero64] at cost
    omega
  · simp [R,NExpr.nodes] at need
    change r.need ≤ P.length+40
    omega
  · rw [mem]
    simpa only [P,List.append_assoc] using take_P caller
      ([⟨ty,x⟩,⟨i32,sz⟩]++[⟨ty,x⟩,⟨i32,sz⟩,⟨ty,x⟩,⟨i32,sz⟩])

theorem op_correct (second : Bool) (caller : NState) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : ty.valid v1 = true) (g2 : i32.valid v2 = true)
    (g3 : ty.valid v3 = true) (g4 : i32.valid v4 = true)
    (s13 : Int) (hc13 : ty.convert (v1+v3) = some s13) (gx : ty.valid s13 = true) (gz : i32.valid (v2+v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gOp ty second
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if second then v2+v4 else s13)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  let prog := gOp ty second
  refine Proofs.ScalarRefs.refs4t_correct prog (if second then i32 else ty) ty i32 ty i32
    (by cases second <;> rfl) (by cases second <;> rfl) (by show Scalar (prog.body) = true; cases second <;> simp [prog, gE, gNew1, gNew0, gOp, fieldsBody, picked, defaultBody, defaultPicked, Scalar, NExpr.scalarOnly, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl])
    caller s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base
    1 (if second then v2+v4 else s13) (by cases second <;> assumption) 20 ?_
  intro P hP
  subst hP
  let P := callerP caller
  let R : List CppState.Binding := [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]
  have e0 : penv (ws P R []) 0 ty = some v1 :=
    ws_env_ref P R [] 0 b1.address false ty v1 rfl (Proofs.IntervalCall.P_cell_ty caller s1 ty b1 v1 c1) g1
  have e2 : penv (ws P R []) 2 ty = some v3 :=
    ws_env_ref P R [] 2 b3.address false ty v3 rfl (Proofs.IntervalCall.P_cell_ty caller s3 ty b3 v3 c3) g3
  have dx : (opX ty).denote (penv (ws P R [])) = some s13 := by
    rw [den_binary,den_variable,den_variable,e0,e2]
    simp only [Option.bind_some]
    exact hc13
  have e1 : penv (ws P R [⟨ty,s13⟩]) 1 i32 = some v2 :=
    ws_env_ref P R _ 1 b2.address false i32 v2 rfl (Proofs.IntervalCall.P_cell_ty caller s2 i32 b2 v2 c2) g2
  have e3 : penv (ws P R [⟨ty,s13⟩]) 3 i32 = some v4 :=
    ws_env_ref P R _ 3 b4.address false i32 v4 rfl (Proofs.IntervalCall.P_cell_ty caller s4 i32 b4 v4 c4) g4
  have ds : opSizeE.denote (penv (ws P R [⟨ty,s13⟩])) = some (v2+v4) := by
    rw [den_binary,den_variable,den_variable,e1,e3]
    simp only [Option.bind_some]
    exact conv_signed i32 rfl rfl _ gz
  obtain ⟨r,ran,ret,cost,need,mem⟩ := fields_exec ty P R (opX ty) opSizeE s13 (v2+v4) second gx gz dx ds
  have body : prog.body = fieldsBody ty 4 (opX ty) opSizeE second := by cases second <;> rfl
  refine ⟨r,?_,ret,?_,?_,?_⟩
  · rw [body]; simpa [R,ws_nil] using ran
  · simp [NExpr.nodes, zero64] at cost
    omega
  · simp [R,NExpr.nodes] at need
    change r.need ≤ P.length+100
    omega
  · rw [mem]; exact take_P caller _

theorem add_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = ty) (value : e.denote (envOf caller) = some v)
    (hv : ty.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.GenericLazy.addNew0 ty).parameters [.value e] = some Sinit ∧
      (Proofs.GenericLazy.addNew0 ty).callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  Proofs.GenericLazy.rangeadd_new0_gen ty caller e v hs hty value hv valid lengths strict base

theorem add_id_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.GenericLazy.addNew1 ty).parameters [] = some Sinit ∧
      (Proofs.GenericLazy.addNew1 ty).callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.GenericLazy.rangeadd_new1_gen ty caller valid lengths strict base

theorem compose_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = ty) (ht2 : e2.resultType = ty)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : ty.valid x = true) (hy : ty.valid y = true) (s : Int) (hc : ty.convert (x+y) = some s) (hxy : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (gCompose ty).parameters [.value e1,.value e2] = some Sinit ∧
      (gCompose ty).callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar s) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  refine two_values_body_correct (gCompose ty) ty ty ty rfl rfl (Proofs.GenericCall.composeAdd_scalar ty)
    caller e1 e2 x y s hs1 hs2 ht1 ht2 d1 d2 hx hy hxy valid lengths strict base ?_
  intro P hP
  subst hP
  let P := callerP caller ++ [(⟨ty,x⟩ : Cell),⟨ty,y⟩]
  let R : List CppState.Binding := [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
  have e0 : penv (ws P R []) 0 ty = some x :=
    ws_env_ref P R [] 0 (callerP caller).length true ty x rfl (by simp [P]) hx
  have e1 : penv (ws P R []) 1 ty = some y :=
    ws_env_ref P R [] 1 ((callerP caller).length+1) true ty y rfl (by simp [P]) hy
  obtain ⟨r,ran,ret,cost,need,mem⟩ := Proofs.GenericCall.shapeG_exec ty P R (Proofs.GenericCall.addG ty) s hxy
    (Proofs.GenericCall.addG_den_conv ty _ x y s e0 e1 hc) (by simp [NExpr.nodes])
  refine ⟨r,?_,ret,cost,?_,?_⟩
  · have hb : (gCompose ty).body = Proofs.GenericCall.shapeG ty 2 (Proofs.GenericCall.addG ty) := rfl
    rw [hb]
    simpa [R,ws_nil,P] using ran
  · change r.need ≤ P.length+40
    simp [R] at need
    omega
  · rw [mem]
    simpa only [P,List.append_assoc] using take_P caller
      ([⟨ty,x⟩,⟨ty,y⟩]++[⟨ty,s⟩,⟨ty,s⟩])

end GenericAddSum
