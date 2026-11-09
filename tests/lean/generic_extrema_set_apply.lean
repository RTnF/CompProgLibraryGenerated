namespace GenericSetApplyRaw
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


open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev bl : Ty := ⟨1,false,true⟩
abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
def refs (a b : Nat) : List CppState.Binding := [⟨a,true⟩,⟨b,true⟩]
def selected (v f x : Int) : Int := if f=0 then v else x
def yesInner (ty : Ty) : Command := .sequence (.primitive (.declare ty true (.variable ty 2)))
  (.sequence (.primitive (.assign 3 ty (.variable ty 4))) Sk)
def noInner (ty : Ty) : Command := .sequence (.primitive (.declare ty true (.variable ty 0)))
  (.sequence (.primitive (.declare ty true (.variable ty 4)))
    (.sequence (.scope Sk) (.sequence (.primitive (.assign 3 ty (.variable ty 5))) Sk)))
def yesBody (ty : Ty) : Command := .sequence (.scope (yesInner ty)) Sk
def noBody (ty : Ty) : Command := .sequence (.scope (noInner ty)) Sk
def choice (ty : Ty) : Command := .branch (.variable bl 1) (yesBody ty) (noBody ty)
def rawBody (ty : Ty) : Command := .sequence (.primitive (.declare ty true (.literal ty 0)))
  (.sequence (choice ty) Sk)

theorem ws_assign_second (ty : Ty) (P : List Cell) (R : List CppState.Binding) (L : List Cell)
    (x : Int) (e : NExpr) (v : Int) (hv : ty.valid v = true)
    (de : e.denote (penv (ws P R (cx ty x :: cx ty 0 :: L))) = some v) :
    pstmt (.assign (R.length+1) ty e) (ws P R (cx ty x :: cx ty 0 :: L)) =
      some ⟨ws P R (cx ty x :: cx ty v :: L),none,e.nodes+1,
        P.length+R.length+2*(L.length+2)+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (ws P R (cx ty x :: cx ty 0 :: L)) (R.length+1) ty e v de
    ⟨P.length+1,true⟩ (cx ty 0) (by simp [ws]) (by simp [ws]) rfl (Proofs.GenericLazy.valid_zero ty) rfl v (Ty.convert_of_valid ty v hv)
  have mem : (ws P R (cx ty x :: cx ty 0 :: L)).mem.set (P.length+1) (cx ty v) =
      (ws P R (cx ty x :: cx ty v :: L)).mem := by simp [ws]
  have need : (ws P R (cx ty x :: cx ty 0 :: L)).mem.length +
      (ws P R (cx ty x :: cx ty 0 :: L)).bs.length+e.nodes+2 =
      P.length+R.length+2*(L.length+2)+e.nodes+2 := by simp [ws]; omega
  rw [h,mem,need]
  rfl

theorem choice_exec (ty : Ty) (P : List Cell) (a b : Nat) (v f x : Int)
    (receiver : P[a]? = some (cx ty v)) (flag : P[b]? = some (cf f))
    (hv : ty.valid v = true) (hf : bl.valid f = true) (hx : ty.valid x = true) :
    ∃ r, pexec 1 (choice ty) (ws P (refs a b) [cx ty x,cx ty 0]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 10 else 7) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx ty x,cx ty (selected v f x)] := by
  let R := refs a b
  have cond : (NExpr.variable bl 1).denote (penv (ws P R [cx ty x,cx ty 0])) = some f := by
    rw [den_variable]; exact ws_env_ref P R _ 1 b true bl f rfl flag hf
  by_cases zero : f=0
  · have dv : (NExpr.variable ty 0).denote (penv (ws P R [cx ty x,cx ty 0])) = some v := by
      rw [den_variable]; exact ws_env_ref P R _ 0 a true ty v rfl receiver hv
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx ty x,cx ty 0] ty (.variable ty 0) v dv (Ty.convert_of_valid _ _ hv))
    have dv2 : (NExpr.variable ty 4).denote (penv (ws P R [cx ty x,cx ty 0,cx ty v])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 2 (cx ty v) ty rfl rfl hv
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [cx ty x,cx ty 0,cx ty v] ty (.variable ty 4) v dv2 (Ty.convert_of_valid _ _ hv))
    have dv3 : (NExpr.variable ty 5).denote (penv (ws P R [cx ty x,cx ty 0,cx ty v,cx ty v])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 3 (cx ty v) ty rfl rfl hv
    have q2 := (pexec_prim 1 _ _).trans (ws_assign_second ty P R [cx ty v,cx ty v] x (.variable ty 5) v hv dv3)
    have sc0 := pexec_scope 1 Sk (ws P R [cx ty x,cx ty 0,cx ty v,cx ty v]) _ (pexec_skip 1 _)
    have sc : pexec 1 (.scope Sk) (ws P R [cx ty x,cx ty 0,cx ty v,cx ty v]) =
        some ⟨ws P R [cx ty x,cx ty 0,cx ty v,cx ty v],none,1,P.length+10⟩ := by
      simp only [List.take_length] at sc0
      simpa [ws,R,refs,List.range_succ] using sc0
    have body := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (seq_some q2 rfl (pexec_skip 1 _))))
    have scope := pexec_scope 1 (noInner ty) (ws P R [cx ty x,cx ty 0]) _ body
    have clean : pexec 1 (noBody ty) (ws P R [cx ty x,cx ty 0]) =
        some ⟨ws P R [cx ty x,cx ty v],none,8,P.length+13⟩ := by
      have whole := seq_some scope rfl (pexec_skip 1 _)
      simpa [noBody,noInner,ws,R,refs,NExpr.nodes,List.take_append,List.range_succ,List.take_of_length_le,Nat.add_assoc] using whole
    have br := pexec_branch_false 1 (.variable bl 1) (yesBody ty) (noBody ty) (ws P R [cx ty x,cx ty 0])
      (by simpa [zero] using cond) _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes,zero]
    · simp [ws,R,refs,NExpr.nodes]
    · simp [selected,zero,R]
  · have dx : (NExpr.variable ty 2).denote (penv (ws P R [cx ty x,cx ty 0])) = some x := by
      rw [den_variable]; exact ws_env_loc P R _ 0 (cx ty x) ty rfl rfl hx
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx ty x,cx ty 0] ty (.variable ty 2) x dx (Ty.convert_of_valid _ _ hx))
    have dx2 : (NExpr.variable ty 4).denote (penv (ws P R [cx ty x,cx ty 0,cx ty x])) = some x := by
      rw [den_variable]; exact ws_env_loc P R _ 2 (cx ty x) ty rfl rfl hx
    have q1 := (pexec_prim 1 _ _).trans (ws_assign_second ty P R [cx ty x] x (.variable ty 4) x hx dx2)
    have body := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    have scope := pexec_scope 1 (yesInner ty) (ws P R [cx ty x,cx ty 0]) _ body
    have clean : pexec 1 (yesBody ty) (ws P R [cx ty x,cx ty 0]) =
        some ⟨ws P R [cx ty x,cx ty x],none,5,P.length+11⟩ := by
      have whole := seq_some scope rfl (pexec_skip 1 _)
      simpa [yesBody,yesInner,ws,R,refs,NExpr.nodes,List.take_append,List.range_succ,List.take_of_length_le,Nat.add_assoc] using whole
    have br := pexec_branch_true 1 (.variable bl 1) (yesBody ty) (noBody ty) (ws P R [cx ty x,cx ty 0]) f cond zero _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes,zero]
    · simp [ws,R,refs,NExpr.nodes]
    · simp [selected,zero,R]

theorem raw_exec (ty : Ty) (P : List Cell) (a b : Nat) (v f x : Int)
    (receiver : P[a]? = some (cx ty v)) (flag : P[b]? = some (cf f))
    (hv : ty.valid v = true) (hf : bl.valid f = true) (hx : ty.valid x = true) :
    ∃ r, pexec 1 (rawBody ty) (ws P (refs a b) [cx ty x]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 12 else 9) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx ty x,cx ty (selected v f x)] := by
  let R := refs a b
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx ty x] ty (.literal ty 0) 0 (by simp [NExpr.denote, Proofs.GenericLazy.valid_zero]) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  obtain ⟨u,qu,ru,cu,nu,pu⟩ := choice_exec ty P a b v f x receiver flag hv hf hx
  have run := seq_some q0 rfl (seq_some qu ru (pexec_skip 1 _))
  refine ⟨⟨u.ps,none,2+u.cost,max (P.length+9) (max u.need (u.ps.mem.length+u.ps.bs.length))⟩,?_,rfl,?_,?_,?_⟩
  · simpa [rawBody,ws,R,refs,NExpr.nodes,Nat.add_assoc] using run
  · simp [cu]; split <;> rfl
  · simp [ws,refs,pu] <;> omega
  · exact pu

end GenericSetApplyRaw

namespace GenericSetApplyCall
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


open TemplateMemberResult
open GenericSetApplyRaw
open ExtremaPrepareGeneral
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body


abbrev bl : Ty := ⟨1,false,true⟩
def gApply (ty : Ty) : NProgram :=
  ⟨[.scalar ty true true, .scalar bl true true, .scalar ty false true], .unit, GenericSetApplyRaw.rawBody ty⟩
def gApplyFields (ty : Ty) : List Proofs.CppConstructorFinish.ScalarField := [⟨3,ty⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) := [(ty,(true && (!targetConst || false)))]
def gApplyView (ty : Ty) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gApply ty) fuel caller arguments [] (gApplyFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gApplyObjects (ty : Ty) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.objectArguments caller [(false,[(ty,true),(bl,true)]),(true,[(ty,true)])] objects with
  | none => .fault
  | some args => gApplyView ty fuel caller args targetConst

variable {ty : Ty}
abbrev cf (f : Int) : Cell := ⟨bl,f⟩


theorem caller_cell (caller : NState) (slot : Nat) (ty : Ty) (binding : CppState.Binding) (v : Int)
    (found : caller.scalarCell slot ty = some (binding,⟨ty,v⟩)) :
    (callerP caller)[binding.address]? = some ⟨ty,v⟩ ∧ ty.valid v = true := by
  obtain ⟨index,sl,bs,mem,ht,hv⟩ := scalarCell_facts found
  refine ⟨?_,hv⟩
  simp only [callerP,List.getElem?_append_left (List.getElem?_eq_some_iff.mp mem).1]
  exact mem

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+20-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat :=
  max caller.frame.state.storage.peak caller.frame.state.liveSpace

def fieldBindings (P : List Cell) : List CppState.Binding :=
  (List.range 2).map fun i => ⟨P.length+i,true⟩
def fields (ty : Ty) (old x : Int) : List Cell := [cx ty old,cx ty x]
structure StageState (ty : Ty) (caller initial callee : NState) (a b : Nat) (old x : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields ty old x) (refs a b ++ fieldBindings (callerP caller)) (ssl 4)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+19) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true

theorem stage_ready (caller : NState) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (hx : ty.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] = some initial ∧
      runFuel fuel (gApply ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee binding.address flagBinding.address x (selected v f x) := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references2_value1 caller (gApply ty).parameters ty bl ty rfl
      receiverSlot flagSlot binding flagBinding v f x found writable flagFound flagWritable hx valid
  obtain ⟨receiver,hv⟩ := caller_cell caller receiverSlot ty binding v found
  obtain ⟨flag,hf⟩ := caller_cell caller flagSlot bl flagBinding f flagFound
  have hs : ty.valid (selected v f x) = true := by
    unfold selected
    split
    · exact hv
    · exact hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := GenericSetApplyRaw.raw_exec ty (callerP caller) binding.address flagBinding.address v f x receiver flag hv hf hx
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x]).mem
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x]).bs (ssl 3) := by
    refine ⟨by simpa [ssl] using slots,?_,?_,bas,scope⟩
    · simpa [ws] using mem
    · simpa [ws,refs,List.range_succ] using bindings
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope+1) caller.frame.state.storage.objects.length := by
    refine ⟨by rw [frame]; exact valid,by rw [frame]; exact lengths,by rw [frame],by rw [frame],?_,by rw [frame],by rw [frame]⟩
    intro owner c h
    rw [frame] at h
    have := strict owner c h
    omega
  have cq : Cq (scalarBound caller initial) (storageBound caller) initial.scalars.work initial := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · change initial.scalars.peak ≤ scalarBound caller initial
      unfold scalarBound; omega
    · change initial.frame.state.storage.peak ≤ storageBound caller
      rw [frame]; exact Nat.le_max_left _ _
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound (gApply ty).body (by simp [gApply, GenericSetApplyRaw.rawBody, GenericSetApplyRaw.choice, GenericSetApplyRaw.yesBody, GenericSetApplyRaw.noBody, GenericSetApplyRaw.yesInner, GenericSetApplyRaw.noInner, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,refs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state binding.address flagBinding.address x (selected v f x) := by
    refine ⟨?_,faD,?_,?_,hs⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl,refs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work,cost] at bound
      split at bound <;> omega
    · have stable := CppScalarContents.run_stable fuel (gApply ty).body initial step
        (by simp [gApply, GenericSetApplyRaw.rawBody, GenericSetApplyRaw.choice, GenericSetApplyRaw.yesBody, GenericSetApplyRaw.noBody, GenericSetApplyRaw.yesInner, GenericSetApplyRaw.noInner, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)
def destinationValues (ty : Ty) (x : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx ty x),!targetConst)]
def exported (ty : Ty) (x : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues ty x targetConst)

structure ExportState (ty : Ty) (x : Int) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx ty x)]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 1
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+21
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true

theorem finish_export (old x : Int) (a b : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee a b old x)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gApplyFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState ty x caller initial (exported ty x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields ty old x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c2 : callee.scalarCell 3 ty = some (⟨(callerP caller).length+1,true⟩,(cx ty x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cx,ready.xValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gApplyFields ty) = some [((cx ty x),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨3,ty⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c2]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty x),true)] (gPerm ty targetConst) =
      some (destinationValues ty x targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, cx]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields ty old x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (gApplyFields ty)
      [] (gPerm ty targetConst) =
        some (exported ty x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) := by
    unfold MemberView.finishView
    split
    · simp only [Proofs.CppConstructorMultiFinish.captureVectors,List.mapM_nil,captured,Bind.bind,Option.bind]
      rw [viewed]
      simp [Bind.bind,Option.bind,MemberView.restrictVectors,Proofs.CppConstructorRoots.finishRoots,
        Proofs.CppConstructorRoots.transferAll,Proofs.CppConstructorMultiFinish.descriptors,retired,
        exported,destinationValues]
    · rename_i failed
      exact (failed ⟨ready.scalar.scope,fits,by rw [takeM]⟩).elim
  refine ⟨finished,?_⟩
  have work := ready.counters.work
  have peak := ready.counters.scalarPeak
  have storagePeak := ready.counters.storagePeak
  have outerPeak := ready.counters.outerPeak
  change callee.scalars.peak ≤ scalarBound caller initial at peak
  change callee.frame.state.storage.peak ≤ storageBound caller at storagePeak
  change callee.peak ≤ scalarBound caller initial+storageBound caller at outerPeak
  have live := ready.frame.live
  have liveBound : caller.scalars.memory.length+1-caller.scalars.baseMemory+
      (caller.scalars.bindings.length+1) ≤ scalarBound caller initial := by
    unfold scalarBound
    have Psize : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    omega
  have sp : (exported ty x caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+1-caller.scalars.baseMemory+(caller.scalars.bindings.length+1)+0) ≤ _
    omega
  have tp : (exported ty x caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.xValid⟩
  · change callee.frame.state.wellFormed = true
    exact ready.frame.valid
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe,takeM,destinationValues]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe,
      destinationValues,Proofs.CppConstructorFinish.scalarBindings]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,destinationValues,
      Proofs.CppConstructorMultiFinish.vectorLocations,Proofs.CppConstructorFinish.scalarLocations]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,Proofs.CppConstructorMultiFinish.rebound]
  · change callee.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
    exact ready.frame.count
  · change callee.frame.state.liveSpace = caller.frame.state.liveSpace
    exact live
  · change callee.scalars.work+0+(destinationValues ty x targetConst).length+1 ≤ caller.scalars.work+21
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty x caller callee targetConst).scalars.peak+(exported ty x caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst)
    (slot : Nat) (ty : Ty) (binding : CppState.Binding) (cell : Cell)
    (found : caller.scalarCell slot ty = some (binding,cell)) :
    out.scalarCell slot ty = some (binding,cell) := by
  obtain ⟨index,sl,bs,mem,ht,hv⟩ := scalarCell_facts found
  have slo : out.slots[slot]? = some (.scalar index) := by
    rw [post.slots,List.getElem?_append_left (List.getElem?_eq_some_iff.mp sl).1]; exact sl
  have bso : out.scalars.bindings[index]? = some binding := by
    rw [post.bindings,List.getElem?_append_left (List.getElem?_eq_some_iff.mp bs).1]; exact bs
  have mo : out.scalars.memory[binding.address]? = some cell := by
    rw [post.memory,List.getElem?_append_left (List.getElem?_eq_some_iff.mp mem).1]; exact mem
  simp [NState.scalarCell,NState.scalarSlot,slo,bso,mo,ht,hv]

theorem destination_readable (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst) :
    out.scalarCell caller.slots.length ty = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx ty x)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx ty x) := by rw [post.memory]; simp
  simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]

theorem frame_extension (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension x caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension x caller initial out targetConst post valid lengths) reference value found



theorem view_export_correct (caller : NState) (targetConst : Bool) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (hx : ty.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] = some initial ∧
      (gApplyView ty) fuel caller
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty (selected v f x) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller receiverSlot flagSlot binding flagBinding v f x
    found writable flagFound flagWritable hx valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x (selected v f x) binding.address flagBinding.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty (selected v f x) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gApply ty) fuel caller initial callee _
    [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] []
    (gApplyFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool)
    (receiverSlot flagSlot xSlot : Nat) (binding flagBinding bx : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (sourceX : caller.scalarCell xSlot ty = some (bx,cx ty x))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] = some initial ∧
      (gApplyObjects ty) fuel caller
        [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty (selected v f x) caller initial out targetConst := by
  have hx := (caller_cell caller xSlot ty bx x sourceX).2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst receiverSlot flagSlot binding flagBinding v f x
    found writable flagFound flagWritable hx valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(false,[(ty,true),(bl,true)]),(true,[(ty,true)])]
      [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] =
        some [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x)] := by
    simp [MemberFactory.objectArguments,MemberFactory.referenceFields,MemberFactory.valueFields,
      found,flagFound,sourceX,writable,flagWritable,cx,cf]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
    [(false,[(ty,true),(bl,true)]),(true,[(ty,true)])]
    [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gApplyView ty) fuel caller arguments targetConst) = _
  rw [args]
  exact ran

theorem total_work (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst) : out.work ≤ caller.work+21 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericSetApplyCall
