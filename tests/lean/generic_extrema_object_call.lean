namespace GenericExtremaCall
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


open OriginalExtremaObject
open Proofs.Mod61Body


def gProgram (ty : Ty) (li ri : Nat) : NProgram :=
  ⟨[.scalar ty true false, .scalar ty true false], .unit, Proofs.GenericExtrema.selectionBody ty li ri⟩
def gFields (ty : Ty) (slot : Nat) : List Proofs.CppConstructorFinish.ScalarField := [⟨slot,ty⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) := [(ty,(true && (!targetConst || false)))]
def gExpected (li ri : Nat) (x y : Int) : Int := if (if li = 0 then x else y) < (if ri = 0 then x else y) then y else x
def gView (ty : Ty) (li ri : Nat) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gProgram ty li ri) fuel caller arguments [] (gFields ty 5)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gCombine (ty : Ty) (li ri : Nat) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.referenceArguments caller [[(ty,false)], [(ty,false)]] objects with
  | none => .fault
  | some args => gView ty li ri fuel caller args targetConst

variable {ty : Ty} {li ri : Nat}

def gNullary (ty : Ty) (body : Command) : NProgram := ⟨[], .unit, body⟩
def gNullaryView (ty : Ty) (body : Command) (slot : Nat) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gNullary ty body) fuel caller arguments [] (gFields ty slot)
    (vectorPermissions targetConst) (gPerm ty targetConst)

def inputs (a b : Nat) : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩]
def fields (ty : Ty) (nl : Nat) (x : Int) : List Cell := List.replicate nl ⟨ty,x⟩

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

def fieldBindings (nl : Nat) (P : List Cell) : List CppState.Binding :=
  (List.range nl).map fun i => ⟨P.length+i,true⟩

structure StageState (ty : Ty) (ins : List CppState.Binding) (nl : Nat) (caller initial callee : NState) (x : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields ty nl x) (ins ++ fieldBindings nl (callerP caller)) (ssl (ins.length+nl))
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+45) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true

theorem stage_of_exec (prog : NProgram) (ins : List CppState.Binding) (nl : Nat) (x : Int)
    (hx : ty.valid x = true) (caller initial : NState) (args : List NArgument)
    (prepared : prepare caller prog.parameters args = some initial)
    (hslots : initial.slots = ssl ins.length) (mem : initial.scalars.memory = callerP caller)
    (bindings : initial.scalars.bindings = ins) (bas : initial.scalars.baseMemory = caller.scalars.baseMemory)
    (scope : initial.scope = caller.scope+1)
    (frame : initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩)
    (work : initial.scalars.work ≤ caller.scalars.work+5)
    (peak : caller.scalars.peak ≤ initial.scalars.peak)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hsc : Scalar prog.body = true) (hal : CppScalarContents.Allowed prog.body = true)
    (hins : ins.length ≤ 2) (hnl : nl ≤ 4)
    (rr : PR) (ran : pexec 1 prog.body ⟨callerP caller,ins⟩ = some rr)
    (ret : rr.ret = none) (cost : rr.cost ≤ 40) (need : rr.need ≤ (callerP caller).length+16)
    (ps : rr.ps = Proofs.GroupCall.ws (callerP caller) ins (List.replicate nl ⟨ty,x⟩)) :
    ∃ fuel callee, runFuel fuel prog.body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty ins nl caller initial callee x := by
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1) (callerP caller)
      ins (ssl ins.length) := ⟨hslots,mem,bindings,bas,scope⟩
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope+1) caller.frame.state.storage.objects.length := by
    refine ⟨by rw [frame]; exact valid,by rw [frame]; exact lengths,by rw [frame],by rw [frame],?_,by rw [frame],by rw [frame]⟩
    intro owner sc h
    rw [frame] at h
    have := strict owner sc h
    omega
  have cq : Cq (scalarBound caller initial) (storageBound caller) initial.scalars.work initial := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · change initial.scalars.peak ≤ scalarBound caller initial
      unfold scalarBound; omega
    · change initial.frame.state.storage.peak ≤ storageBound caller
      rw [frame]; exact Nat.le_max_left _ _
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (callerP caller).length := by simp [callerP]; omega
  have run := sound prog.body hsc 1 _ rr ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty ins nl caller initial step.state x := by
    refine ⟨?_,faD,?_,?_,hx⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      omega
    · have stable := CppScalarContents.run_stable fuel prog.body initial step
        hal (by intro owner sc found; rw [frame] at found; have h := strict owner sc found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨fuel,step.state,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)


theorem stage_ready (hij : (li = 0 ∧ ri = 1) ∨ (li = 1 ∧ ri = 0)) (caller : NState) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 ty = some (b2,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee,
      prepare caller (gProgram ty li ri).parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      runFuel fuel (gProgram ty li ri).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty (inputs b1.address b2.address) 4 caller initial callee ((gExpected li ri) x y) := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_ref2 caller (gProgram ty li ri).parameters ty false false rfl s1 s2 b1 b2 x y c1 c2 (by simp) (by simp) valid
  obtain ⟨p0,hx⟩ := caller_cell caller s1 ty b1 x c1
  obtain ⟨p1,hy⟩ := caller_cell caller s2 ty b2 y c2
  have hv : ty.valid ((gExpected li ri) x y) = true := by
    unfold gExpected
    by_cases h : (if li = 0 then x else y) < (if ri = 0 then x else y)
    · rw [ite_eq_left h]; exact hy
    · rw [ite_eq_right h]; exact hx
  obtain ⟨rr,ran0,ret,cost,need,ps0⟩ := Proofs.GenericExtrema.selection_exec ty li ri hij (callerP caller)
    b1.address b2.address x y hx hy p0 p1
  have ran : pexec 1 (gProgram ty li ri).body ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩]⟩ = some rr := ran0
  have ps : rr.ps = Proofs.GroupCall.ws (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩] (List.replicate 4 ⟨ty,gExpected li ri x y⟩) := by
    rw [ps0]; rfl
  obtain ⟨fuel,callee,ran',st⟩ := stage_of_exec (gProgram ty li ri) (inputs b1.address b2.address) 4 (gExpected li ri x y) hv
    caller initial _ prepared (by simpa [inputs,ssl,List.range_succ] using slots) mem bindings bas scope frame (by omega) peak
    valid lengths strict base (by simp [gProgram, Proofs.GenericExtrema.selectionBody, Scalar, NExpr.scalarOnly])
    (by simp [gProgram, Proofs.GenericExtrema.selectionBody, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar])
    (by simp [inputs]) (by omega) rr ran ret cost need ps
  exact ⟨initial,fuel,callee,prepared,ran',st⟩

abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩


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
  scalarWork : out.scalars.work ≤ caller.scalars.work+47
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true

theorem finish_export (ins : List CppState.Binding) (m : Nat) (x : Int) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty ins (m+1) caller initial callee x)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gFields ty (ins.length+m))
        [] (gPerm ty targetConst) =
      some (exported ty x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState ty x caller initial (exported ty x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields ty (m+1) x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c5 : callee.scalarCell (ins.length+m) ty = some (⟨(callerP caller).length+m,true⟩,(cx ty x)) := by
    have hs : callee.scalarSlot (ins.length+m) = some (ins.length+m) := by
      simp [NState.scalarSlot, sl, ssl]
    have hb : callee.scalars.bindings[ins.length+m]? = some ⟨(callerP caller).length+m,true⟩ := by
      rw [bs, List.getElem?_append_right (by omega)]
      simp [fieldBindings]
    have hm : callee.scalars.memory[(callerP caller).length+m]? = some ⟨ty,x⟩ := by
      rw [mem, List.getElem?_append_right (by omega)]
      simp [fields]
    simp [NState.scalarCell, hs, hb, hm, cx, ready.xValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gFields ty (ins.length+m)) = some [((cx ty x),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨ins.length+m,ty⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty x),true)] (gPerm ty targetConst) =
      some (destinationValues ty x targetConst) := by
    cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, cx]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields ty (m+1) x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (gFields ty (ins.length+m))
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
  · change callee.scalars.work+0+(destinationValues ty x targetConst).length+1 ≤ caller.scalars.work+47
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



theorem view_export_correct (hij : (li = 0 ∧ ri = 1) ∨ (li = 1 ∧ ri = 0)) (caller : NState) (targetConst : Bool) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 ty = some (b2,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gProgram ty li ri).parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      gView ty li ri fuel caller [.scalarReference s1,.scalarReference s2] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty ((gExpected li ri) x y) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready hij caller s1 s2 b1 b2 x y c1 c2 valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export (inputs b1.address b2.address) 3 ((gExpected li ri) x y) caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty ((gExpected li ri) x y) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gProgram ty li ri) fuel caller initial callee _
    [.scalarReference s1,.scalarReference s2] [] (gFields ty 5) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (hij : (li = 0 ∧ ri = 1) ∨ (li = 1 ∧ ri = 0)) (caller : NState) (targetConst : Bool) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 ty = some (b2,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gProgram ty li ri).parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      gCombine ty li ri fuel caller [⟨[],[s1]⟩,⟨[],[s2]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty ((gExpected li ri) x y) caller initial out targetConst := by
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct hij caller targetConst s1 s2 b1 b2 x y c1 c2 valid lengths strict base
  have args : MemberFactory.referenceArguments caller [[(ty,false)],[(ty,false)]] [⟨[],[s1]⟩,⟨[],[s2]⟩] =
      some [.scalarReference s1,.scalarReference s2] := by
    simp [MemberFactory.referenceArguments,MemberFactory.referenceFields,c1,c2]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.referenceArguments caller [[(ty,false)],[(ty,false)]] [⟨[],[s1]⟩,⟨[],[s2]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => gView ty li ri fuel caller arguments targetConst) = _
  rw [args]
  exact ran


/-- `e()` (slot 1, two locals) and the default constructor (slot 2, three locals): a nullary
    program whose last local is exported; `ready` comes from the executed body. -/
theorem nullary_export_correct (body : Command) (m : Nat) (v : Int) (hv : ty.valid v = true)
    (hsc : Scalar body = true) (hal : CppScalarContents.Allowed body = true) (hm : m ≤ 3)
    (exec : ∀ P : List Cell, ∃ rr, pexec 1 body ⟨P,[]⟩ = some rr ∧ rr.ret = none ∧ rr.cost ≤ 40 ∧
      rr.need ≤ P.length + 16 ∧ rr.ps = Proofs.GroupCall.ws P [] (List.replicate (m+1) ⟨ty,v⟩))
    (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gNullary ty body).parameters [] = some initial ∧
      gNullaryView ty body m fuel caller [] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty v caller initial out targetConst := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_none caller (gNullary ty body).parameters rfl valid
  obtain ⟨rr,ran,ret,cost,need,ps⟩ := exec (callerP caller)
  obtain ⟨fuel,callee,ran',ready⟩ := stage_of_exec (ty := ty) (gNullary ty body) [] (m+1) v hv caller initial _ prepared
    (by simpa [ssl] using slots) mem bindings bas scope frame (by omega) peak valid lengths strict base hsc hal
    (by simp) (by omega) rr ran ret cost need (by simpa using ps)
  obtain ⟨fin,post⟩ := finish_export [] m v caller initial callee targetConst (by simpa using ready) base
  refine ⟨initial,fuel,exported ty v caller callee targetConst,prepared,?_,by simpa using post⟩
  have := MemberView.constructView_of_steps (gNullary ty body) fuel caller initial callee _
    [] [] (gFields ty m) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran' (Or.inl rfl) (by simpa using fin)
  exact this


theorem identity_export_correct (v : Int) (hv : ty.valid v = true) (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gNullary ty (Proofs.GenericExtrema.identBody ty v)).parameters [] = some initial ∧
      gNullaryView ty (Proofs.GenericExtrema.identBody ty v) 1 fuel caller [] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty v caller initial out targetConst :=
  nullary_export_correct (Proofs.GenericExtrema.identBody ty v) 1 v hv
    (by simp [Scalar, NExpr.scalarOnly]) (by simp [CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by omega)
    (fun P => by
      obtain ⟨r,ran,ret,cost,need,ps⟩ := Proofs.GenericExtrema.ident_exec ty P v hv
      rw [Proofs.GroupCall.ws_nil] at ran
      exact ⟨r,ran,ret,cost,need,ps⟩)
    caller targetConst valid lengths strict base

theorem default_export_correct (v : Int) (hv : ty.valid v = true) (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gNullary ty (Proofs.GenericExtrema.ctorBody ty v)).parameters [] = some initial ∧
      gNullaryView ty (Proofs.GenericExtrema.ctorBody ty v) 2 fuel caller [] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty v caller initial out targetConst :=
  nullary_export_correct (Proofs.GenericExtrema.ctorBody ty v) 2 v hv
    (by simp [Scalar, NExpr.scalarOnly]) (by simp [CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by omega)
    (fun P => by
      obtain ⟨r,ran,ret,cost,need,ps⟩ := Proofs.GenericExtrema.ctor_exec ty P v hv
      rw [Proofs.GroupCall.ws_nil] at ran
      exact ⟨r,ran,ret,cost,need,ps⟩)
    caller targetConst valid lengths strict base

theorem total_work (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x caller initial out targetConst) : out.work ≤ caller.work+47 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericExtremaCall
