namespace ExtremaObjectCallGeneral
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


open OriginalExtremaObject SelectedExtrema
open Proofs.Mod61Body

def inputs (a b : Nat) : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩]
def fields (x : Int) : List Cell := List.replicate 4 ⟨s64,x⟩

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
  (List.range 4).map fun i => ⟨P.length+i,true⟩

structure StageState (caller initial callee : NState) (a b : Nat) (x : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields x) (inputs a b ++ fieldBindings (callerP caller)) (ssl 6)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+45) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : s64.valid x = true

theorem stage_ready (caller : NState) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,x⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee,
      prepare caller program.parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      runFuel fuel program.body initial = .finished ⟨callee,none,false⟩ ∧
      StageState caller initial callee b1.address b2.address (expected x y) := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_ref2 caller program.parameters s64 false false rfl s1 s2 b1 b2 x y c1 c2 (by simp) (by simp) valid
  obtain ⟨p0,hx⟩ := caller_cell caller s1 s64 b1 x c1
  obtain ⟨p1,hy⟩ := caller_cell caller s2 s64 b2 y c2
  have hv : s64.valid (expected x y) = true := by
    rw [← expected_value]
    by_cases h : (if leftIndex = 0 then x else y) < (if rightIndex = 0 then x else y)
    · rw [ite_eq_left h]; exact hy
    · rw [ite_eq_right h]; exact hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := ExtremaObjectAudit.source_raw_exec (callerP caller)
    b1.address b2.address x y hx hy p0 p1
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1) (callerP caller)
      (inputs b1.address b2.address) (ssl 2) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,mem,bindings,bas,scope⟩
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
  have run := sound program.body (by decide) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState caller initial step.state b1.address b2.address (expected x y) := by
    refine ⟨?_,faD,?_,?_,hv⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl,inputs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel program.body initial step
        (by decide) (by intro owner sc found; rw [frame] at found; have h := strict owner sc found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)

abbrev cx (x : Int) : Cell := ⟨s64,x⟩


def destinationValues (x : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx x),!targetConst)]
def exported (x : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues x targetConst)

structure ExportState (x : Int) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx x)]
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
  xValid : s64.valid x = true

theorem finish_export (x : Int) (a b : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState caller initial callee a b x)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] selectedFields
        [] (scalarPermissions targetConst) =
      some (exported x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState x caller initial (exported x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c5 : callee.scalarCell 5 s64 = some (⟨(callerP caller).length+3,true⟩,(cx x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,inputs,ssl,List.range_succ,cx,ready.xValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      selectedFields = some [((cx x),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨5,s64⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx x),true)] (scalarPermissions targetConst) =
      some (destinationValues x targetConst) := by cases targetConst <;> rfl
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] selectedFields
      [] (scalarPermissions targetConst) =
        some (exported x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) := by
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
  have sp : (exported x caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+1-caller.scalars.baseMemory+(caller.scalars.bindings.length+1)+0) ≤ _
    omega
  have tp : (exported x caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
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
  · change callee.scalars.work+0+(destinationValues x targetConst).length+1 ≤ caller.scalars.work+47
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported x caller callee targetConst).scalars.peak+(exported x caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x caller initial out targetConst)
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
    (post : ExportState x caller initial out targetConst) :
    out.scalarCell caller.slots.length s64 = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx x)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx x) := by rw [post.memory]; simp
  simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]

theorem frame_extension (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x caller initial out targetConst)
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
    (post : ExportState x caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension x caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension x caller initial out targetConst post valid lengths) reference value found



theorem view_export_correct (caller : NState) (targetConst : Bool) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,x⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller program.parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      viewExport fuel caller [.scalarReference s1,.scalarReference s2] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (expected x y) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller s1 s2 b1 b2 x y c1 c2 valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export (expected x y) b1.address b2.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported (expected x y) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps program fuel caller initial callee _
    [.scalarReference s1,.scalarReference s2] [] selectedFields [] (scalarPermissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,x⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller program.parameters [.scalarReference s1,.scalarReference s2] = some initial ∧
      combineExport fuel caller [⟨[],[s1]⟩,⟨[],[s2]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (expected x y) caller initial out targetConst := by
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst s1 s2 b1 b2 x y c1 c2 valid lengths strict base
  have args : MemberFactory.referenceArguments caller [[(s64,false)],[(s64,false)]] [⟨[],[s1]⟩,⟨[],[s2]⟩] =
      some [.scalarReference s1,.scalarReference s2] := by
    simp [MemberFactory.referenceArguments,MemberFactory.referenceFields,c1,c2]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.referenceArguments caller [[(s64,false)],[(s64,false)]] [⟨[],[s1]⟩,⟨[],[s2]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => viewExport fuel caller arguments targetConst) = _
  rw [args]
  exact ran

theorem total_work (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x caller initial out targetConst) : out.work ≤ caller.work+47 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end ExtremaObjectCallGeneral
