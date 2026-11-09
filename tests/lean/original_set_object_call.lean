namespace SetObjectCallGeneral
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


open OriginalSetObject
open SetObjectGeneral
open Proofs.Mod61Body Proofs.CppScalarValuePrepare

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

def fieldCells (x f y g : Int) : List Cell :=
  inputs x f y g ++ [cf f,cx (selectedValue x f y),cx (selectedValue x f y),
    cf (selectedFlag f g),cf (selectedFlag f g)]
def fieldBindings (P : List Cell) : List CppState.Binding :=
  refs P ++ (List.range 4).map (fun i => ⟨P.length+5+i,true⟩)

structure StageState (caller initial callee : NState) (x f y g : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fieldCells x f y g) (fieldBindings (callerP caller)) (ssl 9)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+29) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  vValid : s64.valid (selectedValue x f y) = true
  nValid : bl.valid (selectedFlag f g) = true

theorem stage_ready (caller : NState) (x f y g : Int)
    (hx : s64.valid x = true) (hf : bl.valid f = true)
    (hy : s64.valid y = true) (hg : bl.valid g = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller RangeSet_factory_compose.parameters
        [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] = some initial ∧
      runFuel fuel RangeSet_factory_compose.body initial = .finished ⟨callee,none,false⟩ ∧
      StageState caller initial callee x f y g := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_literals4 s64 bl s64 bl caller RangeSet_factory_compose.parameters rfl x f y g hx hf hy hg valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec (callerP caller) x f y g hx hf hy hg
  have hv : s64.valid (selectedValue x f y) = true := by unfold selectedValue; split <;> assumption
  have hn : bl.valid (selectedFlag f g) = true := by unfold selectedFlag; split <;> assumption
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] (inputs x f y g)).mem (ws (callerP caller) [] (inputs x f y g)).bs (ssl 4) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,?_,?_,bas,scope⟩
    · simpa [ws,inputs,cx,cf] using mem
    · simpa [ws,inputs] using bindings
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] (inputs x f y g)).mem.length := by simp [ws,callerP,inputs]; omega
  have run := sound RangeSet_factory_compose.body (by decide) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,inputs]; unfold scalarBound; omega)
    (by rw [need]; unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState caller initial step.state x f y g := by
    refine ⟨?_,faD,?_,?_,hv,hn⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,ssl,inputs,refs,Nat.add_assoc] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work,cost] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel RangeSet_factory_compose.body initial step
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
abbrev cn (n : Int) : Cell := ⟨bl,n⟩


def destinationValues (x n : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx x),!targetConst),((cn n),!targetConst)]
def exported (x n : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues x n targetConst)

structure ExportState (x n : Int) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx x),(cn n)]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩,⟨caller.scalars.memory.length+1,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+32
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : s64.valid x = true
  nValid : bl.valid n = true

theorem finish_export (x f y g : Int) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState caller initial callee x f y g)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] OriginalSetObject.Stages.RangeSet_factory_compose.scalarFields
        [] (scalarPermissions targetConst) =
      some (exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState (selectedValue x f y) (selectedFlag f g) caller initial (exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells x f y g) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 6 s64 = some (⟨(callerP caller).length+6,true⟩,(cx (selectedValue x f y))) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputs,refs,cf,Nat.add_assoc,ssl,List.range_succ,cx,ready.vValid]
  have c5 : callee.scalarCell 8 bl = some (⟨(callerP caller).length+8,true⟩,(cn (selectedFlag f g))) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputs,refs,cf,Nat.add_assoc,ssl,List.range_succ,cn,ready.nValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      OriginalSetObject.Stages.RangeSet_factory_compose.scalarFields = some [((cx (selectedValue x f y)),true),((cn (selectedFlag f g)),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨6,s64⟩,⟨8,bl⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c4,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx (selectedValue x f y)),true),((cn (selectedFlag f g)),true)] (scalarPermissions targetConst) =
      some (destinationValues (selectedValue x f y) (selectedFlag f g) targetConst) := by cases targetConst <;> rfl
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells x f y g)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] OriginalSetObject.Stages.RangeSet_factory_compose.scalarFields
      [] (scalarPermissions targetConst) =
        some (exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
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
  have liveBound : caller.scalars.memory.length+2-caller.scalars.baseMemory+
      (caller.scalars.bindings.length+2) ≤ scalarBound caller initial := by
    unfold scalarBound
    have Psize : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    omega
  have sp : (exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.vValid,ready.nValid⟩
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
  · change callee.scalars.work+0+(destinationValues (selectedValue x f y) (selectedFlag f g) targetConst).length+1 ≤ caller.scalars.work+32
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst).scalars.peak+(exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst)
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

theorem destination_readable (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst) :
    out.scalarCell caller.slots.length s64 = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx x)) ∧
    out.scalarCell (caller.slots.length+1) bl = some (⟨caller.scalars.memory.length+1,!targetConst⟩,(cn n)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have s1 : out.slots[caller.slots.length+1]? = some (.scalar (caller.scalars.bindings.length+1)) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have b1 : out.scalars.bindings[caller.scalars.bindings.length+1]? = some ⟨caller.scalars.memory.length+1,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx x) := by rw [post.memory]; simp
  have m1 : out.scalars.memory[caller.scalars.memory.length+1]? = some (cn n) := by rw [post.memory]; simp
  constructor
  · simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]
  · simp [NState.scalarCell,NState.scalarSlot,s1,b1,m1,cn,post.nValid]

theorem frame_extension (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension x n caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension x n caller initial out targetConst post valid lengths) reference value found



theorem view_export_correct (caller : NState) (targetConst : Bool) (x f y g : Int)
    (hx : s64.valid x = true) (hf : bl.valid f = true)
    (hy : s64.valid y = true) (hg : bl.valid g = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller RangeSet_factory_compose.parameters
        [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] = some initial ∧
      RangeSet_factory_compose_exportViewFuel fuel caller
        [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState (selectedValue x f y) (selectedFlag f g) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller x f y g hx hf hy hg valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x f y g caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported (selectedValue x f y) (selectedFlag f g) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps RangeSet_factory_compose fuel caller initial callee _
    [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] []
    OriginalSetObject.Stages.RangeSet_factory_compose.scalarFields [] (scalarPermissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (x f y g : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,x⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,f⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,y⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,g⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller RangeSet_factory_compose.parameters
        [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] = some initial ∧
      RangeSet_factory_compose_exportObjectsFuel fuel caller [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState (selectedValue x f y) (selectedFlag f g) caller initial out targetConst := by
  obtain ⟨_,hx⟩ := caller_cell caller s1 s64 b1 x c1
  obtain ⟨_,hf⟩ := caller_cell caller s2 bl b2 f c2
  obtain ⟨_,hy⟩ := caller_cell caller s3 s64 b3 y c3
  obtain ⟨_,hg⟩ := caller_cell caller s4 bl b4 g c4
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst x f y g hx hf hy hg valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(true,[(s64,true),(bl,true)]),(true,[(s64,true),(bl,true)])] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] =
      some [.value (.literal s64 x),.value (.literal bl f),.value (.literal s64 y),.value (.literal bl g)] := by
    simp [MemberFactory.objectArguments,MemberFactory.valueFields,c1,c2,c3,c4]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
      [(true,[(s64,true),(bl,true)]),(true,[(s64,true),(bl,true)])] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => RangeSet_factory_compose_exportViewFuel fuel caller arguments targetConst) = _
  rw [args]; exact ran

theorem total_work (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x n caller initial out targetConst) : out.work ≤ caller.work+32 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end SetObjectCallGeneral
