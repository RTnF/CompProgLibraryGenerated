namespace ExtremaSetMemberCallGeneral
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
open ExtremaSetMemberGeneral
open ExtremaPrepareGeneral
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩

abbrev cx (x : Int) : Cell := ⟨s64,x⟩

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
def fields (old x : Int) : List Cell := [cx old,cx x]
structure StageState (caller initial callee : NState) (a b : Nat) (old x : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields old x) (refs a b ++ fieldBindings (callerP caller)) (ssl 4)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+19) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : s64.valid x = true

theorem stage_ready (caller : NState) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot s64 = some (binding,cx v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (hx : s64.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller SelectedExtrema.applyProgram.parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] = some initial ∧
      runFuel fuel SelectedExtrema.applyProgram.body initial = .finished ⟨callee,none,false⟩ ∧
      StageState caller initial callee binding.address flagBinding.address x (selected v f x) := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references2_value1 caller SelectedExtrema.applyProgram.parameters s64 bl s64 rfl
      receiverSlot flagSlot binding flagBinding v f x found writable flagFound flagWritable hx valid
  obtain ⟨receiver,hv⟩ := caller_cell caller receiverSlot s64 binding v found
  obtain ⟨flag,hf⟩ := caller_cell caller flagSlot bl flagBinding f flagFound
  have hs : s64.valid (selected v f x) = true := by
    unfold selected
    split
    · exact hv
    · exact hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := ExtremaSetMemberGeneral.raw_exec (callerP caller) binding.address flagBinding.address v f x receiver flag hv hf hx
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx x]).mem
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx x]).bs (ssl 3) := by
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) (refs binding.address flagBinding.address) [cx x]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound SelectedExtrema.applyProgram.body (by decide) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,refs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState caller initial step.state binding.address flagBinding.address x (selected v f x) := by
    refine ⟨?_,faD,?_,?_,hs⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl,refs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work,cost] at bound
      split at bound <;> omega
    · have stable := CppScalarContents.run_stable fuel SelectedExtrema.applyProgram.body initial step
        (by decide) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)
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
  scalarWork : out.scalars.work ≤ caller.scalars.work+21
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : s64.valid x = true

theorem finish_export (old x : Int) (a b : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState caller initial callee a b old x)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] SelectedExtrema.applyFields
        [] (SelectedExtrema.scalarPermissions targetConst) =
      some (exported x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState x caller initial (exported x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields old x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c2 : callee.scalarCell 3 s64 = some (⟨(callerP caller).length+1,true⟩,(cx x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cx,ready.xValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      SelectedExtrema.applyFields = some [((cx x),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨3,s64⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c2]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx x),true)] (SelectedExtrema.scalarPermissions targetConst) =
      some (destinationValues x targetConst) := by cases targetConst <;> rfl
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields old x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] SelectedExtrema.applyFields
      [] (SelectedExtrema.scalarPermissions targetConst) =
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
  · change callee.scalars.work+0+(destinationValues x targetConst).length+1 ≤ caller.scalars.work+21
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



theorem view_export_correct (caller : NState) (targetConst : Bool) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot s64 = some (binding,cx v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (hx : s64.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller SelectedExtrema.applyProgram.parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] = some initial ∧
      SelectedExtrema.applyView fuel caller
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (selected v f x) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller receiverSlot flagSlot binding flagBinding v f x
    found writable flagFound flagWritable hx valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x (selected v f x) binding.address flagBinding.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported (selected v f x) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps SelectedExtrema.applyProgram fuel caller initial callee _
    [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] []
    SelectedExtrema.applyFields [] (SelectedExtrema.scalarPermissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool)
    (receiverSlot flagSlot xSlot : Nat) (binding flagBinding bx : CppState.Binding) (v f x : Int)
    (found : caller.scalarCell receiverSlot s64 = some (binding,cx v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,cf f))
    (flagWritable : flagBinding.writable = true)
    (sourceX : caller.scalarCell xSlot s64 = some (bx,cx x))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller SelectedExtrema.applyProgram.parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] = some initial ∧
      SelectedExtrema.applyObjects fuel caller
        [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (selected v f x) caller initial out targetConst := by
  have hx := (caller_cell caller xSlot s64 bx x sourceX).2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst receiverSlot flagSlot binding flagBinding v f x
    found writable flagFound flagWritable hx valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(false,[(s64,true),(bl,true)]),(true,[(s64,true)])]
      [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] =
        some [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal s64 x)] := by
    simp [MemberFactory.objectArguments,MemberFactory.referenceFields,MemberFactory.valueFields,
      found,flagFound,sourceX,writable,flagWritable,cx,cf]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
    [(false,[(s64,true),(bl,true)]),(true,[(s64,true)])]
    [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => SelectedExtrema.applyView fuel caller arguments targetConst) = _
  rw [args]
  exact ran

theorem total_work (x : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x caller initial out targetConst) : out.work ≤ caller.work+21 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end ExtremaSetMemberCallGeneral
