namespace ValueAddCallGeneral
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


open OriginalValueAdd
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

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

abbrev cx (x : Int) : Cell := ⟨s64,x⟩
def fieldCells (x y : Int) : List Cell := [cx x,cx y,cx (x+y),cx (x+y)]
def add64 : NExpr := .binary s64 .add (.variable s64 0) (.variable s64 1)
def rawBody : Command :=
  .sequence (.primitive (.declare s64 true add64))
    (.sequence (.primitive (.declare s64 true (.variable s64 2))) (.sequence (.scope Sk) Sk))
theorem body_shape : RangeAdd_factory_compose.body = rawBody := rfl

theorem raw_exec (P : List Cell) (x y : Int)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (hs : s64.valid (x+y) = true) :
    ∃ r, pexec 1 RangeAdd_factory_compose.body (ws P [] [cx x,cx y]) = some r ∧
      r.ret = none ∧ r.cost = 7 ∧ r.need = P.length+11 ∧
      r.ps = ws P [] (fieldCells x y) := by
  let L2 : List Cell := [cx x,cx y]
  let L3 : List Cell := [cx x,cx y,cx (x+y)]
  let L4 := fieldCells x y
  have e0 : penv (ws P [] L2) 0 s64 = some x := ws_env_loc P [] L2 0 (cx x) s64 rfl rfl hx
  have e1 : penv (ws P [] L2) 1 s64 = some y := ws_env_loc P [] L2 1 (cx y) s64 rfl rfl hy
  have d0 : add64.denote (penv (ws P [] L2)) = some (x+y) := by
    unfold add64
    rw [den_binary,den_variable,den_variable,e0,e1]
    simpa [binaryValue] using Ty.convert_of_valid s64 (x+y) hs
  have d1 : (NExpr.variable s64 2).denote (penv (ws P [] L3)) = some (x+y) := by
    rw [den_variable]
    exact ws_env_loc P [] L3 2 (cx (x+y)) s64 rfl rfl hs
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] L2 s64 add64 (x+y) d0 (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] L3 s64 (.variable s64 2) (x+y) d1 (Ty.convert_of_valid _ _ hs))
  have sc0 := pexec_scope 1 Sk (ws P [] L4) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P [] L4) = some ⟨ws P [] L4,none,1,P.length+8⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,L4,fieldCells,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
  refine ⟨⟨ws P [] L4,none,7,P.length+11⟩,?_,rfl,rfl,rfl,rfl⟩
  rw [body_shape]
  simpa [rawBody,ws,L2,L3,L4,fieldCells,add64,NExpr.nodes,Nat.add_assoc] using all

structure StageState (caller initial callee : NState) (x y : Int) (E : Nat) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fieldCells x y) (fieldBindings (callerP caller)) (ssl 4)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+E+10) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : s64.valid x = true
  yValid : s64.valid y = true
  sumValid : s64.valid (x+y) = true

theorem stage_ready (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hn : s64.valid y = true) (hs : s64.valid (x+y) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller RangeAdd_factory_compose.parameters [.value e1,.value e2] = some initial ∧
      runFuel fuel RangeAdd_factory_compose.body initial = .finished ⟨callee,none,false⟩ ∧
      StageState caller initial callee x y (e1.nodes+e2.nodes) := by
  obtain ⟨t1,t2,g1,g2,initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_values2 s64 s64 caller RangeAdd_factory_compose.parameters rfl e1 e2 x y
      hs1 hs2 ht1 ht2 d1 d2 valid hx hn
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec (callerP caller) x y hx hn hs
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] [cx x,cx y]).mem (ws (callerP caller) [] [cx x,cx y]).bs (ssl 2) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,?_,?_,bas,scope⟩
    · simpa [ws,cx,cn] using mem
    · simpa [ws,List.range_succ] using bindings
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] [cx x,cx y]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound RangeAdd_factory_compose.body (by decide) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws]; unfold scalarBound; omega)
    (by rw [need]; unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState caller initial step.state x y (e1.nodes+e2.nodes) := by
    refine ⟨?_,faD,?_,?_,hx,hn,hs⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,ssl] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      have w1 := g1.2.2.1
      have w2 := g2.2.2.1
      rw [work,cost] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel RangeAdd_factory_compose.body initial step
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

structure ExportState (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx x)]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 1
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+E+12
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : s64.valid x = true

theorem finish_export (x y : Int) (E : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState caller initial callee x y E)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] OriginalValueAdd.Stages.RangeAdd_factory_compose.scalarFields
        [] (scalarPermissions targetConst) =
      some (exported (x+y) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState (x+y) E caller initial (exported (x+y) caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells x y) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c5 : callee.scalarCell 3 s64 = some (⟨(callerP caller).length+3,true⟩,(cx (x+y))) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,ssl,List.range_succ,cx,ready.sumValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      OriginalValueAdd.Stages.RangeAdd_factory_compose.scalarFields = some [((cx (x+y)),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨3,s64⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx (x+y)),true)] (scalarPermissions targetConst) =
      some (destinationValues (x+y) targetConst) := by cases targetConst <;> rfl
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells x y)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] OriginalValueAdd.Stages.RangeAdd_factory_compose.scalarFields
      [] (scalarPermissions targetConst) =
        some (exported (x+y) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) := by
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
  have sp : (exported (x+y) caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+1-caller.scalars.baseMemory+(caller.scalars.bindings.length+1)+0) ≤ _
    omega
  have tp : (exported (x+y) caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.sumValid⟩
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
  · change callee.scalars.work+0+(destinationValues (x+y) targetConst).length+1 ≤ caller.scalars.work+E+12
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported (x+y) caller callee targetConst).scalars.peak+(exported (x+y) caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x E caller initial out targetConst)
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

theorem destination_readable (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x E caller initial out targetConst) :
    out.scalarCell caller.slots.length s64 = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx x)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx x) := by rw [post.memory]; simp
  simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]

theorem frame_extension (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension x E caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension x E caller initial out targetConst post valid lengths) reference value found



theorem value_compose_correct (caller : NState) (targetConst : Bool) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (hs : s64.valid (x+y) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller RangeAdd_factory_compose.parameters [.value e1,.value e2] = some initial ∧
      RangeAdd_factory_compose_exportViewFuel fuel caller [.value e1,.value e2] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (x+y) (e1.nodes+e2.nodes) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller e1 e2 x y
    hs1 hs2 ht1 ht2 d1 d2 hx hy hs valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x y (e1.nodes+e2.nodes) caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported (x+y) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps RangeAdd_factory_compose fuel caller initial callee _ [.value e1,.value e2] []
    OriginalValueAdd.Stages.RangeAdd_factory_compose.scalarFields [] (scalarPermissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem object_compose_correct (caller : NState) (targetConst : Bool) (s1 s2 : Nat)
    (b1 b2 : CppState.Binding) (x y : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,x⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,y⟩))
    (hs : s64.valid (x+y) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller RangeAdd_factory_compose.parameters
        [.value (.literal s64 x),.value (.literal s64 y)] = some initial ∧
      RangeAdd_factory_compose_exportObjectsFuel fuel caller [⟨[],[s1]⟩,⟨[],[s2]⟩] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState (x+y) 2 caller initial out targetConst := by
  obtain ⟨_,hx⟩ := caller_cell caller s1 s64 b1 x c1
  obtain ⟨_,hy⟩ := caller_cell caller s2 s64 b2 y c2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := value_compose_correct caller targetConst
    (.literal s64 x) (.literal s64 y) x y rfl rfl rfl rfl
    (by simp [NExpr.denote,hx])
    (by simp [NExpr.denote,hy])
    hx hy hs valid lengths strict base
  have args : MemberFactory.objectArguments caller [(true,[(s64,true)]),(true,[(s64,true)])]
      [⟨[],[s1]⟩,⟨[],[s2]⟩] = some [.value (.literal s64 x),.value (.literal s64 y)] := by
    simp [MemberFactory.objectArguments,MemberFactory.valueFields,c1,c2]
  refine ⟨initial,fuel,out,prepared,?_,?_⟩
  · change (match MemberFactory.objectArguments caller [(true,[(s64,true)]),(true,[(s64,true)])]
      [⟨[],[s1]⟩,⟨[],[s2]⟩] with
      | none => Proofs.CppLoop.Outcome.fault
      | some arguments => RangeAdd_factory_compose_exportViewFuel fuel caller arguments targetConst) = _
    rw [args]; exact ran
  · simpa [NExpr.nodes] using post

theorem total_work (v : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState v E caller initial out targetConst) : out.work ≤ caller.work+E+12 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end ValueAddCallGeneral
