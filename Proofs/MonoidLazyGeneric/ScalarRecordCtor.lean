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

open Proofs.CppScalar
namespace VPScalarRecordCtor
def vectorPermissions (_targetConst : Bool) : List Bool := []
end VPScalarRecordCtor
open VPScalarRecordCtor
namespace GenericScalarCtor
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


open Proofs.Mod61Body

theorem prepare_value1 (ty : Ty) (caller : NState) (params : List Proofs.CppVectorBindings.Parameter)
    (hp : params = [.scalar ty false true]) (e : NExpr) (v : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = ty)
    (de : e.denote (envOf caller) = some v)
    (valid : caller.frame.state.wellFormed = true) (hv : ty.valid v = true) :
    ∃ t, Good caller t e.nodes e.nodes ∧
      ∃ initial, prepare caller params [.value e] = some initial ∧
        initial.slots = [.scalar 0] ∧ initial.scalars.memory = callerP caller ++ [⟨ty,v⟩] ∧
        initial.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
        initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        initial.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ initial.scalars.peak := by
  obtain ⟨t,ran,g⟩ := scalar_eval e caller v he de
  refine ⟨t,g,?_⟩
  have fs : t.frame.state = caller.frame.state := by rw [g.1.1]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [g.1.1]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [g.1.1]
  have hm := g.1.2.2.2.1
  have hb := g.1.2.2.2.2.1
  have hbase := g.1.2.2.2.2.2
  have res : resolve caller (.scalar ty false true) (.value e) = some (t,.scalar ty true v) := by
    simp [resolve,ht,ran]
  rw [hp]
  simp [prepare,valid,resolveAll,res,fs,fr,fb,hm,hb,hbase,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  omega

abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
variable (ty : Ty)
def fieldCells (x : Int) : List Cell := [cx ty x,cx ty x]
def fieldBindings (P : List Cell) : List CppState.Binding :=
  (List.range 2).map fun i => ⟨P.length+i,true⟩
def rawBody : Command := .sequence (.primitive (.declare ty true (.variable ty 0))) Sk
def program : NProgram := ⟨[.scalar ty false true],.unit,rawBody ty⟩
def fields : List Proofs.CppConstructorFinish.ScalarField := [⟨1,ty⟩]
def permissions (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) := [(ty,(true && (!targetConst || false)))]
def view (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (program ty) fuel caller arguments [] (fields ty) (vectorPermissions targetConst) (permissions ty targetConst)
theorem body_shape : (program ty).body = rawBody ty := rfl

theorem raw_exec (P : List Cell) (x : Int) (hx : ty.valid x = true) :
    ∃ r, pexec 1 (program ty).body (ws P [] [cx ty x]) = some r ∧
      r.ret = none ∧ r.cost = 2 ∧ r.need = P.length+7 ∧ r.ps = ws P [] (fieldCells ty x) := by
  have dx : (NExpr.variable ty 0).denote (penv (ws P [] [cx ty x])) = some x := by
    rw [den_variable]; exact ws_env_loc P [] _ 0 (cx ty x) ty rfl rfl hx
  have q := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty x] ty (.variable ty 0) x dx (Ty.convert_of_valid _ _ hx))
  have run := seq_some q rfl (pexec_skip 1 _)
  refine ⟨⟨ws P [] (fieldCells ty x),none,2,P.length+7⟩,?_,rfl,rfl,rfl,rfl⟩
  simpa [body_shape,rawBody,ws,fieldCells,NExpr.nodes,Nat.add_assoc] using run

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+20-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat :=
  max caller.frame.state.storage.peak caller.frame.state.liveSpace

structure StageState (caller initial callee : NState) (x : Int) (E : Nat) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fieldCells ty x) (fieldBindings (callerP caller)) (ssl 2)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+E+4) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true

theorem stage_ready (caller : NState) (e1 : NExpr) (x : Int)
    (hs1 : e1.scalarOnly = true)
    (ht1 : e1.resultType = ty)
    (d1 : e1.denote (envOf caller) = some x)
    (hx : ty.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (program ty).parameters [.value e1] = some initial ∧
      runFuel fuel (program ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee x (e1.nodes) := by
  obtain ⟨t1,g1,initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_value1 ty caller (program ty).parameters rfl e1 x
      hs1 ht1 d1 valid hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty (callerP caller) x hx
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] [cx ty x]).mem (ws (callerP caller) [] [cx ty x]).bs (ssl 1) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,?_,?_,bas,scope⟩
    · simpa [ws,cx] using mem
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] [cx ty x]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound (program ty).body (by simp [program, rawBody, Scalar, NExpr.scalarOnly, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws]; unfold scalarBound; omega)
    (by rw [need]; unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state x (e1.nodes) := by
    refine ⟨?_,faD,?_,?_,hx⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,ssl] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      have w1 := g1.2.2.1
      rw [work,cost] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (program ty).body initial step
        (by simp [program, rawBody, Scalar, NExpr.scalarOnly, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
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
  [((cx ty x),!targetConst)]
def exported (x : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues ty x targetConst)

structure ExportState (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx ty x)]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 1
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+E+6
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true

theorem finish_export (x : Int) (E : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee x E)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (fields ty)
        [] (permissions ty targetConst) =
      some (exported ty x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
    ExportState ty x E caller initial (exported ty x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells ty x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c1 : callee.scalarCell 1 ty = some (⟨(callerP caller).length+1,true⟩,(cx ty x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,ssl,List.range_succ,cx,ready.xValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (fields ty) = some [((cx ty x),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨1,ty⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c1]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty x),true)] (permissions ty targetConst) =
      some (destinationValues ty x targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, permissions, destinationValues, cx]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells ty x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (fields ty)
      [] (permissions ty targetConst) =
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
  · change callee.scalars.work+0+(destinationValues ty x targetConst).length+1 ≤ caller.scalars.work+E+6
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty x caller callee targetConst).scalars.peak+(exported ty x caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x E caller initial out targetConst)
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
    (post : ExportState ty x E caller initial out targetConst) :
    out.scalarCell caller.slots.length ty = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx ty x)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx ty x) := by rw [post.memory]; simp
  simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]

theorem frame_extension (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x E caller initial out targetConst)
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
    (post : ExportState ty x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension ty x E caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension ty x E caller initial out targetConst post valid lengths) reference value found


theorem value_construct_correct (caller : NState) (targetConst : Bool) (e1 : NExpr) (x : Int)
    (hs1 : e1.scalarOnly = true)
    (ht1 : e1.resultType = ty)
    (d1 : e1.denote (envOf caller) = some x)
    (hx : ty.valid x = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program ty).parameters [.value e1] = some initial ∧
      (view ty) fuel caller [.value e1] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ExportState ty x (e1.nodes) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready ty caller e1 x
    hs1 ht1 d1 hx valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export ty x (e1.nodes) caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty x caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (program ty) fuel caller initial callee _ [.value e1] []
    (fields ty) [] (permissions ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl) fin

theorem total_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x E caller initial out targetConst) : out.work ≤ caller.work+E+6 := by
  have hw := post.scalarWork
  have hs := post.storageWork
  simp only [NState.work]
  omega

end GenericScalarCtor

