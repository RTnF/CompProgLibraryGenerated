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
namespace VPSumDefaultCtor
def vectorPermissions (_targetConst : Bool) : List Bool := []
end VPSumDefaultCtor
open VPSumDefaultCtor
namespace GenericDefaultCtor
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

abbrev z64 (ty : Ty) : Cell := ⟨ty,0⟩
abbrev z32 : Cell := ⟨i32,0⟩
variable (ty : Ty)
def fieldCells : List Cell := [(z64 ty),z32,(z64 ty),z32,(z64 ty),z32]
def fieldBindings (P : List Cell) : List CppState.Binding :=
  (List.range 6).map fun i => ⟨P.length+i,true⟩
def rawBody : Command :=
  .sequence (.primitive (.declare ty true (Proofs.GenericLazy.castTo ty i32 (.literal i32 0))))
    (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.primitive (.declare ty true (.variable ty 0)))
        (.sequence (.primitive (.declare i32 true (.variable i32 1)))
          (.sequence (.scope Sk)
            (.sequence (.primitive (.declare ty true (.variable ty 2)))
              (.sequence (.primitive (.declare i32 true (.variable i32 3))) Sk))))))


variable (ty : Ty)
def gDefaultCtor : NProgram := ⟨[], .unit, rawBody ty⟩
def gFields : List Proofs.CppConstructorFinish.ScalarField := [⟨4,ty⟩,⟨5,i32⟩]
def gPerm (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(i32,(true && (!targetConst || false)))]
def gView (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gDefaultCtor ty) fuel caller arguments [] (gFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)


theorem raw_exec (P : List Cell) :
    ∃ r, pexec 1 (gDefaultCtor ty).body ⟨P,[]⟩ = some r ∧ r.ret = none ∧
      r.cost ≤ 14 ∧ r.need ≤ P.length+15 ∧ r.ps = ws P [] (fieldCells ty) := by
  let L1 : List Cell := [(z64 ty)]
  let L2 : List Cell := [(z64 ty),z32]
  let L3 : List Cell := [(z64 ty),z32,(z64 ty)]
  let L4 : List Cell := [(z64 ty),z32,(z64 ty),z32]
  let L5 : List Cell := [(z64 ty),z32,(z64 ty),z32,(z64 ty)]
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] ty (Proofs.GenericLazy.castTo ty i32 (.literal i32 0)) 0 (Proofs.GenericLazy.R0z_gen ty _) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] L1 i32 (.literal i32 0) 0 rfl rfl)
  have dx1 : (NExpr.variable ty 0).denote (penv (ws P [] L2)) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] L2 0 (z64 ty) ty rfl rfl (Proofs.GenericLazy.valid_zero ty)
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P [] L2 ty (.variable ty 0) 0 dx1 (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have dz1 : (NExpr.variable i32 1).denote (penv (ws P [] L3)) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] L3 1 z32 i32 rfl rfl rfl
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P [] L3 i32 (.variable i32 1) 0 dz1 rfl)
  have sc0 := pexec_scope 1 Sk (ws P [] L4) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P [] L4) = some ⟨ws P [] L4,none,1,P.length+8⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,L4,Nat.add_assoc] using sc0
  have dx2 : (NExpr.variable ty 2).denote (penv (ws P [] L4)) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] L4 2 (z64 ty) ty rfl rfl (Proofs.GenericLazy.valid_zero ty)
  have q4 := (pexec_prim 1 _ _).trans (ws_declare P [] L4 ty (.variable ty 2) 0 dx2 (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have dz2 : (NExpr.variable i32 3).denote (penv (ws P [] L5)) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] L5 3 z32 i32 rfl rfl rfl
  have q5 := (pexec_prim 1 _ _).trans (ws_declare P [] L5 i32 (.variable i32 3) 0 dz2 rfl)
  have whole := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl
    (seq_some sc rfl (seq_some q4 rfl (seq_some q5 rfl (pexec_skip 1 _)))))))
  have hn' := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
  simp only [NExpr.nodes] at hn'
  refine ⟨_,by simpa [gDefaultCtor,rawBody,ws,fieldCells,L1,L2,L3,L4,L5,NExpr.nodes,Nat.add_assoc] using whole,rfl,?h3,?h4,rfl⟩
  · simp [NExpr.nodes,ws,fieldCells] <;> omega
  · simp [NExpr.nodes,ws,fieldCells] <;> omega

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+12-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat :=
  max caller.frame.state.storage.peak caller.frame.state.liveSpace

structure StageState (caller initial callee : NState) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ (fieldCells ty)) (fieldBindings (callerP caller)) (ssl 6)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+15) callee
  contents : CppScalarContents.Contents caller.frame callee.frame

theorem stage_ready (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gDefaultCtor ty).parameters [] = some initial ∧
      runFuel fuel (gDefaultCtor ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_none caller (gDefaultCtor ty).parameters rfl valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty (callerP caller)
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1) (callerP caller) [] (ssl 0) :=
    ⟨by simpa [ssl] using slots,by simpa using mem,bindings,bas,scope⟩
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
      rw [frame]
      change caller.frame.state.storage.peak ≤ storageBound caller
      unfold storageBound; omega
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (callerP caller).length := by simp [callerP]; omega
  have run := sound (gDefaultCtor ty).body (by simp [gDefaultCtor, rawBody, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl, Scalar, NExpr.scalarOnly]) 1 ⟨callerP caller,[]⟩ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp only [List.length_nil,Nat.add_zero]; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by unfold storageBound; omega)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state := by
    refine ⟨?_,faD,?_,?_⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (gDefaultCtor ty).body initial step
        (by simp [gDefaultCtor, rawBody, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)

def destinationValues (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((z64 ty),!targetConst),(z32,!targetConst)]
def exported (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues ty targetConst)

structure ExportState (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(z64 ty),z32]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩,⟨caller.scalars.memory.length+1,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+18
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame

theorem finish_export (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty caller initial (exported ty caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells ty) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 4 ty = some (⟨(callerP caller).length+4,true⟩,(z64 ty)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,ssl,List.range_succ,z64]
    exact Proofs.GenericLazy.valid_zero ty
  have c5 : callee.scalarCell 5 i32 = some (⟨(callerP caller).length+5,true⟩,z32) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,ssl,List.range_succ,z32]
    rfl
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gFields ty) = some [((z64 ty),true),(z32,true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨4,ty⟩,⟨5,i32⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c4,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((z64 ty),true),(z32,true)] (gPerm ty targetConst) =
      some (destinationValues ty targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, z64, z32]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells ty)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (gFields ty)
      [] (gPerm ty targetConst) =
        some (exported ty caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
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
  have sp : (exported ty caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported ty caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_⟩
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
  · change callee.scalars.work+0+(destinationValues ty targetConst).length+1 ≤ caller.scalars.work+18
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty caller callee targetConst).scalars.peak+(exported ty caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem default_construct_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gDefaultCtor ty).parameters [] = some initial ∧
      (gView ty) fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready ty caller valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export ty caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gDefaultCtor ty) fuel caller initial callee _ [] []
    (gFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem existing_scalar_read (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty caller initial out targetConst)
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

theorem destination_readable (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty caller initial out targetConst) :
    out.scalarCell caller.slots.length ty = some (⟨caller.scalars.memory.length,!targetConst⟩,(z64 ty)) ∧
    out.scalarCell (caller.slots.length+1) i32 = some (⟨caller.scalars.memory.length+1,!targetConst⟩,z32) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have s1 : out.slots[caller.slots.length+1]? = some (.scalar (caller.scalars.bindings.length+1)) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have b1 : out.scalars.bindings[caller.scalars.bindings.length+1]? = some ⟨caller.scalars.memory.length+1,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (z64 ty) := by rw [post.memory]; simp
  have m1 : out.scalars.memory[caller.scalars.memory.length+1]? = some z32 := by rw [post.memory]; simp
  constructor
  · simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,z64]; exact Proofs.GenericLazy.valid_zero ty
  · simp [NState.scalarCell,NState.scalarSlot,s1,b1,m1,z32]; rfl

theorem frame_extension (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension ty caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension ty caller initial out targetConst post valid lengths) reference value found

end GenericDefaultCtor

