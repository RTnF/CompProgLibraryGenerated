namespace SetRecordConstructorGeneral
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


open ValueObject
open Proofs.Mod61Body

abbrev bl : Ty := ⟨1,false,true⟩
abbrev cx (x : Int) : Cell := ⟨s64,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
inductive Mode where
  | value | defaulted | identity
  deriving DecidableEq
def program : Mode → NProgram
  | .value => SelectedSet.valueProgram
  | .defaulted => SelectedSet.defaultProgram
  | .identity => SelectedSet.idProgram
def view : Mode → Nat → NState → List NArgument → Bool → Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef)
  | .value => SelectedSet.valueView
  | .defaulted => SelectedSet.defaultView
  | .identity => SelectedSet.idView
def fields : Mode → List Proofs.CppConstructorFinish.ScalarField
  | .value => SelectedSet.valueFields
  | .defaulted => SelectedSet.defaultFields
  | .identity => SelectedSet.idFields
def argCount : Mode → Nat | .value => 1 | _ => 0
def arguments : Mode → NExpr → List NArgument | .value,e => [.value e] | _,_ => []
def inputCells : Mode → Int → List Cell | .value,x => [cx x] | _,_ => []
def outputValue : Mode → Int → Int | .value,x => x | _,_ => 0
def flag : Mode → Int | .value => 0 | _ => 1
def fieldCells (mode : Mode) (x : Int) : List Cell :=
  inputCells mode x ++ [cx (outputValue mode x),cf (flag mode)]
def fieldBindings (P : List Cell) (count : Nat) : List CppState.Binding :=
  (List.range count).map fun i => ⟨P.length+i,true⟩
def rawWork : Mode → Nat | .value => 4 | .defaulted => 5 | .identity => 6
def rawNeed : Mode → Nat | .value => 9 | _ => 7
def prepWork : Mode → Nat → Nat | .value,E => E+2 | _,_ => 1
def stageWork (mode : Mode) (E : Nat) : Nat := prepWork mode E+rawWork mode
def inputExpr : Mode → NExpr | .value => .variable s64 0 | _ => .cast s64 (.literal i32 0)
def tail : Mode → Command | .identity => .sequence (.scope Sk) Sk | _ => Sk
def rawBody (mode : Mode) : Command := .sequence (.primitive (.declare s64 true (inputExpr mode)))
  (.sequence (.primitive (.declare bl true (.literal bl (flag mode)))) (tail mode))
theorem body_shape (mode : Mode) : (program mode).body = rawBody mode := by cases mode <;> rfl
theorem fields_shape (mode : Mode) : fields mode = [⟨argCount mode,s64⟩,⟨argCount mode+1,bl⟩] := by cases mode <;> rfl
theorem scalar_body (mode : Mode) : Scalar (program mode).body = true := by cases mode <;> decide
theorem allowed_body (mode : Mode) : CppScalarContents.Allowed (program mode).body = true := by cases mode <;> decide
theorem flag_valid (mode : Mode) : bl.valid (flag mode) = true := by cases mode <;> decide
theorem value_valid (mode : Mode) (x : Int) (hx : s64.valid x = true) :
    s64.valid (outputValue mode x) = true := by cases mode with
  | value => exact hx
  | defaulted => change s64.valid 0 = true; rfl
  | identity => change s64.valid 0 = true; rfl
theorem input_length (mode : Mode) (x : Int) : (inputCells mode x).length = argCount mode := by cases mode <;> rfl
theorem arg_count_bound (mode : Mode) : argCount mode ≤ 1 := by cases mode <;> decide
theorem raw_need_bound (mode : Mode) : rawNeed mode ≤ 9 := by cases mode <;> decide

theorem raw_exec (mode : Mode) (P : List Cell) (x : Int) (hx : s64.valid x = true) :
    ∃ r, pexec 1 (program mode).body (ws P [] (inputCells mode x)) = some r ∧
      r.ret = none ∧ r.cost = rawWork mode ∧ r.need = P.length+rawNeed mode ∧
      r.ps = ws P [] (fieldCells mode x) := by
  cases mode with
  | value =>
    have dx : (NExpr.variable s64 0).denote (penv (ws P [] [cx x])) = some x := by
      rw [den_variable]; exact ws_env_loc P [] _ 0 (cx x) s64 rfl rfl hx
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx x] s64 (.variable s64 0) x dx (Ty.convert_of_valid _ _ hx))
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx x,cx x] bl (.literal bl 0) 0 rfl rfl)
    have run := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    refine ⟨⟨ws P [] [cx x,cx x,cf 0],none,4,P.length+9⟩,?_,rfl,rfl,rfl,rfl⟩
    simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc] using run
  | defaulted =>
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] s64 (.cast s64 (.literal i32 0)) 0 rfl rfl)
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx 0] bl (.literal bl 1) 1 rfl rfl)
    have run := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    refine ⟨⟨ws P [] [cx 0,cf 1],none,5,P.length+7⟩,?_,rfl,rfl,rfl,rfl⟩
    simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc] using run
  | identity =>
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] s64 (.cast s64 (.literal i32 0)) 0 rfl rfl)
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx 0] bl (.literal bl 1) 1 rfl rfl)
    have sc0 := pexec_scope 1 Sk (ws P [] [cx 0,cf 1]) _ (pexec_skip 1 _)
    have sc : pexec 1 (.scope Sk) (ws P [] [cx 0,cf 1]) = some ⟨ws P [] [cx 0,cf 1],none,1,P.length+4⟩ := by
      simp only [List.take_length] at sc0
      simpa [ws] using sc0
    have run := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
    refine ⟨⟨ws P [] [cx 0,cf 1],none,6,P.length+7⟩,?_,rfl,rfl,rfl,rfl⟩
    simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc] using run

theorem prepare_entry (mode : Mode) (caller : NState) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = s64) (de : e.denote (envOf caller) = some x)
    (hx : s64.valid x = true) (valid : caller.frame.state.wellFormed = true) :
    ∃ initial, prepare caller (program mode).parameters (arguments mode e) = some initial ∧
      initial.slots = ssl (argCount mode) ∧ initial.scalars.memory = callerP caller ++ inputCells mode x ∧
      initial.scalars.bindings = fieldBindings (callerP caller) (argCount mode) ∧
      initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
      initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      initial.scalars.work ≤ caller.scalars.work+prepWork mode e.nodes := by
  cases mode with
  | value =>
    obtain ⟨t,g,initial,prepared,slots,mem,bindings,base,scope,frame,work,peak,_⟩ :=
      prep_val caller (program .value).parameters s64 rfl e x he ht de valid hx
    refine ⟨initial,prepared,?_,mem,?_,base,scope,frame,?_⟩
    · simpa [ssl,argCount,List.range_succ] using slots
    · simpa [fieldBindings,argCount,List.range_succ] using bindings
    · have bound := g.2.2.1
      rw [work]
      change t.scalars.work+2 ≤ caller.scalars.work+(e.nodes+2)
      omega
  | defaulted =>
    obtain ⟨initial,prepared,slots,mem,bindings,base,scope,frame,work,_⟩ := prep_none caller (program .defaulted).parameters rfl valid
    refine ⟨initial,prepared,?_,?_,?_,base,scope,frame,?_⟩
    · simpa [ssl,argCount] using slots
    · simpa [inputCells] using mem
    · simpa [fieldBindings,argCount] using bindings
    · rw [work]; exact Nat.le_refl _
  | identity =>
    obtain ⟨initial,prepared,slots,mem,bindings,base,scope,frame,work,_⟩ := prep_none caller (program .identity).parameters rfl valid
    refine ⟨initial,prepared,?_,?_,?_,base,scope,frame,?_⟩
    · simpa [ssl,argCount] using slots
    · simpa [inputCells] using mem
    · simpa [fieldBindings,argCount] using bindings
    · rw [work]; exact Nat.le_refl _

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+20-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat := max caller.frame.state.storage.peak caller.frame.state.liveSpace
structure StageState (mode : Mode) (caller initial callee : NState) (x : Int) (E : Nat) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fieldCells mode x) (fieldBindings (callerP caller) (argCount mode+2)) (ssl (argCount mode+2))
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+stageWork mode E) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  valueValid : s64.valid (outputValue mode x) = true

theorem stage_ready (mode : Mode) (caller : NState) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = s64) (de : e.denote (envOf caller) = some x)
    (hx : s64.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (program mode).parameters (arguments mode e) = some initial ∧
      runFuel fuel (program mode).body initial = .finished ⟨callee,none,false⟩ ∧ StageState mode caller initial callee x e.nodes := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work⟩ := prepare_entry mode caller e x he ht de hx valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec mode (callerP caller) x hx
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] (inputCells mode x)).mem (ws (callerP caller) [] (inputCells mode x)).bs (ssl (ws (callerP caller) [] (inputCells mode x)).bs.length) := by
    refine ⟨by simpa [ws,input_length] using slots,?_,?_,bas,scope⟩
    · simpa [ws] using mem
    · simpa [ws,fieldBindings,input_length] using bindings
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1) caller.frame.state.storage.objects.length := by
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] (inputCells mode x)).mem.length := by simp [ws,callerP]; omega
  have nbound := raw_need_bound mode
  have ab := arg_count_bound mode
  have run := sound (program mode).body (scalar_body mode) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,input_length]; unfold scalarBound; omega)
    (by rw [need]; unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState mode caller initial step.state x e.nodes := by
    refine ⟨?_,faD,?_,?_,value_valid mode x hx⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,input_length] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [cost] at bound
      unfold stageWork
      omega
    · have stable := CppScalarContents.run_stable fuel (program mode).body initial step
        (allowed_body mode) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have ic : CppScalarContents.Contents caller.frame initial.frame := by rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact ic.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)

def destinationValues (mode : Mode) (x : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx (outputValue mode x)),!targetConst),((cf (flag mode)),!targetConst)]
def exported (mode : Mode) (x : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues mode x targetConst)

structure ExportState (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx (outputValue mode x)),(cf (flag mode))]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩,⟨caller.scalars.memory.length+1,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+stageWork mode E+3
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  valueValid : s64.valid (outputValue mode x) = true

theorem finish_export (mode : Mode) (x : Int) (E : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState mode caller initial callee x E)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (fields mode)
        [] (SelectedSet.permissions targetConst) =
      some (exported mode x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState mode x E caller initial (exported mode x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells mode x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c0 : callee.scalarCell (argCount mode) s64 =
      some (⟨(callerP caller).length+argCount mode,true⟩,cx (outputValue mode x)) := by
    cases mode <;> simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputCells,
      argCount,outputValue,flag,ssl,List.range_succ,cx,cf] <;> simpa [outputValue] using ready.valueValid
  have c1 : callee.scalarCell (argCount mode+1) bl =
      some (⟨(callerP caller).length+argCount mode+1,true⟩,cf (flag mode)) := by
    cases mode <;> simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputCells,
      argCount,outputValue,flag,ssl,List.range_succ,cx,cf,bl] <;> rfl
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (fields mode) = some [((cx (outputValue mode x)),true),((cf (flag mode)),true)] := by
    rw [fields_shape]
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c0,c1]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx (outputValue mode x)),true),((cf (flag mode)),true)] (SelectedSet.permissions targetConst) =
      some (destinationValues mode x targetConst) := by cases targetConst <;> rfl
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells mode x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (fields mode)
      [] (SelectedSet.permissions targetConst) =
        some (exported mode x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
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
  have sp : (exported mode x caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported mode x caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.valueValid⟩
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
  · change callee.scalars.work+0+(destinationValues mode x targetConst).length+1 ≤ caller.scalars.work+stageWork mode E+3
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported mode x caller callee targetConst).scalars.peak+(exported mode x caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst)
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

theorem destination_readable (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst) :
    out.scalarCell caller.slots.length s64 = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx (outputValue mode x))) ∧
    out.scalarCell (caller.slots.length+1) bl = some (⟨caller.scalars.memory.length+1,!targetConst⟩,(cf (flag mode))) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have s1 : out.slots[caller.slots.length+1]? = some (.scalar (caller.scalars.bindings.length+1)) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have b1 : out.scalars.bindings[caller.scalars.bindings.length+1]? = some ⟨caller.scalars.memory.length+1,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx (outputValue mode x)) := by rw [post.memory]; simp
  have m1 : out.scalars.memory[caller.scalars.memory.length+1]? = some (cf (flag mode)) := by rw [post.memory]; simp
  constructor
  · simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.valueValid]
  · simp [NState.scalarCell,NState.scalarSlot,s1,b1,m1,cf,flag_valid]

theorem frame_extension (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension mode x E caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension mode x E caller initial out targetConst post valid lengths) reference value found


theorem view_shape (mode : Mode) (fuel : Nat) (caller : NState) (args : List NArgument) (targetConst : Bool) :
    view mode fuel caller args targetConst = MemberView.constructViewFuel (program mode) fuel caller args []
      (fields mode) [] (SelectedSet.permissions targetConst) := by cases mode <;> rfl

theorem entry_correct (mode : Mode) (caller : NState) (targetConst : Bool) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = s64) (de : e.denote (envOf caller) = some x)
    (hx : s64.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program mode).parameters (arguments mode e) = some initial ∧
      view mode fuel caller (arguments mode e) targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState mode x e.nodes caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready mode caller e x he ht de hx valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export mode x e.nodes caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported mode x caller callee targetConst,prepared,?_,post⟩
  rw [view_shape]
  exact MemberView.constructView_of_steps (program mode) fuel caller initial callee _ (arguments mode e) []
    (fields mode) [] (SelectedSet.permissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem value_construct_correct (caller : NState) (targetConst : Bool) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = s64) (de : e.denote (envOf caller) = some x)
    (hx : s64.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program .value).parameters [.value e] = some initial ∧
      view .value fuel caller [.value e] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState .value x e.nodes caller initial out targetConst :=
  entry_correct .value caller targetConst e x he ht de hx valid lengths strict base

theorem default_construct_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program .defaulted).parameters [] = some initial ∧
      view .defaulted fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState .defaulted 0 1 caller initial out targetConst :=
  entry_correct .defaulted caller targetConst (.literal s64 0) 0 rfl rfl rfl rfl valid lengths strict base

theorem id_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program .identity).parameters [] = some initial ∧
      view .identity fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState .identity 0 1 caller initial out targetConst :=
  entry_correct .identity caller targetConst (.literal s64 0) 0 rfl rfl rfl rfl valid lengths strict base

theorem total_work (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState mode x E caller initial out targetConst) : out.work ≤ caller.work+stageWork mode E+3 := by
  have hw := post.scalarWork
  have hs := post.storageWork
  simp only [NState.work]
  omega

theorem value_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState .value x E caller initial out targetConst) : out.work ≤ caller.work+E+9 := by
  have bound := total_work .value x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

theorem default_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState .defaulted x E caller initial out targetConst) : out.work ≤ caller.work+9 := by
  have bound := total_work .defaulted x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

theorem id_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState .identity x E caller initial out targetConst) : out.work ≤ caller.work+10 := by
  have bound := total_work .identity x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

end SetRecordConstructorGeneral
