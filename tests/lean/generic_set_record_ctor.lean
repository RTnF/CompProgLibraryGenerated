namespace GenericSetCtor
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
abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
variable (ty : Ty)
inductive Mode where
  | value | defaulted | identity
  deriving DecidableEq
def argCount : Mode → Nat | .value => 1 | _ => 0
def arguments : Mode → NExpr → List NArgument | .value,e => [.value e] | _,_ => []
def inputCells : Mode → Int → List Cell | .value,x => [cx ty x] | _,_ => []
def outputValue : Mode → Int → Int | .value,x => x | _,_ => 0
def flag : Mode → Int | .value => 0 | _ => 1
def fieldCells (mode : Mode) (x : Int) : List Cell :=
  inputCells ty mode x ++ [cx ty (outputValue mode x),cf (flag mode)]
def fieldBindings (P : List Cell) (count : Nat) : List CppState.Binding :=
  (List.range count).map fun i => ⟨P.length+i,true⟩
def rawWork : Mode → Nat | .value => 4 | .defaulted => 5 | .identity => 6
def rawNeed : Mode → Nat | .value => 9 | _ => 7
def prepWork : Mode → Nat → Nat | .value,E => E+2 | _,_ => 1
def stageWork (mode : Mode) (E : Nat) : Nat := prepWork mode E+rawWork mode
def inputExpr : Mode → NExpr | .value => .variable ty 0 | _ => Proofs.GenericLazy.castTo ty i32 (.literal i32 0)
def tail : Mode → Command | .identity => .sequence (.scope Sk) Sk | _ => Sk
def rawBody (mode : Mode) : Command := .sequence (.primitive (.declare ty true (inputExpr ty mode)))
  (.sequence (.primitive (.declare bl true (.literal bl (flag mode)))) (tail mode))

def program : Mode → NProgram
  | .value => ⟨[.scalar ty false true],.unit,rawBody ty .value⟩
  | .defaulted => ⟨[],.unit,rawBody ty .defaulted⟩
  | .identity => ⟨[],.unit,rawBody ty .identity⟩
def fields : Mode → List Proofs.CppConstructorFinish.ScalarField
  | .value => [⟨1,ty⟩,⟨2,bl⟩]
  | .defaulted => [⟨0,ty⟩,⟨1,bl⟩]
  | .identity => [⟨0,ty⟩,⟨1,bl⟩]
def permissions (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(bl,(true && (!targetConst || false)))]
def view (mode : Mode) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (program ty mode) fuel caller arguments [] (fields ty mode)
    (vectorPermissions targetConst) (permissions ty targetConst)
theorem body_shape (mode : Mode) : (program ty mode).body = rawBody ty mode := by cases mode <;> rfl
theorem fields_shape (mode : Mode) : fields ty mode = [⟨argCount mode,ty⟩,⟨argCount mode+1,bl⟩] := by cases mode <;> rfl
theorem scalar_body (mode : Mode) : Scalar (program ty mode).body = true := by
  have h := Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl
  cases mode <;> simp [program, rawBody, tail, inputExpr, Scalar, NExpr.scalarOnly, h]
theorem allowed_body (mode : Mode) : CppScalarContents.Allowed (program ty mode).body = true := by
  cases mode <;> simp [program, rawBody, tail, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]
theorem flag_valid (mode : Mode) : bl.valid (flag mode) = true := by cases mode <;> decide
theorem value_valid (mode : Mode) (x : Int) (hx : ty.valid x = true) :
    ty.valid (outputValue mode x) = true := by cases mode with
  | value => exact hx
  | defaulted => exact Proofs.GenericLazy.valid_zero ty
  | identity => exact Proofs.GenericLazy.valid_zero ty
theorem input_length (mode : Mode) (x : Int) : (inputCells ty mode x).length = argCount mode := by cases mode <;> rfl
theorem arg_count_bound (mode : Mode) : argCount mode ≤ 1 := by cases mode <;> decide
theorem raw_need_bound (mode : Mode) : rawNeed mode ≤ 9 := by cases mode <;> decide

theorem raw_exec (mode : Mode) (P : List Cell) (x : Int) (hx : ty.valid x = true) :
    ∃ r, pexec 1 (program ty mode).body (ws P [] (inputCells ty mode x)) = some r ∧
      r.ret = none ∧ r.cost ≤ rawWork mode ∧ r.need ≤ P.length+rawNeed mode ∧
      r.ps = ws P [] (fieldCells ty mode x) := by
  cases mode with
  | value =>
    have dx : (NExpr.variable ty 0).denote (penv (ws P [] [cx ty x])) = some x := by
      rw [den_variable]; exact ws_env_loc P [] _ 0 (cx ty x) ty rfl rfl hx
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty x] ty (.variable ty 0) x dx (Ty.convert_of_valid _ _ hx))
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty x,cx ty x] bl (.literal bl 0) 0 rfl rfl)
    have run := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    refine ⟨⟨ws P [] [cx ty x,cx ty x,cf 0],none,4,P.length+9⟩,?_,rfl,by simp [rawWork],by simp [rawNeed],rfl⟩
    simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc,cf] using run
  | defaulted =>
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] ty (Proofs.GenericLazy.castTo ty i32 (.literal i32 0)) 0 (Proofs.GenericLazy.R0z_gen ty _) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty 0] bl (.literal bl 1) 1 rfl rfl)
    have run := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
    simp only [NExpr.nodes] at hn
    refine ⟨⟨ws P [] [cx ty 0,cf 1],none,(Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+3,P.length+max ((Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+4) 7⟩,?_,rfl,?_,?_,rfl⟩
    · simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc,cf] using run
    · simp only [NExpr.nodes] at *; simp [rawWork]; omega
    · simp only [NExpr.nodes] at *; simp [rawNeed]; omega
  | identity =>
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] ty (Proofs.GenericLazy.castTo ty i32 (.literal i32 0)) 0 (Proofs.GenericLazy.R0z_gen ty _) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty 0] bl (.literal bl 1) 1 rfl rfl)
    have sc0 := pexec_scope 1 Sk (ws P [] [cx ty 0,cf 1]) _ (pexec_skip 1 _)
    have sc : pexec 1 (.scope Sk) (ws P [] [cx ty 0,cf 1]) = some ⟨ws P [] [cx ty 0,cf 1],none,1,P.length+4⟩ := by
      simp only [List.take_length] at sc0
      simpa [ws] using sc0
    have run := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
    have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
    simp only [NExpr.nodes] at hn
    refine ⟨⟨ws P [] [cx ty 0,cf 1],none,(Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+4,P.length+max ((Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+4) 7⟩,?_,rfl,?_,?_,rfl⟩
    · simpa [body_shape,rawBody,inputExpr,flag,tail,inputCells,ws,NExpr.nodes,Nat.add_assoc,cf] using run
    · simp only [NExpr.nodes] at *; simp [rawWork]; omega
    · simp only [NExpr.nodes] at *; simp [rawNeed]; omega

theorem prepare_entry (mode : Mode) (caller : NState) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = ty) (de : e.denote (envOf caller) = some x)
    (hx : ty.valid x = true) (valid : caller.frame.state.wellFormed = true) :
    ∃ initial, prepare caller (program ty mode).parameters (arguments mode e) = some initial ∧
      initial.slots = ssl (argCount mode) ∧ initial.scalars.memory = callerP caller ++ inputCells ty mode x ∧
      initial.scalars.bindings = fieldBindings (callerP caller) (argCount mode) ∧
      initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
      initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      initial.scalars.work ≤ caller.scalars.work+prepWork mode e.nodes := by
  cases mode with
  | value =>
    obtain ⟨t,g,initial,prepared,slots,mem,bindings,base,scope,frame,work,peak,_⟩ :=
      prep_val caller (program ty .value).parameters ty rfl e x he ht de valid hx
    refine ⟨initial,prepared,?_,mem,?_,base,scope,frame,?_⟩
    · simpa [ssl,argCount,List.range_succ] using slots
    · simpa [fieldBindings,argCount,List.range_succ] using bindings
    · have bound := g.2.2.1
      rw [work]
      change t.scalars.work+2 ≤ caller.scalars.work+(e.nodes+2)
      omega
  | defaulted =>
    obtain ⟨initial,prepared,slots,mem,bindings,base,scope,frame,work,_⟩ := prep_none caller (program ty .defaulted).parameters rfl valid
    refine ⟨initial,prepared,?_,?_,?_,base,scope,frame,?_⟩
    · simpa [ssl,argCount] using slots
    · simpa [inputCells] using mem
    · simpa [fieldBindings,argCount] using bindings
    · rw [work]; exact Nat.le_refl _
  | identity =>
    obtain ⟨initial,prepared,slots,mem,bindings,base,scope,frame,work,_⟩ := prep_none caller (program ty .identity).parameters rfl valid
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
    (callerP caller ++ fieldCells ty mode x) (fieldBindings (callerP caller) (argCount mode+2)) (ssl (argCount mode+2))
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+stageWork mode E) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  valueValid : ty.valid (outputValue mode x) = true

theorem stage_ready (mode : Mode) (caller : NState) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = ty) (de : e.denote (envOf caller) = some x)
    (hx : ty.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (program ty mode).parameters (arguments mode e) = some initial ∧
      runFuel fuel (program ty mode).body initial = .finished ⟨callee,none,false⟩ ∧ StageState ty mode caller initial callee x e.nodes := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work⟩ := prepare_entry ty mode caller e x he ht de hx valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty mode (callerP caller) x hx
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] (inputCells ty mode x)).mem (ws (callerP caller) [] (inputCells ty mode x)).bs (ssl (ws (callerP caller) [] (inputCells ty mode x)).bs.length) := by
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] (inputCells ty mode x)).mem.length := by simp [ws,callerP]; omega
  have nbound := raw_need_bound mode
  have ab := arg_count_bound mode
  have run := sound (program ty mode).body (scalar_body ty mode) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,input_length]; unfold scalarBound; omega)
    (by unfold scalarBound; have := raw_need_bound mode; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty mode caller initial step.state x e.nodes := by
    refine ⟨?_,faD,?_,?_,value_valid ty mode x hx⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,input_length] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      unfold stageWork
      omega
    · have stable := CppScalarContents.run_stable fuel (program ty mode).body initial step
        (allowed_body ty mode) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have ic : CppScalarContents.Contents caller.frame initial.frame := by rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact ic.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)

def destinationValues (mode : Mode) (x : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx ty (outputValue mode x)),!targetConst),((cf (flag mode)),!targetConst)]
def exported (mode : Mode) (x : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues ty mode x targetConst)

structure ExportState (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx ty (outputValue mode x)),(cf (flag mode))]
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
  valueValid : ty.valid (outputValue mode x) = true

theorem finish_export (mode : Mode) (x : Int) (E : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty mode caller initial callee x E)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (fields ty mode)
        [] (permissions ty targetConst) =
      some (exported ty mode x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty mode x E caller initial (exported ty mode x caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells ty mode x) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c0 : callee.scalarCell (argCount mode) ty =
      some (⟨(callerP caller).length+argCount mode,true⟩,cx ty (outputValue mode x)) := by
    cases mode <;> simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputCells,
      argCount,outputValue,flag,ssl,List.range_succ,cx,cf] <;> simpa [outputValue] using ready.valueValid
  have c1 : callee.scalarCell (argCount mode+1) bl =
      some (⟨(callerP caller).length+argCount mode+1,true⟩,cf (flag mode)) := by
    cases mode <;> simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputCells,
      argCount,outputValue,flag,ssl,List.range_succ,cx,cf,bl] <;> rfl
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (fields ty mode) = some [((cx ty (outputValue mode x)),true),((cf (flag mode)),true)] := by
    rw [fields_shape ty]
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c0,c1]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty (outputValue mode x)),true),((cf (flag mode)),true)] (permissions ty targetConst) =
      some (destinationValues ty mode x targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, permissions, destinationValues, cx, cf, bl]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells ty mode x)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (fields ty mode)
      [] (permissions ty targetConst) =
        some (exported ty mode x caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
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
  have sp : (exported ty mode x caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported ty mode x caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
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
  · change callee.scalars.work+0+(destinationValues ty mode x targetConst).length+1 ≤ caller.scalars.work+stageWork mode E+3
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty mode x caller callee targetConst).scalars.peak+(exported ty mode x caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty mode x E caller initial out targetConst)
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
    (post : ExportState ty mode x E caller initial out targetConst) :
    out.scalarCell caller.slots.length ty = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx ty (outputValue mode x))) ∧
    out.scalarCell (caller.slots.length+1) bl = some (⟨caller.scalars.memory.length+1,!targetConst⟩,(cf (flag mode))) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have s1 : out.slots[caller.slots.length+1]? = some (.scalar (caller.scalars.bindings.length+1)) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have b1 : out.scalars.bindings[caller.scalars.bindings.length+1]? = some ⟨caller.scalars.memory.length+1,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx ty (outputValue mode x)) := by rw [post.memory]; simp
  have m1 : out.scalars.memory[caller.scalars.memory.length+1]? = some (cf (flag mode)) := by rw [post.memory]; simp
  constructor
  · simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.valueValid]
  · simp [NState.scalarCell,NState.scalarSlot,s1,b1,m1,cf,flag_valid]

theorem frame_extension (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty mode x E caller initial out targetConst)
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
    (post : ExportState ty mode x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension ty mode x E caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty mode x E caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension ty mode x E caller initial out targetConst post valid lengths) reference value found


theorem view_shape (mode : Mode) (fuel : Nat) (caller : NState) (args : List NArgument) (targetConst : Bool) :
    view ty mode fuel caller args targetConst = MemberView.constructViewFuel (program ty mode) fuel caller args []
      (fields ty mode) [] (permissions ty targetConst) := by cases mode <;> rfl

theorem entry_correct (mode : Mode) (caller : NState) (targetConst : Bool) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = ty) (de : e.denote (envOf caller) = some x)
    (hx : ty.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program ty mode).parameters (arguments mode e) = some initial ∧
      view ty mode fuel caller (arguments mode e) targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty mode x e.nodes caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready ty mode caller e x he ht de hx valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export ty mode x e.nodes caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty mode x caller callee targetConst,prepared,?_,post⟩
  rw [view_shape ty]
  exact MemberView.constructView_of_steps (program ty mode) fuel caller initial callee _ (arguments mode e) []
    (fields ty mode) [] (permissions ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem value_construct_correct (caller : NState) (targetConst : Bool) (e : NExpr) (x : Int)
    (he : e.scalarOnly = true) (ht : e.resultType = ty) (de : e.denote (envOf caller) = some x)
    (hx : ty.valid x = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program ty .value).parameters [.value e] = some initial ∧
      view ty .value fuel caller [.value e] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty .value x e.nodes caller initial out targetConst :=
  entry_correct ty .value caller targetConst e x he ht de hx valid lengths strict base

theorem default_construct_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program ty .defaulted).parameters [] = some initial ∧
      view ty .defaulted fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty .defaulted 0 1 caller initial out targetConst :=
  entry_correct ty .defaulted caller targetConst (.literal ty 0) 0 rfl rfl (by simp [NExpr.denote, Proofs.GenericLazy.valid_zero]) (Proofs.GenericLazy.valid_zero ty) valid lengths strict base

theorem id_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (program ty .identity).parameters [] = some initial ∧
      view ty .identity fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty .identity 0 1 caller initial out targetConst :=
  entry_correct ty .identity caller targetConst (.literal ty 0) 0 rfl rfl (by simp [NExpr.denote, Proofs.GenericLazy.valid_zero]) (Proofs.GenericLazy.valid_zero ty) valid lengths strict base

theorem total_work (mode : Mode) (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty mode x E caller initial out targetConst) : out.work ≤ caller.work+stageWork mode E+3 := by
  have hw := post.scalarWork
  have hs := post.storageWork
  simp only [NState.work]
  omega

theorem value_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty .value x E caller initial out targetConst) : out.work ≤ caller.work+E+9 := by
  have bound := total_work ty .value x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

theorem default_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty .defaulted x E caller initial out targetConst) : out.work ≤ caller.work+9 := by
  have bound := total_work ty .defaulted x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

theorem id_work (x : Int) (E : Nat) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty .identity x E caller initial out targetConst) : out.work ≤ caller.work+10 := by
  have bound := total_work ty .identity x E caller initial out targetConst post
  simpa [stageWork,prepWork,rawWork,Nat.add_assoc] using bound

end GenericSetCtor
