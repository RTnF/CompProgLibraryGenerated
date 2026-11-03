import Proofs.CppMoveWrite
import Proofs.CppNestedCall
import Proofs.CppExprPrefix
import Proofs.CppEvalScope

namespace Proofs.CppMoveContext
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram

-- Vector locations in this high-level context are stable object-view slots;
-- scalar locations remain existing scalar binding slots and addresses.
structure Context where
  objects : Proofs.CppMoveViews.State Int
  scalars : Proofs.CppState.State
  slots : List Location := []
  scope : Nat := 0
  peak : Nat := 0

def location (grants : Nat) : Location → Location
  | .scalar index => .scalar index
  | .vector view => .vector (grants+view)

def project (s : Context) (ty : Ty) : NState :=
  ⟨s.scalars,(Proofs.CppMoveFrame.materialize s.objects ty).frame,
    s.slots.map (location s.objects.heap.grants.length),s.scope,s.peak⟩

def scalarSlot (s : Context) (slot : Nat) : Option Nat := do
  let .scalar index ← s.slots[slot]? | none
  some index

def vectorView (s : Context) (slot : Nat) : Option Nat := do
  let .vector view ← s.slots[slot]? | none
  some view

def work (s : Context) : Nat := s.scalars.work+s.objects.heap.work

def charge (s : Context) (work temporaries : Nat) : Context :=
  let scalars := ({s.scalars with work := s.scalars.work+work} : Proofs.CppState.State).observe temporaries
  {s with scalars := scalars, peak := max s.peak (scalars.peak+s.objects.heap.peak)}

theorem project_work (s : Context) (ty : Ty) : (project s ty).work = work s := rfl

theorem project_scalarSlot (s : Context) (ty : Ty) (slot : Nat) :
    (project s ty).scalarSlot slot = scalarSlot s slot := by
  unfold NState.scalarSlot scalarSlot
  simp only [project,List.getElem?_map]
  cases found : s.slots[slot]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem project_vectorSlot (s : Context) (ty : Ty) (slot : Nat) :
    (project s ty).vectorSlot slot = (vectorView s slot).map (s.objects.heap.grants.length+·) := by
  unfold NState.vectorSlot vectorView
  simp only [project,List.getElem?_map]
  cases found : s.slots[slot]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem project_scalarCell (s : Context) (ty expected : Ty) (slot : Nat) :
    (project s ty).scalarCell slot expected = (do
      let index ← scalarSlot s slot
      let binding ← s.scalars.bindings[index]?
      let cell ← s.scalars.memory[binding.address]?
      if cell.type = expected ∧ expected.valid cell.value then some (binding,cell) else none) := by
  unfold NState.scalarCell
  rw [project_scalarSlot]
  rfl

theorem project_charge (s : Context) (ty : Ty) (amount temporaries : Nat) :
    project (charge s amount temporaries) ty = (project s ty).charge amount temporaries := by
  rfl

-- Projection re-resolves current vector objects; the element-grant prefix
-- remains independent of the caller's vector slot map.
theorem project_view_ready (s : Context) (ty : Ty) (slot viewSlot : Nat)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (located : vectorView s slot = some viewSlot)
    (resolved : Proofs.CppMoveViews.resolve s.objects viewSlot = some (view,header))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header ty.valid = true)
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (supported : Proofs.CppVectorBindings.supported ty)
    (valid : Proofs.CppMoveFrame.AllocationsValid s.objects.heap ty) :
    ∃ buffer, Proofs.CppMoveFrame.currentBuffer s.objects.heap view.header header = some buffer ∧
      (project s ty).vectorSlot slot = some (s.objects.heap.grants.length+viewSlot) ∧
      (project s ty).frame.resolve (s.objects.heap.grants.length+viewSlot) (.integer ty) =
        some (⟨buffer.owner,.integer ty,view.writable,.root header.scope⟩,Proofs.CppMoveFrame.box buffer) := by
  obtain ⟨buffer,current,frame⟩ := Proofs.CppMoveFrame.materialize_view_ready s.objects ty viewSlot view header
    resolved readable unique covered supported valid
  exact ⟨buffer,current,by simp [project_vectorSlot,located],frame⟩

-- This context is not yet a full prepare/finish adapter. Durable argument
-- references must store view/header identity across later argument evaluation;
-- a previously resolved allocation owner must not become an object alias.
-- Existing NestedCall.prepare reserves frame.bindings.length scalar cells.
-- A call bridge must account for actual live locals separately: immutable
-- grant-history bindings in this projection are ghost metadata, not stack.

-- A vector-reference argument keeps object identity and permission. It does
-- not snapshot the allocation that object happens to own during evaluation.
structure Borrow where
  header : Nat
  writable : Bool
  deriving DecidableEq, Repr

def captureBorrow (s : Context) (slot : Nat) (writable : Bool) : Option Borrow := do
  let viewSlot ← vectorView s slot
  let (view,_) ← Proofs.CppMoveViews.resolve s.objects viewSlot
  if writable = true → view.writable = true then some ⟨view.header,writable⟩ else none

-- This is a binding helper, not full callee preparation or stack accounting.
def installBorrow (s : Context) (argument : Borrow) : Option (Context × Nat) := do
  let (objects,viewSlot) ← Proofs.CppMoveViews.bind s.objects argument.header argument.writable
  some ({s with objects := objects,slots := s.slots++[.vector viewSlot]},s.slots.length)

theorem captureBorrow_runs (s : Context) (slot viewSlot : Nat) (writable : Bool)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (located : vectorView s slot = some viewSlot)
    (resolved : Proofs.CppMoveViews.resolve s.objects viewSlot = some (view,header))
    (permission : writable = true → view.writable = true) :
    captureBorrow s slot writable = some ⟨view.header,writable⟩ := by
  simp [captureBorrow,located,resolved]
  exact permission

theorem installBorrow_runs (s : Context) (argument : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header argument.header = some header)
    (permission : argument.writable = true → header.writable = true) :
    installBorrow s argument = some
      ({s with objects := ⟨s.objects.heap,s.objects.views++[⟨argument.header,argument.writable⟩]⟩, slots := s.slots++[.vector s.objects.views.length]},s.slots.length) := by
  have bound := Proofs.CppMoveViews.bind_runs s.objects argument.header header argument.writable found permission
  simp [installBorrow,bound]


theorem argument_resolve_runs (caller : NState) (slot index owner scope : Nat) (ty : Ty)
    (writable requested : Bool) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (located : caller.vectorSlot slot = some index)
    (resolved : caller.frame.resolve index (.integer ty) = some (⟨owner,.integer ty,writable,.root scope⟩,buffer))
    (permission : requested = true → writable = true) :
    Proofs.CppNestedCall.resolve caller (.vector ty requested) (.vectorReference slot) =
      some (caller.charge 1 1,.vector owner scope ty requested) := by
  have binding := (Proofs.CppFixedWrite.resolve_facts caller.frame index (.integer ty)
    ⟨owner,.integer ty,writable,.root scope⟩ buffer resolved).1
  simp [Proofs.CppNestedCall.resolve,located,binding,resolved]
  exact permission

theorem installBorrow_ready (s : Context) (argument : Borrow) (header : Proofs.CppMoveHeaders.Header) (ty : Ty)
    (found : s.objects.heap.header argument.header = some header)
    (permission : argument.writable = true → header.writable = true)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header ty.valid = true)
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (supported : Proofs.CppVectorBindings.supported ty)
    (valid : Proofs.CppMoveFrame.AllocationsValid s.objects.heap ty) :
    ∃ after slot buffer, installBorrow s argument = some (after,slot) ∧
      Proofs.CppMoveFrame.currentBuffer s.objects.heap argument.header header = some buffer ∧
      Proofs.CppNestedCall.resolve (project after ty) (.vector ty argument.writable) (.vectorReference slot) =
        some ((project after ty).charge 1 1,.vector buffer.owner header.scope ty argument.writable) := by
  let after : Context := {s with objects := ⟨s.objects.heap,s.objects.views++[⟨argument.header,argument.writable⟩]⟩, slots := s.slots++[.vector s.objects.views.length]}
  have installed := installBorrow_runs s argument header found permission
  have located : vectorView after s.slots.length = some s.objects.views.length := by
    simp [vectorView,after]
  have resolved : Proofs.CppMoveViews.resolve after.objects s.objects.views.length =
      some (⟨argument.header,argument.writable⟩,header) := by
    apply Proofs.CppMoveViews.resolve_runs
    · simp [after]
    · exact found
    · exact permission
  obtain ⟨buffer,current,slotRun,frameRun⟩ := project_view_ready after ty s.slots.length s.objects.views.length
    ⟨argument.header,argument.writable⟩ header located resolved readable unique covered supported valid
  refine ⟨after,s.slots.length,buffer,installed,current,?_⟩
  exact argument_resolve_runs (project after ty) s.slots.length _ buffer.owner header.scope ty
    argument.writable argument.writable _ slotRun frameRun (fun h => h)


-- Saved arguments are the result of argument evaluation. They are separate
-- from expression syntax; evaluation/side-effect ordering remains a caller
-- obligation until the complete argument evaluator is connected.
inductive SavedArgument where
  | scalar (parameter : Proofs.CppState.Parameter) (argument : Proofs.CppState.Argument)
  | vector (argument : Borrow)
  deriving DecidableEq, Repr

def observe (s : Context) : Context := {s with peak := max s.peak (s.scalars.peak+s.objects.heap.peak)}

def captureScalarReference (s : Context) (ty : Ty) (slot : Nat) (writable : Bool) : Option SavedArgument := do
  let (binding,_) ← (project s ty).scalarCell slot ty
  if writable = true → binding.writable = true then
    some (.scalar ⟨ty,true,writable⟩ (.reference binding.address))
  else none

-- Retain caller cells for shared scalar references, reserve one conservative
-- declaration/reference unit per actual caller slot, and clear callee locals.
-- Immutable object-view and element-grant history does not enter this count.
def prepareBase (caller : Context) (parameters : Nat) : Context :=
  let scalars : Proofs.CppState.State := {caller.scalars with memory := caller.scalars.memory ++ List.replicate caller.slots.length ⟨⟨1,false,true⟩,0⟩,bindings := [],work := caller.scalars.work+1+parameters}
  observe ⟨caller.objects,scalars.observe 0,[],caller.scope+1,caller.peak⟩

def bindSaved (s : Context) : SavedArgument → Option Context
  | .scalar parameter argument => do
    let scalars ← Proofs.CppState.bindArgument s.scalars parameter argument
    some (observe {s with scalars := scalars,slots := s.slots++[.scalar s.scalars.bindings.length]})
  | .vector argument => do
    let (next,_) ← installBorrow s argument
    -- A live vector-reference parameter needs one unit; historical bindings
    -- do not. Its placeholder is not a C++ element allocation.
    let scalars := ({next.scalars with memory := next.scalars.memory++[⟨⟨1,false,true⟩,0⟩]} : Proofs.CppState.State).observe 0
    some (observe {next with scalars := scalars})

def bindSavedAll : Context → List SavedArgument → Option Context
  | s,[] => some s
  | s,argument::tail => do
    let next ← bindSaved s argument
    bindSavedAll next tail

def prepareSaved (caller : Context) (arguments : List SavedArgument) : Option Context :=
  bindSavedAll (prepareBase caller arguments.length) arguments

theorem prepareBase_memory (caller : Context) (parameters : Nat) :
    (prepareBase caller parameters).scalars.memory.length = caller.scalars.memory.length+caller.slots.length ∧
      (prepareBase caller parameters).scalars.bindings = [] ∧
      (prepareBase caller parameters).slots = [] ∧ (prepareBase caller parameters).scope = caller.scope+1 ∧
      (prepareBase caller parameters).objects = caller.objects := by
  simp [prepareBase,observe,Proofs.CppState.State.observe]

theorem prepareBase_existing_cell (caller : Context) (parameters address : Nat) (cell : Proofs.CppState.Cell)
    (found : caller.scalars.memory[address]? = some cell) :
    (prepareBase caller parameters).scalars.memory[address]? = some cell := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp only [prepareBase,observe,Proofs.CppState.State.observe,List.getElem?_append_left inside]
  exact found

theorem bindSaved_scalar_runs (s : Context) (parameter : Proofs.CppState.Parameter) (argument : Proofs.CppState.Argument)
    (scalars : Proofs.CppState.State) (run : Proofs.CppState.bindArgument s.scalars parameter argument = some scalars) :
    bindSaved s (.scalar parameter argument) =
      some (observe {s with scalars := scalars,slots := s.slots++[.scalar s.scalars.bindings.length]}) := by
  simp [bindSaved,run]

theorem prepareSaved_nil (caller : Context) : prepareSaved caller [] = some (prepareBase caller 0) := rfl


-- Exit helper for borrowed-vector calls that leave no owned vector header in
-- their lexical scope. General local-vector destruction/return needs a
-- separate lifetime adapter and is not silently skipped here.
def finishBorrowed (caller callee : Context) : Option Context :=
  if callee.scope = caller.scope+1 ∧
      callee.objects.views.take caller.objects.views.length = caller.objects.views ∧
      callee.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants ∧
      caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
        caller.scalars.memory.map Proofs.CppState.Cell.type ∧
      (callee.objects.heap.headers.all fun entry => match entry with
        | none => true | some header => header.scope != callee.scope) = true then
    let scalars : Proofs.CppState.State := {caller.scalars with memory := callee.scalars.memory.take caller.scalars.memory.length,work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
    some (observe ⟨callee.objects,scalars.observe 0,caller.slots,caller.scope,max caller.peak callee.peak⟩)
  else none

theorem finishBorrowed_metadata (caller callee out : Context) (run : finishBorrowed caller callee = some out) :
    out.objects = callee.objects ∧ out.scalars.bindings = caller.scalars.bindings ∧
      out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length ∧
      out.slots = caller.slots ∧ out.scope = caller.scope := by
  unfold finishBorrowed at run
  split at run
  · have eq := Option.some.inj run
    subst out
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · simp at run


theorem installBorrow_effects (s out : Context) (argument : Borrow) (slot : Nat)
    (run : installBorrow s argument = some (out,slot)) :
    out.objects.heap = s.objects.heap ∧ out.scalars = s.scalars ∧ out.slots.length = s.slots.length+1 := by
  unfold installBorrow at run
  obtain ⟨pair,core,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  rcases pair with ⟨objects,viewSlot⟩
  have eq := Prod.mk.inj (Option.some.inj rest)
  rw [← eq.1]
  unfold Proofs.CppMoveViews.bind at core
  obtain ⟨header,_,last⟩ := Proofs.DynamicResultValid.bind_some _ _ _ core
  split at last
  · have objectsEq := (Prod.mk.inj (Option.some.inj last)).1
    rw [← objectsEq]
    exact ⟨rfl,rfl,by simp⟩
  · simp at last

theorem bindSaved_effects (s out : Context) (argument : SavedArgument) (run : bindSaved s argument = some out) :
    out.objects.heap = s.objects.heap ∧ out.slots.length = s.slots.length+1 := by
  cases argument with
  | scalar parameter argument =>
    unfold bindSaved at run
    obtain ⟨scalars,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj rest
    subst out
    exact ⟨rfl,by simp [observe]⟩
  | vector argument =>
    unfold bindSaved at run
    obtain ⟨pair,installed,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    have effects := installBorrow_effects s next argument slot installed
    have eq := Option.some.inj rest
    subst out
    exact ⟨effects.1,effects.2.2⟩

theorem bindSavedAll_effects (s out : Context) (arguments : List SavedArgument)
    (run : bindSavedAll s arguments = some out) :
    out.objects.heap = s.objects.heap ∧ out.slots.length = s.slots.length+arguments.length := by
  induction arguments generalizing s with
  | nil =>
    have eq := Option.some.inj run
    subst out
    exact ⟨rfl,by simp⟩
  | cons argument tail ih =>
    unfold bindSavedAll at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have before := bindSaved_effects s next argument first
    have after := ih next rest
    exact ⟨after.1.trans before.1,by simp only [List.length_cons]; omega⟩

theorem prepareSaved_effects (caller out : Context) (arguments : List SavedArgument)
    (run : prepareSaved caller arguments = some out) :
    out.objects.heap = caller.objects.heap ∧ out.slots.length = arguments.length := by
  have effects := bindSavedAll_effects (prepareBase caller arguments.length) out arguments run
  simpa [prepareBase,observe] using effects


theorem finishBorrowed_aliases (caller callee out : Context) (run : finishBorrowed caller callee = some out) :
    out.objects.views.take caller.objects.views.length = caller.objects.views ∧
      out.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants := by
  unfold finishBorrowed at run
  split at run
  next good =>
    have eq := Option.some.inj run
    subst out
    exact ⟨good.2.1,good.2.2.1⟩
  next => simp at run

theorem finishBorrowed_cell (caller callee out : Context) (address : Nat)
    (old actual : Proofs.CppState.Cell) (run : finishBorrowed caller callee = some out)
    (existing : caller.scalars.memory[address]? = some old)
    (updated : callee.scalars.memory[address]? = some actual) : out.scalars.memory[address]? = some actual := by
  have metadata := finishBorrowed_metadata caller callee out run
  have inside := (List.getElem?_eq_some_iff.mp existing).1
  rw [metadata.2.2.1,List.getElem?_take_of_lt inside]
  exact updated

theorem finishBorrowed_scalarCell (caller callee out : Context) (vectorTy expected : Ty) (slot index : Nat)
    (binding : Proofs.CppState.Binding) (old actual : Proofs.CppState.Cell)
    (run : finishBorrowed caller callee = some out) (located : scalarSlot caller slot = some index)
    (bound : caller.scalars.bindings[index]? = some binding)
    (existing : caller.scalars.memory[binding.address]? = some old)
    (updated : callee.scalars.memory[binding.address]? = some actual)
    (typed : actual.type = expected) (valid : expected.valid actual.value = true) :
    (project out vectorTy).scalarCell slot expected = some (binding,actual) := by
  have metadata := finishBorrowed_metadata caller callee out run
  have cell := finishBorrowed_cell caller callee out binding.address old actual run existing updated
  have slotFound : scalarSlot out slot = some index := by simpa [scalarSlot,metadata.2.2.2.1] using located
  rw [project_scalarCell]
  simp [slotFound,metadata.2.1,bound,cell,typed,valid]


-- NExpr performs scalar arithmetic and vector observations. The existing
-- evaluator's temporary Frame bindings are released at the expression boundary.
def resumeExpression (s : Context) (out : NState) : Context := {s with scalars := out.scalars,peak := out.peak}

def evalExpression (s : Context) (vectorTy : Ty) (expression : NExpr) : Option (Context × Int) := do
  let (out,value) ← expression.eval (project s vectorTy)
  some (resumeExpression s out,value)

theorem project_resumeExpression (s : Context) (vectorTy : Ty) (expression : NExpr) (out : NState) (value : Int)
    (run : expression.eval (project s vectorTy) = some (out,value)) :
    project (resumeExpression s out) vectorTy = out.release (project s vectorTy) := by
  have frame := Proofs.CppExprPrefix.release_frame expression (project s vectorTy) out value run
  have slots := (Proofs.CppExprPrefix.expression_prefix expression (project s vectorTy) out value run).1
  have scope := Proofs.CppEvalScope.expression_scope expression (project s vectorTy) out value run
  change (⟨out.scalars,(project s vectorTy).frame,(project s vectorTy).slots,(project s vectorTy).scope,out.peak⟩ : NState) =
    ⟨out.scalars,(out.release (project s vectorTy)).frame,out.slots,out.scope,out.peak⟩
  rw [frame,slots,scope]

theorem evalExpression_correspondence (s : Context) (vectorTy : Ty) (expression : NExpr) :
    (evalExpression s vectorTy expression).map (fun pair => (project pair.1 vectorTy,pair.2)) =
      (expression.eval (project s vectorTy)).map (fun pair => (pair.1.release (project s vectorTy),pair.2)) := by
  cases run : expression.eval (project s vectorTy) with
  | none => simp [evalExpression,run]
  | some pair =>
    rcases pair with ⟨out,value⟩
    simp [evalExpression,run,project_resumeExpression s vectorTy expression out value run]

def resolveArgument (s : Context) (vectorTy : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : Proofs.CppNestedCall.NArgument) : Option (Context × SavedArgument) := do
  match parameter,argument with
  | .scalar ty false writable,.value expression =>
    if expression.resultType = ty then
      let (next,value) ← evalExpression s vectorTy expression
      some (next,.scalar ⟨ty,false,writable⟩ (.value value))
    else none
  | .scalar ty true writable,.scalarReference slot =>
    let saved ← captureScalarReference s ty slot writable
    some (charge s 1 1,saved)
  | .vector ty writable,.vectorReference slot =>
    if ty = vectorTy then
      let saved ← captureBorrow s slot writable
      some (charge s 1 1,.vector saved)
    else none
  | _,_ => none

def resolveArguments : Context → Ty → List Proofs.CppVectorBindings.Parameter →
    List Proofs.CppNestedCall.NArgument → Option (Context × List SavedArgument)
  | s,_,[],[] => some (s,[])
  | s,ty,parameter::parameters,argument::arguments => do
    let (next,first) ← resolveArgument s ty parameter argument
    let (last,rest) ← resolveArguments next ty parameters arguments
    some (last,first::rest)
  | _,_,_,_ => none

def prepareArguments (caller : Context) (vectorTy : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument) : Option Context := do
  let (last,saved) ← resolveArguments caller vectorTy parameters arguments
  prepareSaved last saved

theorem resolve_value_runs (s next : Context) (vectorTy ty : Ty) (expression : NExpr) (writable : Bool) (value : Int)
    (type : expression.resultType = ty) (run : evalExpression s vectorTy expression = some (next,value)) :
    resolveArgument s vectorTy (.scalar ty false writable) (.value expression) =
      some (next,.scalar ⟨ty,false,writable⟩ (.value value)) := by simp [resolveArgument,type,run]

theorem resolve_vector_runs (s : Context) (ty : Ty) (slot : Nat) (writable : Bool) (argument : Borrow)
    (run : captureBorrow s slot writable = some argument) :
    resolveArgument s ty (.vector ty writable) (.vectorReference slot) = some (charge s 1 1,.vector argument) := by
  simp [resolveArgument,run]


def SavedReady (s : Context) : SavedArgument → Prop
  | .scalar parameter (.value value) => parameter.reference = false ∧ parameter.type.valid value = true
  | .scalar parameter (.reference address) =>
    ∃ cell, s.scalars.memory[address]? = some cell ∧ parameter.reference = true ∧
      cell.type = parameter.type ∧ parameter.type.valid cell.value = true
  | .vector argument =>
    ∃ header, s.objects.heap.header argument.header = some header ∧
      (argument.writable = true → header.writable = true)

theorem bindSaved_ready (s : Context) (argument : SavedArgument) (ready : SavedReady s argument) :
    ∃ out, bindSaved s argument = some out := by
  cases argument with
  | scalar parameter argument =>
    cases argument with
    | value value =>
      obtain ⟨notRef,valid⟩ := ready
      let scalars := ({s.scalars with memory := s.scalars.memory++[⟨parameter.type,value⟩],bindings := s.scalars.bindings++[⟨s.scalars.memory.length,parameter.writable⟩]} : Proofs.CppState.State).observe 0
      have core : Proofs.CppState.bindArgument s.scalars parameter (.value value) = some scalars := by
        simp [Proofs.CppState.bindArgument,notRef,valid,scalars]
      exact ⟨_,bindSaved_scalar_runs s parameter (.value value) scalars core⟩
    | reference address =>
      obtain ⟨cell,found,isRef,typed,valid⟩ := ready
      let scalars := ({s.scalars with bindings := s.scalars.bindings++[⟨address,parameter.writable⟩]} : Proofs.CppState.State).observe 0
      have core : Proofs.CppState.bindArgument s.scalars parameter (.reference address) = some scalars := by
        simp [Proofs.CppState.bindArgument,found,isRef,typed,valid,scalars]
      exact ⟨_,bindSaved_scalar_runs s parameter (.reference address) scalars core⟩
  | vector argument =>
    obtain ⟨header,found,permission⟩ := ready
    have installed := installBorrow_runs s argument header found permission
    simp only [bindSaved,installed,Bind.bind,Option.bind]
    exact ⟨_,rfl⟩


theorem scalarBind_memory (s out : Proofs.CppState.State) (parameter : Proofs.CppState.Parameter)
    (argument : Proofs.CppState.Argument) (run : Proofs.CppState.bindArgument s parameter argument = some out) :
    ∃ extra, out.memory = s.memory++extra := by
  cases argument with
  | value value =>
    simp only [Proofs.CppState.bindArgument] at run
    split at run
    · simp at run
    · have eq := Option.some.inj run
      subst out
      exact ⟨_,rfl⟩
  | reference address =>
    simp only [Proofs.CppState.bindArgument] at run
    obtain ⟨cell,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      subst out
      exact ⟨[],by simp [Proofs.CppState.State.observe]⟩

theorem bindSaved_memory (s out : Context) (argument : SavedArgument) (run : bindSaved s argument = some out) :
    ∃ extra, out.scalars.memory = s.scalars.memory++extra := by
  cases argument with
  | scalar parameter argument =>
    unfold bindSaved at run
    obtain ⟨scalars,core,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj rest
    subst out
    exact scalarBind_memory s.scalars scalars parameter argument core
  | vector argument =>
    unfold bindSaved at run
    obtain ⟨pair,installed,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    have effects := installBorrow_effects s next argument slot installed
    have eq := Option.some.inj rest
    subst out
    refine ⟨[⟨⟨1,false,true⟩,0⟩],?_⟩
    change next.scalars.memory++_ = _
    rw [effects.2.1]

theorem savedReady_mono (s out : Context) (argument : SavedArgument)
    (heap : out.objects.heap = s.objects.heap)
    (memory : ∃ extra, out.scalars.memory = s.scalars.memory++extra)
    (ready : SavedReady s argument) : SavedReady out argument := by
  cases argument with
  | scalar parameter argument =>
    cases argument with
    | value value => exact ready
    | reference address =>
      obtain ⟨cell,found,isRef,typed,valid⟩ := ready
      obtain ⟨extra,memoryEq⟩ := memory
      have inside := (List.getElem?_eq_some_iff.mp found).1
      refine ⟨cell,?_,isRef,typed,valid⟩
      rw [memoryEq,List.getElem?_append_left inside]
      exact found
  | vector argument =>
    obtain ⟨header,found,permission⟩ := ready
    refine ⟨header,?_,permission⟩
    rw [heap]
    exact found

theorem bindSavedAll_ready (s : Context) (arguments : List SavedArgument)
    (ready : ∀ argument ∈ arguments, SavedReady s argument) :
    ∃ out, bindSavedAll s arguments = some out := by
  induction arguments generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons argument tail ih =>
    obtain ⟨next,first⟩ := bindSaved_ready s argument (ready argument (by simp))
    have effects := bindSaved_effects s next argument first
    have memory := bindSaved_memory s next argument first
    have nextReady : ∀ argument ∈ tail, SavedReady next argument := by
      intro later member
      exact savedReady_mono s next later effects.1 memory (ready later (by simp [member]))
    obtain ⟨out,rest⟩ := ih next nextReady
    exact ⟨out,by simp [bindSavedAll,first,rest]⟩

theorem prepareSaved_ready (caller : Context) (arguments : List SavedArgument)
    (ready : ∀ argument ∈ arguments, SavedReady caller argument) :
    ∃ out, prepareSaved caller arguments = some out ∧
      out.objects.heap = caller.objects.heap ∧ out.slots.length = arguments.length := by
  have initialReady : ∀ argument ∈ arguments, SavedReady (prepareBase caller arguments.length) argument := by
    intro argument member
    apply savedReady_mono caller (prepareBase caller arguments.length) argument rfl
    · exact ⟨_,rfl⟩
    · exact ready argument member
  obtain ⟨out,run⟩ := bindSavedAll_ready (prepareBase caller arguments.length) arguments initialReady
  have effects := prepareSaved_effects caller out arguments run
  exact ⟨out,run,effects.1,effects.2⟩


def argumentCells : SavedArgument → Nat
  | .scalar _ (.value _) => 1
  | .scalar _ (.reference _) => 0
  | .vector _ => 1

def argumentBindings : SavedArgument → Nat
  | .scalar _ _ => 1
  | .vector _ => 0

theorem scalarBind_resources (s out : Proofs.CppState.State) (parameter : Proofs.CppState.Parameter)
    (argument : Proofs.CppState.Argument) (run : Proofs.CppState.bindArgument s parameter argument = some out) :
    out.memory.length = s.memory.length+(match argument with | .value _ => 1 | .reference _ => 0) ∧
      out.bindings.length = s.bindings.length+1 ∧ out.work = s.work ∧ out.baseMemory = s.baseMemory := by
  cases argument with
  | value value =>
    simp only [Proofs.CppState.bindArgument] at run
    split at run
    · simp at run
    · have eq := Option.some.inj run
      subst out
      simp [Proofs.CppState.State.observe]
  | reference address =>
    simp only [Proofs.CppState.bindArgument] at run
    obtain ⟨cell,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      subst out
      simp [Proofs.CppState.State.observe]

theorem bindSaved_resources (s out : Context) (argument : SavedArgument) (run : bindSaved s argument = some out) :
    out.scalars.memory.length = s.scalars.memory.length+argumentCells argument ∧
      out.scalars.bindings.length = s.scalars.bindings.length+argumentBindings argument ∧
      out.scalars.work = s.scalars.work ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  cases argument with
  | scalar parameter argument =>
    unfold bindSaved at run
    obtain ⟨scalars,core,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj rest
    subst out
    have resources := scalarBind_resources s.scalars scalars parameter argument core
    cases argument <;> exact resources
  | vector argument =>
    unfold bindSaved at run
    obtain ⟨pair,installed,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    have effects := installBorrow_effects s next argument slot installed
    have eq := Option.some.inj rest
    subst out
    simp [observe,Proofs.CppState.State.observe,effects.2.1,argumentCells,argumentBindings]

theorem bindSavedAll_resources (s out : Context) (arguments : List SavedArgument)
    (run : bindSavedAll s arguments = some out) :
    out.scalars.memory.length = s.scalars.memory.length+(arguments.map argumentCells).sum ∧
      out.scalars.bindings.length = s.scalars.bindings.length+(arguments.map argumentBindings).sum ∧
      out.scalars.work = s.scalars.work ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  induction arguments generalizing s with
  | nil =>
    have eq := Option.some.inj run
    subst out
    simp
  | cons argument tail ih =>
    unfold bindSavedAll at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have a := bindSaved_resources s next argument first
    have b := ih next rest
    refine ⟨?_,?_,b.2.2.1.trans a.2.2.1,b.2.2.2.trans a.2.2.2⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · simp only [List.map_cons,List.sum_cons]
      omega

theorem prepareSaved_resources (caller out : Context) (arguments : List SavedArgument)
    (run : prepareSaved caller arguments = some out) :
    out.scalars.memory.length = caller.scalars.memory.length+caller.slots.length+(arguments.map argumentCells).sum ∧
      out.scalars.bindings.length = (arguments.map argumentBindings).sum ∧
      work out = work caller+1+arguments.length ∧ out.scalars.baseMemory = caller.scalars.baseMemory := by
  have r := bindSavedAll_resources (prepareBase caller arguments.length) out arguments run
  have heap := (prepareSaved_effects caller out arguments run).1
  simp only [prepareBase,observe,Proofs.CppState.State.observe,List.length_append,List.length_replicate,List.length_nil,Nat.zero_add] at r
  refine ⟨r.1,r.2.1,?_,r.2.2.2⟩
  simp only [work,heap,r.2.2.1]
  omega


def scalarLive (s : Context) : Nat := s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length

theorem scalarBind_peak (s out : Proofs.CppState.State) (parameter : Proofs.CppState.Parameter)
    (argument : Proofs.CppState.Argument) (run : Proofs.CppState.bindArgument s parameter argument = some out) :
    out.peak = max s.peak (out.memory.length-out.baseMemory+out.bindings.length) := by
  cases argument with
  | value value =>
    simp only [Proofs.CppState.bindArgument] at run
    split at run
    · simp at run
    · have eq := Option.some.inj run
      subst out
      rfl
  | reference address =>
    simp only [Proofs.CppState.bindArgument] at run
    obtain ⟨cell,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      subst out
      rfl

theorem installBorrow_peak (s out : Context) (argument : Borrow) (slot : Nat)
    (run : installBorrow s argument = some (out,slot)) : out.peak = s.peak := by
  unfold installBorrow at run
  obtain ⟨pair,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  rcases pair with ⟨objects,viewSlot⟩
  have eq := (Prod.mk.inj (Option.some.inj rest)).1
  rw [← eq]

theorem bindSaved_peak (s out : Context) (argument : SavedArgument) (run : bindSaved s argument = some out) :
    out.scalars.peak = max s.scalars.peak (scalarLive out) ∧
      out.peak = max s.peak (out.scalars.peak+s.objects.heap.peak) := by
  cases argument with
  | scalar parameter argument =>
    unfold bindSaved at run
    obtain ⟨scalars,core,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj rest
    subst out
    exact ⟨scalarBind_peak s.scalars scalars parameter argument core,rfl⟩
  | vector argument =>
    unfold bindSaved at run
    obtain ⟨pair,installed,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    have effects := installBorrow_effects s next argument slot installed
    have peak := installBorrow_peak s next argument slot installed
    have eq := Option.some.inj rest
    subst out
    simp [scalarLive,observe,Proofs.CppState.State.observe,effects.2.1,effects.1,peak]

theorem bindSavedAll_live_mono (s out : Context) (arguments : List SavedArgument)
    (run : bindSavedAll s arguments = some out) : scalarLive s ≤ scalarLive out := by
  have r := bindSavedAll_resources s out arguments run
  unfold scalarLive
  rw [r.1,r.2.1,r.2.2.2]
  omega

theorem bindSavedAll_peak (s out : Context) (arguments : List SavedArgument)
    (run : bindSavedAll s arguments = some out) :
    out.scalars.peak ≤ max s.scalars.peak (scalarLive out) ∧
      out.peak ≤ max s.peak (max s.scalars.peak (scalarLive out)+s.objects.heap.peak) := by
  induction arguments generalizing s with
  | nil =>
    have eq := Option.some.inj run
    subst out
    exact ⟨Nat.le_max_left _ _,Nat.le_max_left _ _⟩
  | cons argument tail ih =>
    unfold bindSavedAll at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have a := bindSaved_peak s next argument first
    have b := ih next rest
    have mono := bindSavedAll_live_mono next out tail rest
    have heap := (bindSaved_effects s next argument first).1
    rw [heap] at b
    exact ⟨by omega,by omega⟩

theorem prepareSaved_peak (caller out : Context) (arguments : List SavedArgument)
    (run : prepareSaved caller arguments = some out) :
    out.scalars.peak ≤ max caller.scalars.peak (scalarLive out) ∧
      out.peak ≤ max caller.peak (max caller.scalars.peak (scalarLive out)+caller.objects.heap.peak) := by
  have bound := bindSavedAll_peak (prepareBase caller arguments.length) out arguments run
  have mono := bindSavedAll_live_mono (prepareBase caller arguments.length) out arguments run
  have initialScalar : (prepareBase caller arguments.length).scalars.peak =
      max caller.scalars.peak (scalarLive (prepareBase caller arguments.length)) := by
    simp [prepareBase,observe,Proofs.CppState.State.observe,scalarLive]
  have initialPeak : (prepareBase caller arguments.length).peak =
      max caller.peak ((prepareBase caller arguments.length).scalars.peak+caller.objects.heap.peak) := rfl
  rw [initialPeak,initialScalar] at bound
  change out.scalars.peak ≤ _ ∧ out.peak ≤ max (max caller.peak _)
    (max (max caller.scalars.peak (scalarLive (prepareBase caller arguments.length))) (scalarLive out)+caller.objects.heap.peak) at bound
  exact ⟨by omega,by omega⟩


theorem argument_footprint (argument : SavedArgument) : argumentCells argument+argumentBindings argument ≤ 2 := by
  cases argument with
  | scalar parameter argument => cases argument <;> simp [argumentCells,argumentBindings]
  | vector argument => simp [argumentCells,argumentBindings]

theorem arguments_footprint (arguments : List SavedArgument) :
    (arguments.map argumentCells).sum+(arguments.map argumentBindings).sum ≤ 2*arguments.length := by
  induction arguments with
  | nil => simp
  | cons argument tail ih =>
    have bound := argument_footprint argument
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem prepareSaved_scalarLive (caller out : Context) (arguments : List SavedArgument)
    (run : prepareSaved caller arguments = some out)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    scalarLive out ≤ caller.scalars.memory.length-caller.scalars.baseMemory+caller.slots.length+2*arguments.length := by
  have resources := prepareSaved_resources caller out arguments run
  have footprint := arguments_footprint arguments
  unfold scalarLive
  rw [resources.1,resources.2.1,resources.2.2.2]
  omega

theorem prepareSaved_peak_linear (caller out : Context) (arguments : List SavedArgument)
    (run : prepareSaved caller arguments = some out)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    out.peak ≤ max caller.peak (max caller.scalars.peak
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.slots.length+2*arguments.length)+caller.objects.heap.peak) := by
  have peak := (prepareSaved_peak caller out arguments run).2
  have live := prepareSaved_scalarLive caller out arguments run baseline
  omega

end Proofs.CppMoveContext
