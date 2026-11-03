import Proofs.CppMovePreparedCall
import Proofs.CppFixedCall

namespace Proofs.CppMoveCallBindings
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppMixedInvoke
open Proofs.DynamicResultValid

-- Only callee parameter bindings are exposed to its formal location map.
-- Caller grants remain in the high-level heap and are restored by finish.
def vectorIndices : List Location → List Nat
  | [] => []
  | .scalar _::tail => vectorIndices tail
  | .vector index::tail => index::vectorIndices tail

def compactSlots : Nat → List Location → List Location
  | _,[] => []
  | next,.scalar index::tail => .scalar index::compactSlots next tail
  | next,.vector _::tail => .vector next::compactSlots (next+1) tail

def compact (s : NState) : Option NState := do
  let bindings ← (vectorIndices s.slots).mapM (fun index => s.frame.bindings[index]?)
  some {s with frame := {s.frame with bindings := bindings},slots := compactSlots 0 s.slots}

theorem compact_metadata (s out : NState) (actual : compact s = some out) :
    out.frame.state = s.frame.state ∧ out.frame.rootWritable = s.frame.rootWritable ∧
    out.scalars = s.scalars ∧ out.scope = s.scope ∧ out.peak = s.peak ∧
    out.slots = compactSlots 0 s.slots := by
  unfold compact at actual
  obtain ⟨bindings,_,done⟩ := bind_some _ _ _ actual
  have eq := Option.some.inj done
  subst out
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem vectorIndices_scalar (indices : List Nat) : vectorIndices (indices.map Location.scalar) = [] := by
  induction indices with
  | nil => rfl
  | cons head tail ih => simpa [vectorIndices] using ih

theorem compactSlots_scalar (indices : List Nat) (start : Nat) :
    compactSlots start (indices.map Location.scalar) = indices.map Location.scalar := by
  induction indices with
  | nil => rfl
  | cons head tail ih => simp [compactSlots,ih]

theorem compact_one_vector (s : NState) (index : Nat) (binding : Binding) (scalars : List Nat)
    (slots : s.slots = .vector index::scalars.map Location.scalar)
    (found : s.frame.bindings[index]? = some binding) :
    compact s = some {s with frame := {s.frame with bindings := [binding]},slots := .vector 0::scalars.map Location.scalar} := by
  simp [compact,slots,vectorIndices,vectorIndices_scalar,found,compactSlots,compactSlots_scalar]

def scalarIndex : Location → Option Nat
  | .scalar index => some index
  | _ => none

theorem compactSlots_scalarIndex (slots : List Location) (start slot : Nat) :
    ((compactSlots start slots)[slot]?).bind scalarIndex = (slots[slot]?).bind scalarIndex := by
  induction slots generalizing start slot with
  | nil => simp [compactSlots]
  | cons head tail ih =>
    cases slot with
    | zero => cases head <;> rfl
    | succ slot => cases head <;> simpa [compactSlots] using ih _ slot

theorem compact_scalarSlot (s out : NState) (actual : compact s = some out) (slot : Nat) :
    out.scalarSlot slot = s.scalarSlot slot := by
  have metadata := compact_metadata s out actual
  unfold NState.scalarSlot
  rw [metadata.2.2.2.2.2]
  exact compactSlots_scalarIndex s.slots 0 slot

theorem compact_scalarCell (s out : NState) (actual : compact s = some out)
    (slot : Nat) (ty : Proofs.CppScalar.Ty) : out.scalarCell slot ty = s.scalarCell slot ty := by
  have metadata := compact_metadata s out actual
  unfold NState.scalarCell
  rw [compact_scalarSlot s out actual slot,metadata.2.2.1]

theorem captured_binding (old : List Binding) (slots : List Location) (bindings : List Binding)
    (actual : (vectorIndices slots).mapM (fun index => old[index]?) = some bindings)
    (start slot index : Nat) (found : slots[slot]? = some (.vector index)) :
    ∃ next binding, (compactSlots start slots)[slot]? = some (.vector (start+next)) ∧
      bindings[next]? = some binding ∧ old[index]? = some binding := by
  induction slots generalizing bindings start slot with
  | nil => simp at found
  | cons head tail ih =>
    cases head with
    | scalar address =>
      cases slot with
      | zero => simp at found
      | succ slot =>
        obtain ⟨next,binding,mapped,captured,original⟩ := ih bindings actual start slot found
        exact ⟨next,binding,mapped,captured,original⟩
    | vector address =>
      simp only [vectorIndices,List.mapM_cons] at actual
      obtain ⟨binding,first,rest⟩ := bind_some _ _ _ actual
      obtain ⟨remaining,tailRun,done⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj done
      subst bindings
      cases slot with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq,Location.vector.injEq] at found
        subst index
        exact ⟨0,binding,by simp [compactSlots],rfl,first⟩
      | succ slot =>
        obtain ⟨next,entry,mapped,captured,original⟩ := ih remaining tailRun (start+1) slot found
        refine ⟨next+1,entry,?_,captured,original⟩
        simpa only [compactSlots,List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm 1 next] using mapped

theorem compact_vectorSlot (s out : NState) (actual : compact s = some out)
    (slot index : Nat) (located : s.vectorSlot slot = some index) :
    ∃ next binding, out.vectorSlot slot = some next ∧ out.frame.bindings[next]? = some binding ∧
      s.frame.bindings[index]? = some binding := by
  have found : s.slots[slot]? = some (.vector index) := by
    unfold NState.vectorSlot at located
    cases raw : s.slots[slot]? with
    | none => simp [raw] at located
    | some location =>
      cases location with
      | scalar address => simp [raw] at located
      | vector address =>
        simp only [raw,Bind.bind,Option.bind,Option.some.injEq] at located
        subst index
        rfl
  unfold compact at actual
  obtain ⟨bindings,gathered,done⟩ := bind_some _ _ _ actual
  have eq := Option.some.inj done
  subst out
  obtain ⟨next,binding,mapped,captured,original⟩ := captured_binding s.frame.bindings s.slots bindings gathered 0 slot index found
  refine ⟨next,binding,?_,captured,original⟩
  simp [NState.vectorSlot,mapped,Bind.bind,Option.bind]

theorem compact_resolve (s out : NState) (actual : compact s = some out)
    (slot index : Nat) (located : s.vectorSlot slot = some index)
    (expected : Proofs.CppVectorOwnership.Element) :
    ∃ next, out.vectorSlot slot = some next ∧ out.frame.resolve next expected = s.frame.resolve index expected := by
  have metadata := compact_metadata s out actual
  obtain ⟨next,binding,mapped,captured,original⟩ := compact_vectorSlot s out actual slot index located
  refine ⟨next,mapped,?_⟩
  simp only [Frame.resolve,captured,original,Frame.headerOwner,Frame.object,Frame.maximum,metadata.1,metadata.2.1]

open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppMovePreparedCall Proofs.CppMoveRestore Proofs.CppMoveHeaders

theorem finish_memory (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) :
    out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length := by
  cases returned with
  | none => simp [Proofs.CppNestedCall.finish] at actual
  | some ret =>
    cases ret with
    | unit => simp [Proofs.CppNestedCall.finish] at actual
    | vector owner element => simp [Proofs.CppNestedCall.finish] at actual
    | scalar value =>
      unfold Proofs.CppNestedCall.finish at actual
      dsimp only at actual
      split at actual
      · split at actual
        · obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
          obtain ⟨retired,_,done⟩ := bind_some _ _ _ rest
          have eq := congrArg Prod.fst (Option.some.inj done)
          change _ = out at eq
          subst out
          rfl
        · simp at actual
      · simp at actual

def callFuel (program : NProgram) (fuel : Nat) (caller : Context) (ty : Ty)
    (arguments : List NArgument) : Outcome (Context × Ret) :=
  if Proofs.CppMoveCallRestore.eligible program then do
    let prepared ← liftChecked (prepareArguments caller ty program.parameters arguments)
    let initial ← liftChecked (compact (project prepared ty))
    let step ← Proofs.CppNestedProgram.runFuel fuel program.body initial
    if step.breaking then .fault else do
      let (after,result) ← liftChecked (Proofs.CppNestedCall.finish (project caller ty) step.state program.result step.returned)
      let out ← liftChecked (restoreContext caller ty after)
      pure (out,result)
  else .fault

theorem call_of_body (program : NProgram) (fuel : Nat) (caller prepared : Context) (initial : NState)
    (ty retType : Ty) (arguments : List NArgument) (callee : NState) (value : Int)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller ty).frame.state.wellFormed = true)
    (preparedRun : prepareArguments caller ty program.parameters arguments = some prepared)
    (compacted : compact (project prepared ty) = some initial)
    (ran : Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished ⟨callee,some (.scalar value),false⟩)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (valueValid : retType.valid value = true) :
    ∃ out, callFuel program fuel caller ty arguments = .finished (out,.scalar value) ∧ work out = callee.work+1 ∧
      out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length ∧
      (∀ owner, (project out ty).frame.state.storage.lookup owner = callee.frame.state.storage.lookup owner) ∧
      out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak)
        (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
      out.objects.heap.peak = max callee.frame.state.storage.peak
        (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ∧
      out.peak = max (max caller.peak callee.peak) (out.scalars.peak+out.objects.heap.peak) := by
  have prep := prepareArguments_effects caller prepared ty program.parameters arguments preparedRun
  have compactedData := compact_metadata (project prepared ty) initial compacted
  have state : initial.frame.state = (project caller ty).frame.state := by
    rw [compactedData.1]
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have flags : initial.frame.rootWritable = (project caller ty).frame.rootWritable := by
    rw [compactedData.2.1]
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have scope : initial.scope = caller.scope+1 := compactedData.2.2.2.1.trans prep.2
  have innerContexts : ∀ owner sc, initial.frame.state.forest.context owner = some sc → sc ≤ initial.scope := by
    intro owner sc found
    rw [state] at found
    rw [scope]
    exact Nat.le_trans (contexts owner sc found) (Nat.le_succ _)
  have initialValid : initial.frame.state.wellFormed = true := by rw [state]; exact valid
  have calleeValid := Proofs.CppNoResizeValid.run_valid fuel program.body initial
    ⟨callee,some (.scalar value),false⟩ allowed innerContexts initialValid ran
  have body := Proofs.CppNoResizeRun.run_headers fuel program.body initial
    ⟨callee,some (.scalar value),false⟩ allowed innerContexts ran
  have headers : Proofs.CppBufferHeaders.SameHeaders (project caller ty).frame.state callee.frame.state := by
    rw [← state]
    exact body.headers
  obtain ⟨after,finished⟩ := finish_ready (project caller ty) callee retType value fits types calleeValid valueValid
  have effects := Proofs.CppCallFrame.finish_scalar_frame (project caller ty) callee after retType
    (some (.scalar value)) (.scalar value) headers (body.flags.trans flags) (body.scopedState.trans scope) contexts finished
  obtain ⟨out,restored⟩ := restoreContext_ready caller ty after effects.slots effects.scopedState effects.vectorBindings
    effects.scalarBindings effects.memoryLength effects.base effects.headers effects.flags covered
    (Proofs.CppMoveCallRestore.finish_valid (project caller ty) callee after retType (some (.scalar value)) (.scalar value) finished)
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner callee.scope found
    have endScope : callee.scope = caller.scope+1 := body.scopedState.trans scope
    rw [endScope] at bound
    omega
  have memory : out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length := by
    have projected := restoreContext_project caller out ty after restored covered
    have scalarMemory := congrArg (fun s : NState => s.scalars.memory) projected
    exact scalarMemory.trans (finish_memory (project caller ty) callee after retType (some (.scalar value)) (.scalar value) finished)
  refine ⟨out,?_,?_,memory,?_,restored_finish_counters caller out ty retType callee after
    (some (.scalar value)) (.scalar value) finished restored covered⟩
  · simp [callFuel,Proofs.CppMoveCallRestore.eligible,scalar,allowed,preparedRun,compacted,ran,finished,restored,
      bind,Outcome.bind,liftChecked,pure]
  · rw [← project_work out ty,restoreContext_project caller out ty after restored covered]
    exact finish_work (project caller ty) callee after retType (some (.scalar value)) (.scalar value) fresh finished
  · intro owner
    rw [restoreContext_project caller out ty after restored covered]
    exact Proofs.CppFixedCall.finish_values (project caller ty) callee after retType (some (.scalar value)) (.scalar value)
      headers (body.scopedState.trans scope) contexts finished owner

end Proofs.CppMoveCallBindings
