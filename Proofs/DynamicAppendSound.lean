import Proofs.DynamicScalarSound
import Proofs.MultiVecDynamicSteps

namespace Proofs.DynamicAppendSound
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicScalarSteps Proofs.DynamicScalarSound

theorem parameter_found (params : List Parameter) (l : Locals) (slot : Nat) (p : Parameter)
    (run : DynamicStmt.parameter params l slot = some p) :
    l.slots[slot]? = some (.vector p.slot) ∧ params.find? (fun q => q.slot == p.slot) = some p := by
  unfold DynamicStmt.parameter at run
  cases found : l.slots[slot]? with
  | none => simp [found] at run
  | some loc =>
    cases loc with
    | scalar index => simp [found] at run
    | vector rb =>
      simp only [found,Bind.bind,Option.bind] at run
      have equal : p.slot = rb := by simpa using List.find?_some run
      subst rb
      exact ⟨rfl,run⟩

theorem mutable_found (params : List Parameter) (st : DynamicStmt.State) (slot : Nat)
    (expected : Element) (p : Parameter) (run : DynamicStmt.mutableRoot params st slot expected = some p) :
    st.locals.slots[slot]? = some (.vector p.slot) ∧ params.find? (fun q => q.slot == p.slot) = some p ∧
      p.writable = true ∧ p.maximum = true ∧ p.element = expected ∧
      ∃ view, st.contents p.owner = some view ∧ view.element = expected ∧ view.scope = p.scope := by
  unfold DynamicStmt.mutableRoot at run
  cases first : DynamicStmt.parameter params st.locals slot with
  | none => simp [first] at run
  | some q =>
    cases second : st.contents q.owner with
    | none => simp [first,second] at run
    | some view =>
      simp only [first,second,Bind.bind,Option.bind] at run
      split at run
      · rename_i good
        have equal : q = p := Option.some.inj run
        subst q
        obtain ⟨loc,selected⟩ := parameter_found params st.locals slot p first
        exact ⟨loc,selected,good.1,good.2.1,good.2.2.1,view,second,good.2.2.2.1,good.2.2.2.2⟩
      · contradiction

-- The local-container operation changes the frame only. Scalar values and
-- the variable slot map survive the container evaluation and final charge.
theorem appendRoot_locals (s out : NState) (slot : Nat) (ty : Ty)
    (run : (NStmt.appendRow (.local slot) ty).run s = some ⟨out,none,false⟩) : snapshot out = snapshot s := by
  cases loc : s.vectorSlot slot with
  | none =>
    have missing : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+2)) = none := by
      have loc' : (s.charge 0 ((Container.local slot).nodes+2)).vectorSlot slot = none := loc
      simp [Container.eval,loc']
    simp [NStmt.run,missing] at run
  | some rb =>
    have eval := eval_local (s.charge 0 ((Container.local slot).nodes+2)) slot rb
      (by simpa [NState.vectorSlot] using loc)
    cases step : s.frame.appendRow rb ty with
    | none => simp [NStmt.run,eval,step] at run
    | some frame =>
      simp only [NStmt.run,eval,Bind.bind,Option.bind] at run
      change (s.frame.appendRow rb ty).bind _ = _ at run
      simp only [step,Option.bind_some,Option.some.injEq,NStep.mk.injEq] at run
      obtain ⟨rfl,_,_⟩ := run
      rfl

-- No reserve premise is imposed. Only the C++ max-size bound for this actual
-- parent is needed; capacity growth is handled by the underlying operation.
theorem appendRoot (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (slot : Nat) (ty : Ty) (p : Parameter)
    (mutable : DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p)
    (sc : Nat) (values : List (List Int)) (lookup : st.contents p.owner = some (.rows ty sc values))
    (old : Buffer Value) (found : s.frame.state.storage.lookup p.owner = some old)
    (room : old.items.length < old.limit) :
    let pure : DynamicStmt.Step := ⟨⟨st.locals,putContents st.contents p.owner (.rows ty sc (values ++ [[]]))⟩,none⟩
    DynamicStmt.run params (.appendRow (.local slot) ty) st = some pure ∧
      ∃ (r : Result Value Unit) (out : NState), (NStmt.appendRow (.local slot) ty).run s = some ⟨out,none,false⟩ ∧
        Matches params pure ⟨out,none,false⟩ ∧ out.work = s.work+r.work+3 := by
  obtain ⟨location,selected,writable,maximum,_,_⟩ := mutable_found params st slot _ p mutable
  obtain ⟨heap,m,family,he⟩ := realizes.heap
  have lifted : eraseHeap heap p.owner = some (.rows ty sc values) := by rw [he]; exact lookup
  obtain ⟨ids,epoch,hv⟩ := DynamicSizeSound.rows_lift heap p.owner ty sc values lifted
  obtain ⟨r,out,ran,post,scalarWork⟩ := MultiVecDynamicSteps.appendRoot_stmt s params heap m family p
    (List.mem_of_find?_eq_some selected) slot (DynamicSizeSound.vector_slot params st.locals st.contents s realizes slot p.slot location)
    ty sc ids epoch values hv writable maximum old found room
  have projected : eraseHeap (put heap p.owner (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]]))) =
      putContents st.contents p.owner (.rows ty sc (values ++ [[]])) := by
    rw [erase_put,he]; rfl
  have after : Realizes params st.locals (putContents st.contents p.owner (.rows ty sc (values ++ [[]]))) out :=
    ⟨(appendRoot_locals s out slot ty ran).trans realizes.locals,_,_,post,projected⟩
  have storageWork := post.measured.work
  have oldWork := family.measured.work
  refine ⟨?_,r,out,ran,⟨after,rfl,rfl⟩,?_⟩
  · simp [DynamicStmt.run,mutable,DynamicContents.appendRoot,lookup]
  · unfold NState.work
    simp only [afterRoot] at storageWork
    omega

end Proofs.DynamicAppendSound
