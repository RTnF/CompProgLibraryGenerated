import Proofs.DynamicAppendAuto
import Proofs.MultiVecDynamicScope

namespace Proofs.DynamicScopeAuto
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedScope Proofs.CppNestedEval
open Proofs.MultiVecDynamic Proofs.MultiVecDynamicScope Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicControlBridge

-- A finite check on root scope tags implies that a deeper scope owns no
-- object, including descendants whose tag has no scope field of its own.
theorem fresh_of_tags (f : Proofs.CppVectorOwnership.Forest) (scope : Nat)
    (bounded : f.objects.all (fun entry => entry.all (fun tag => tag.scope.all (fun sc => decide (sc ≤ scope)))) = true) :
    ∀ owner, f.context owner ≠ some (scope+1) := by
  intro owner bad
  unfold Proofs.CppVectorOwnership.Forest.context at bad
  cases rooted : f.rootOwner owner with
  | none => simp [rooted] at bad
  | some root =>
    cases found : f.lookup root with
    | none => simp [rooted,found] at bad
    | some tag =>
      simp only [rooted,found,Bind.bind,Option.bind] at bad
      have member : some tag ∈ f.objects := by
        unfold Proofs.CppVectorOwnership.Forest.lookup at found
        cases entry : f.objects[root]? with
        | none => simp [entry] at found
        | some value =>
          cases value with
          | none => simp [entry] at found
          | some t =>
            simp only [entry,Option.join_some,Option.some.injEq] at found
            subst t
            exact List.mem_of_getElem? entry
      have checked := List.all_eq_true.mp bounded (some tag) member
      simp [bad] at checked
      omega

theorem leave_fields (outer inner restored : DynamicStmt.State)
    (run : DynamicControl.leave outer inner = some restored) :
    outer.locals.memory.length ≤ inner.locals.memory.length ∧
      (inner.locals.memory.take outer.locals.memory.length).map Proofs.CppState.Cell.type =
        outer.locals.memory.map Proofs.CppState.Cell.type ∧
      restored = ⟨⟨inner.locals.memory.take outer.locals.memory.length,outer.locals.bindings,outer.locals.slots⟩,inner.contents⟩ := by
  unfold DynamicControl.leave at run
  split at run
  · rename_i good
    exact ⟨good.1,good.2,(Option.some.inj run).symm⟩
  · contradiction

theorem enter (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) :
    Realizes params st.locals st.contents {s with scope := s.scope+1} := ⟨realizes.locals,realizes.heap⟩

-- The pure leave checks scalar length and types. No vector may be owned by
-- the retiring scope; unrelated live roots are allowed at other scopes.
theorem leave_sound (params : List Parameter) (outer inner restored : DynamicStmt.State)
    (s t : NState) (before : Realizes params outer.locals outer.contents s)
    (after : Realizes params inner.locals inner.contents t) (returned : Option Int)
    (pure : DynamicControl.leave outer inner = some restored)
    (fresh : ∀ owner, t.frame.state.forest.context owner ≠ some (s.scope+1)) :
    s.leave t (returned.map Ret.scalar) = some (s.left t) ∧
      Realizes params restored.locals restored.contents (s.left t) ∧
      (s.left t).work = t.work+1 ∧
      (s.left t).peak = max (max s.peak t.peak)
        (max (max s.scalars.peak t.scalars.peak) (liveS s)+
          max t.frame.state.storage.peak (t.frame.state.liveSpace-t.frame.state.storage.baseSpace)) := by
  obtain ⟨fits,types,result⟩ := leave_fields outer inner restored pure
  have sm := congrArg Locals.memory before.locals
  have sb := congrArg Locals.bindings before.locals
  have ss := congrArg Locals.slots before.locals
  have tm := congrArg Locals.memory after.locals
  change s.scalars.memory = outer.locals.memory at sm
  change s.scalars.bindings = outer.locals.bindings at sb
  change s.slots = outer.locals.slots at ss
  change t.scalars.memory = inner.locals.memory at tm
  have fits' : s.scalars.memory.length ≤ t.scalars.memory.length := by rw [sm,tm]; exact fits
  have types' : (t.scalars.memory.take s.scalars.memory.length).map Proofs.CppState.Cell.type =
      s.scalars.memory.map Proofs.CppState.Cell.type := by rw [sm,tm]; exact types
  obtain ⟨h0,m0,family0,_⟩ := before.heap
  obtain ⟨h,m,family,erased⟩ := after.heap
  have bounds : ∀ p ∈ params, p.slot < s.frame.bindings.length := by
    intro p hp
    exact (List.getElem?_eq_some_iff.mp (family0.bindings p hp)).1
  have leftFamily := Family.left s t family bounds
  have leftReal : Realizes params restored.locals restored.contents (s.left t) := by
    subst restored
    refine ⟨?_,h,observed m,leftFamily,erased⟩
    change (⟨t.scalars.memory.take s.scalars.memory.length,s.scalars.bindings,s.slots⟩ : Locals) = _
    rw [sm,tm,sb,ss]
  refine ⟨leave_scalar s t _ (by cases returned <;> simp) fits' types' family.valid fresh,leftReal,?_,?_⟩
  · change t.scalars.work+1+t.frame.state.storage.work = t.scalars.work+t.frame.state.storage.work+1
    omega
  · rw [left_peak,left_scalar_peak]
    have length : (t.scalars.memory.take s.scalars.memory.length).length = s.scalars.memory.length := by
      simp [List.length_take,Nat.min_eq_left fits']
    simp only [length,Nat.add_zero]
    rfl

theorem leave_matches (params : List Parameter) (outer restored : DynamicStmt.State) (s : NState)
    (before : Realizes params outer.locals outer.contents s) (pure : DynamicControl.Step) (actual : NStep)
    (matched : Matches params pure actual) (left : DynamicControl.leave outer pure.state = some restored)
    (fresh : ∀ owner, actual.state.frame.state.forest.context owner ≠ some (s.scope+1)) :
    s.leave actual.state actual.returned = some (s.left actual.state) ∧
      Matches params {pure with state := restored} {actual with state := s.left actual.state} ∧
      (s.left actual.state).work = actual.state.work+1 := by
  obtain ⟨ran,real,work,_⟩ := leave_sound params outer pure.state restored s actual.state before matched.state pure.returned left fresh
  exact ⟨by rw [matched.returned]; exact ran,⟨real,matched.returned,matched.breaking⟩,work⟩

theorem scope (params : List Parameter) (body : Command) (outer : DynamicStmt.State) (s : NState)
    (before : Realizes params outer.locals outer.contents s) (Q : DynamicControl.Step → NStep → Prop)
    (run : DynamicControlBridge.Runs params body outer {s with scope := s.scope+1} fun pure actual =>
      ∃ restored, DynamicControl.leave outer pure.state = some restored ∧
        (∀ owner, actual.state.frame.state.forest.context owner ≠ some (s.scope+1)) ∧
        Q {pure with state := restored} {actual with state := s.left actual.state}) :
    DynamicControlBridge.Runs params (.scope body) outer s Q := by
  apply DynamicControlBridge.Runs.scope
  apply run.inspect.mono
  intro pure actual ⟨matched,restored,pLeft,fresh,post⟩
  obtain ⟨aLeft,matched',_⟩ := leave_matches params outer restored s before pure actual matched pLeft fresh
  exact ⟨restored,s.left actual.state,pLeft,aLeft,matched',post⟩

end Proofs.DynamicScopeAuto
