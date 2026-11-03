import Proofs.BeatsBindingExpr

namespace Proofs.BeatsBindingCycle
open Proofs.CppNestedProgram Proofs.CppScalar Proofs.CppMixedInvoke
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.BeatsSlotCycle (rotate cycle rotate_lookup rotate_length)

theorem rotate_take (xs : List α) (long : 16 ≤ xs.length) (n : Nat) (bound : 16 ≤ n) :
    rotate (xs.take n) = (rotate xs).take n := by
  apply List.ext_getElem?
  intro i
  have taken : 16 ≤ (xs.take n).length := by simp only [List.length_take]; omega
  rw [rotate_lookup _ taken,List.getElem?_take,List.getElem?_take,rotate_lookup _ long]
  by_cases inside : i < n
  · have mapped : cycle i < n := by
      unfold cycle
      split <;> (try split) <;> omega
    simp only [ite_eq_left inside,ite_eq_left mapped]
  · have fixed : cycle i = i := Proofs.BeatsSlotCycle.cycle_ge i (by omega)
    simp only [fixed,ite_eq_right inside]

theorem release_view (after before : NState) (long : 16 ≤ after.frame.bindings.length)
    (base : 16 ≤ before.frame.bindings.length) :
    view (after.release before) = (view after).release (view before) := by
  simp only [view,NState.release,rebind,rotate_length _ base,rotate_take _ long _ base]

theorem declared_view (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    view (s.declared ty writable value) = (view s).declared ty writable value := by
  simp only [view,NState.declared,List.map_append,List.map_cons,List.map_nil,location]

theorem enter_view (s : NState) : view {s with scope := s.scope+1} = {view s with scope := s.scope+1} := rfl

def exitFrame (f : Frame) (scope : Nat) (returned : Option Ret) : Option Frame := do
  let moved ← match returned with
    | some (.vector owner element) => f.transferRoot owner element (scope+1) scope
    | _ => some f
  moved.retireScope (scope+1)

theorem exitFrame_rebind (f : Frame) (scope : Nat) (returned : Option Ret) :
    exitFrame (rebind f) scope returned = (exitFrame f scope returned).map rebind := by
  cases returned with
  | none =>
    simp only [exitFrame,Bind.bind,Option.bind_some,Frame.retireScope,rebind]
    cases f.state.retireScope (scope+1) <;> rfl
  | some ret =>
    cases ret with
    | scalar value =>
      simp only [exitFrame,Bind.bind,Option.bind_some,Frame.retireScope,rebind]
      cases f.state.retireScope (scope+1) <;> rfl
    | unit =>
      simp only [exitFrame,Bind.bind,Option.bind_some,Frame.retireScope,rebind]
      cases f.state.retireScope (scope+1) <;> rfl
    | vector owner element =>
      simp only [exitFrame,Frame.transferRoot,Frame.retireScope,rebind,Bind.bind,Option.map_bind,Function.comp_def]
      cases f.state.transfer owner element (scope+1) scope with
      | none => rfl
      | some moved =>
        dsimp only [Option.bind_some]
        cases moved.retireScope (scope+1) <;> rfl

private theorem retired_bindings (f out : Frame) (scope : Nat)
    (ran : f.retireScope scope = some out) : out.bindings = f.bindings := by
  unfold Frame.retireScope at ran
  cases found : f.state.retireScope scope with
  | none => simp only [found,Bind.bind,Option.bind_none] at ran; contradiction
  | some state =>
    simp only [found,Bind.bind,Option.bind_some] at ran
    cases ran
    rfl

private theorem transferred_bindings (f out : Frame) (owner : Nat) (el : Element) (fromScope toScope : Nat)
    (ran : f.transferRoot owner el fromScope toScope = some out) : out.bindings = f.bindings := by
  unfold Frame.transferRoot at ran
  cases found : f.state.transfer owner el fromScope toScope with
  | none => simp only [found,Bind.bind,Option.bind_none] at ran; contradiction
  | some state =>
    simp only [found,Bind.bind,Option.bind_some] at ran
    cases ran
    rfl

theorem exitFrame_bindings (f out : Frame) (scope : Nat) (returned : Option Ret)
    (ran : exitFrame f scope returned = some out) : out.bindings = f.bindings := by
  cases returned with
  | none => exact retired_bindings f out (scope+1) ran
  | some ret =>
    cases ret with
    | scalar value => exact retired_bindings f out (scope+1) ran
    | unit => exact retired_bindings f out (scope+1) ran
    | vector owner element =>
      unfold exitFrame at ran
      cases found : f.transferRoot owner element (scope+1) scope with
      | none => simp only [found,Bind.bind,Option.bind_none] at ran; contradiction
      | some moved =>
        simp only [found,Bind.bind,Option.bind_some] at ran
        exact (retired_bindings moved out (scope+1) ran).trans
          (transferred_bindings f moved owner element (scope+1) scope found)

def leaveFinish (outer inner : NState) (retired : Frame) : NState :=
  let scalars : Proofs.CppState.State := {outer.scalars with
    memory := inner.scalars.memory.take outer.scalars.memory.length,
    work := inner.scalars.work+1,peak := max outer.scalars.peak inner.scalars.peak}
  let frame := {retired with bindings := retired.bindings.take outer.frame.bindings.length}
  (⟨scalars.observe 0,frame,outer.slots,outer.scope,max outer.peak inner.peak⟩ : NState).observe

theorem leaveFinish_view (outer inner : NState) (frame : Frame)
    (base : 16 ≤ outer.frame.bindings.length) (long : 16 ≤ frame.bindings.length) :
    view (leaveFinish outer inner frame) = leaveFinish (view outer) (view inner) (rebind frame) := by
  simp only [leaveFinish,view,rebind,NState.observe,rotate_length _ base,rotate_take _ long _ base]

private theorem bind_some_map {α β : Type} (o : Option α) (f : α → β) :
    o.bind (fun a => some (f a)) = o.map f := by cases o <;> rfl

theorem leave_normal (outer inner : NState) (returned : Option Ret) :
    outer.leave inner returned =
      if outer.scalars.memory.length ≤ inner.scalars.memory.length ∧
        (inner.scalars.memory.take outer.scalars.memory.length).map Proofs.CppState.Cell.type =
          outer.scalars.memory.map Proofs.CppState.Cell.type then
        (exitFrame inner.frame outer.scope returned).map (leaveFinish outer inner) else none := by
  cases returned with
  | none =>
    unfold NState.leave
    split
    · simp only [exitFrame,Bind.bind,Option.bind_some,← bind_some_map]
      rfl
    · rfl
  | some ret =>
    cases ret <;> unfold NState.leave
    all_goals
      split
      · simp only [exitFrame,Bind.bind,Option.bind_some,← bind_some_map,Option.bind_assoc]
        rfl
      · rfl

theorem leave_view (outer inner : NState) (returned : Option Ret)
    (base : 16 ≤ outer.frame.bindings.length) (long : 16 ≤ inner.frame.bindings.length) :
    (outer.leave inner returned).map view = (view outer).leave (view inner) returned := by
  let ok := outer.scalars.memory.length ≤ inner.scalars.memory.length ∧
    (inner.scalars.memory.take outer.scalars.memory.length).map Proofs.CppState.Cell.type =
      outer.scalars.memory.map Proofs.CppState.Cell.type
  rw [leave_normal,leave_normal]
  change (if ok then (exitFrame inner.frame outer.scope returned).map (leaveFinish outer inner) else none).map view =
    if ok then (exitFrame (rebind inner.frame) outer.scope returned).map (leaveFinish (view outer) (view inner)) else none
  by_cases good : ok
  · simp only [ite_eq_left good,exitFrame_rebind,Option.map_map,Function.comp_def]
    cases ran : exitFrame inner.frame outer.scope returned with
    | none => rfl
    | some frame =>
      simp only [Option.map_some]
      exact congrArg some (leaveFinish_view outer inner frame base (by rw [exitFrame_bindings _ _ _ _ ran]; exact long))
  · simp only [ite_eq_right good,Option.map_none]

def viewStep (step : NStep) : NStep := {step with state := view step.state}

theorem declare_run_view (s : NState) (long : 16 ≤ s.frame.bindings.length)
    (ty : Ty) (writable : Bool) (e : NExpr) :
    ((NStmt.declare ty writable e).run s).map viewStep = (NStmt.declare ty writable e).run (view s) := by
  have equal := expr_eval_view s long e
  cases ran : e.eval s with
  | none =>
    simp only [ran,Option.map_none] at equal
    simp [NStmt.run,ran,← equal]
  | some pair =>
    obtain ⟨t,v⟩ := pair
    have nextLong : 16 ≤ t.frame.bindings.length := Nat.le_trans long (expr_binding_growth s t e v ran)
    simp only [ran,Option.map_some] at equal
    simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
    rw [← release_view t s nextLong long]
    cases converted : ty.convert v with
    | none => simp
    | some value =>
      simp [viewStep,view,NState.release,List.map_append,location] <;> rfl

theorem assign_run_view (s : NState) (long : 16 ≤ s.frame.bindings.length)
    (slot : Nat) (ty : Ty) (e : NExpr) :
    ((NStmt.assign slot ty e).run s).map viewStep = (NStmt.assign slot ty e).run (view s) := by
  have equal := expr_eval_view s long e
  cases ran : e.eval s with
  | none =>
    simp only [ran,Option.map_none] at equal
    simp [NStmt.run,ran,← equal]
  | some pair =>
    obtain ⟨t,v⟩ := pair
    have nextLong : 16 ≤ t.frame.bindings.length := Nat.le_trans long (expr_binding_growth s t e v ran)
    simp only [ran,Option.map_some] at equal
    simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
    rw [← release_view t s nextLong long,scalarCell]
    cases resolved : (t.release s).scalarCell slot ty with
    | none => simp
    | some pair =>
      obtain ⟨binding,cell⟩ := pair
      cases writable : binding.writable <;> cases converted : ty.convert v <;>
        simp [writable,viewStep,view,NState.release] <;> rfl

private theorem bind_some {α β : Type} (o : Option α) (f : α → Option β) (v : β)
    (ran : o.bind f = some v) : ∃ a, o = some a ∧ f a = some v := Option.bind_eq_some_iff.mp ran

theorem commit_bindings (f out : Frame) (owner : Nat) (el : Element)
    (result : Proofs.CppVector.Result Value Unit) (ran : f.commit owner el result = some out) :
    out.bindings = f.bindings := by
  unfold Frame.commit at ran
  cases found : f.object owner el with
  | none => simp only [found] at ran; contradiction
  | some pair =>
    simp only [found] at ran
    split at ran
    · split at ran
      · cases ran; rfl
      · simp at ran
    · simp at ran

theorem write_bindings (f out : Frame) (ref : Reference) (value : Int)
    (ran : f.write ref value = some out) : out.bindings = f.bindings := by
  unfold Frame.write at ran
  obtain ⟨writable,_,rest⟩ := bind_some _ _ _ ran
  split at rest
  · obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨buffer,tag⟩ := pair
    dsimp only at rest
    obtain ⟨result,_,rest⟩ := bind_some _ _ _ rest
    exact commit_bindings f out ref.address.owner (.integer ref.element) result rest
  · simp at rest

def writeValue (f : Frame) (i : Nat) (ty : Ty) (index value : Int) : Option (Frame × Unit) := do
  let ref ← f.elementRef i ty index
  let changed ← f.write ref value
  some (changed,())

theorem writeValue_map (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (ty : Ty) (index value : Int) :
    writeValue (rebind f) (Proofs.BeatsSlotCycle.uncycle i) ty index value =
      (writeValue f i ty index value).map (fun p => (rebind p.1,p.2)) := by
  unfold writeValue
  rw [elementRef f long]
  simp only [Bind.bind,Option.map_bind,Function.comp_def]
  cases f.elementRef i ty index with
  | none => rfl
  | some ref =>
    dsimp only [Option.map_some,Option.bind_some]
    rw [write f long]
    cases f.write ref value <;> rfl

theorem writeValue_growth (f out : Frame) (i : Nat) (ty : Ty) (index value : Int) (u : Unit)
    (ran : writeValue f i ty index value = some (out,u)) : f.bindings.length ≤ out.bindings.length := by
  unfold writeValue at ran
  obtain ⟨ref,_,rest⟩ := bind_some _ _ _ ran
  obtain ⟨changed,written,rest⟩ := bind_some _ _ _ rest
  cases rest
  exact Nat.le_of_eq (congrArg List.length (write_bindings f out ref value written)).symm

theorem release_charge (after before : NState) (w p : Nat) :
    (after.charge w p).release before = (after.release before).charge w p := rfl

theorem EvalRel.toReleasedStep {f g : NState → Option (NState × Unit)} (related : EvalRel id f g)
    (s : NState) (long : 16 ≤ s.frame.bindings.length) :
    ((f s).map (fun p => (⟨p.1.release s,none,false⟩ : NStep))).map viewStep =
      (g (view s)).map (fun p => (⟨p.1.release (view s),none,false⟩ : NStep)) := by
  rw [← related.commute s long]
  cases ran : f s with
  | none => rfl
  | some pair =>
    simp only [Option.map_some,viewStep]
    rw [release_view pair.1 s (Nat.le_trans long (related.growth s pair.1 pair.2 ran)) long]

theorem write_run_view (s : NState) (long : 16 ≤ s.frame.bindings.length)
    (c : Container) (ty : Ty) (index value : NExpr) :
    ((NStmt.write c ty index value).run s).map viewStep = (NStmt.write c ty index value).run (view s) := by
  have all := ((expr_related value).precharge 0 (c.nodes+index.nodes+value.nodes+3)).bind_id
    (fun v => (container_related c).bind
      (k := fun owner s => (index.eval s).bind fun (t,position) =>
        frameStep (fun frame => writeValue frame owner ty position v) 1 0 t)
      (fun owner => (expr_related index).bind_id (fun position =>
        frameStep_related id (fun frame => writeValue frame owner ty position v)
          (fun frame => writeValue frame (Proofs.BeatsSlotCycle.uncycle owner) ty position v)
          (fun f wide => (writeValue_map f wide owner ty position v).symm)
          (fun f out u ran => writeValue_growth f out owner ty position v u ran) 1 0)))
  simpa only [Bind.bind,NStmt.run,frameStep,Proofs.BeatsSlotCycle.frameStep,writeValue,
    Option.map_bind,Option.map_map,Function.comp_def,Option.map_some,Option.bind_some,
    Option.bind_assoc,release_charge,id_eq] using all.toReleasedStep s long

end Proofs.BeatsBindingCycle
