import Proofs.CppNoResizeRun

namespace Proofs.CppCallFrame
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppEvalFrame Proofs.DynamicResultValid

theorem resolve_frame (s t : NState) (p : Proofs.CppVectorBindings.Parameter) (arg : NArgument) (r : Resolved)
    (actual : resolve s p arg = some (t,r)) : FrameSame s.frame t.frame := by
  cases p with
  | scalar ty address wr =>
    cases address with
    | false =>
      cases arg with
      | value e =>
        unfold resolve at actual
        try dsimp only at actual
        split at actual
        · obtain ⟨⟨q,v⟩,ev,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj rest)
          change q = t at eq
          subst t
          exact expression_frame e s q v ev
        · simp at actual
      | _ => simp [resolve] at actual
    | true =>
      cases arg with
      | scalarReference slot =>
        unfold resolve at actual
        obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ actual
        try dsimp only at rest
        split at rest
        · have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = t at eq
          subst t
          exact ⟨rfl,rfl⟩
        · simp at rest
      | _ => simp [resolve] at actual
  | vector ty wr | nested ty wr =>
    cases arg with
    | vectorReference slot =>
      unfold resolve at actual
      obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
      obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
      try dsimp only at rest
      cases header : binding.header with
      | child address =>
        simp only [header] at rest
        first
        | contradiction
        | split at rest
          · have eq := congrArg Prod.fst (Option.some.inj rest)
            change _ = t at eq
            subst t
            exact ⟨rfl,rfl⟩
          · simp at rest
      | root scope =>
        simp only [header] at rest
        split at rest
        · have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = t at eq
          subst t
          exact ⟨rfl,rfl⟩
        · simp at rest
    | _ => simp [resolve] at actual

theorem resolve_all_frame (s t : NState) (ps : List Proofs.CppVectorBindings.Parameter)
    (args : List NArgument) (rs : List Resolved) (actual : resolveAll s ps args = some (t,rs)) : FrameSame s.frame t.frame := by
  induction ps generalizing s args t rs with
  | nil =>
    cases args with
    | nil =>
      have eq := congrArg Prod.fst (Option.some.inj actual)
      change s = t at eq
      subst t
      exact ⟨rfl,rfl⟩
    | cons a args => simp [resolveAll] at actual
  | cons p ps ih =>
    cases args with
    | nil => simp [resolveAll] at actual
    | cons a args =>
      unfold resolveAll at actual
      obtain ⟨⟨q,r⟩,resolved,rest⟩ := bind_some _ _ _ actual
      obtain ⟨⟨u,us⟩,tail,rest⟩ := bind_some _ _ _ rest
      have eq := congrArg Prod.fst (Option.some.inj rest)
      change u = t at eq
      subst t
      exact (resolve_frame s q p a r resolved).trans (ih q u args us tail)

theorem root_frame (f g : Frame) (owner scope : Nat) (element : Element) (wr : Bool) (index : Nat)
    (actual : f.bindRoot owner element scope wr = some (g,index)) : FrameSame f g := by
  unfold Frame.bindRoot at actual
  obtain ⟨⟨buffer,tag⟩,_,rest⟩ := bind_some _ _ _ actual
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = g at eq
    subst g
    exact ⟨rfl,rfl⟩
  · simp at rest

theorem bind_one_frame (s t : NState) (r : Resolved) (actual : bindOne s r = some t) : FrameSame s.frame t.frame := by
  cases r with
  | scalar ty wr _ | scalarAddress ty _ wr =>
    unfold bindOne at actual
    obtain ⟨scalars,_,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact ⟨rfl,rfl⟩
  | vectorChild owner address ty wr =>
    unfold bindOne at actual
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact ⟨rfl,rfl⟩
  | vector owner scope ty wr | nestedRoot owner scope ty wr =>
    unfold bindOne at actual
    obtain ⟨⟨frame,index⟩,ran,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact root_frame s.frame frame owner scope _ wr index ran

theorem bind_all_frame (s t : NState) (rs : List Resolved) (actual : bindAll s rs = some t) : FrameSame s.frame t.frame := by
  induction rs generalizing s t with
  | nil =>
    have eq := Option.some.inj actual
    subst t
    exact ⟨rfl,rfl⟩
  | cons r rs ih =>
    unfold bindAll at actual
    obtain ⟨q,head,tail⟩ := bind_some _ _ _ actual
    exact (bind_one_frame s q r head).trans (ih q t tail)

theorem prepare_frame (s t : NState) (ps : List Proofs.CppVectorBindings.Parameter) (args : List NArgument)
    (actual : prepare s ps args = some t) : FrameSame s.frame t.frame := by
  unfold prepare at actual
  split at actual
  · obtain ⟨⟨q,rs⟩,resolved,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    have before := resolve_all_frame s q ps args rs resolved
    have after := bind_all_frame _ t rs rest
    exact before.trans after
  · simp at actual

theorem prepare_scope (s t : NState) (ps : List Proofs.CppVectorBindings.Parameter) (args : List NArgument)
    (actual : prepare s ps args = some t) : t.scope = s.scope+1 := by
  have one (a b : NState) (r : Resolved) (ran : bindOne a r = some b) : b.scope = a.scope := by
    cases r <;> unfold bindOne at ran
    all_goals
      obtain ⟨value,_,rest⟩ := bind_some _ _ _ ran
      have eq := Option.some.inj rest
      subst b
      rfl
  have all (rs : List Resolved) (a b : NState) (ran : bindAll a rs = some b) : b.scope = a.scope := by
    induction rs generalizing a b with
    | nil => have eq := Option.some.inj ran; subst b; rfl
    | cons r rs ih =>
      unfold bindAll at ran
      obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
      exact (ih next b tail).trans (one a next r head)
  unfold prepare at actual
  split at actual
  · obtain ⟨⟨q,rs⟩,_,rest⟩ := bind_some _ _ _ actual
    exact all rs _ t rest
  · simp at actual

open Proofs.CppNoResizeStmt Proofs.CppBufferHeaders Proofs.CppNoResizeScope Proofs.CppNestedEval Proofs.CppLoop

structure CallEffects (caller out : NState) : Prop where
  headers : SameHeaders caller.frame.state out.frame.state
  flags : out.frame.rootWritable = caller.frame.rootWritable
  vectorBindings : out.frame.bindings = caller.frame.bindings
  scopedState : out.scope = caller.scope
  slots : out.slots = caller.slots
  scalarBindings : out.scalars.bindings = caller.scalars.bindings
  base : out.scalars.baseMemory = caller.scalars.baseMemory
  memoryLength : out.scalars.memory.length = caller.scalars.memory.length
  scalarLive : liveS out = liveS caller

theorem CallEffects.refl (s : NState) : CallEffects s s :=
  ⟨SameHeaders.refl _,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem CallEffects.trans {s t u : NState} (a : CallEffects s t) (b : CallEffects t u) : CallEffects s u :=
  ⟨a.headers.trans b.headers,b.flags.trans a.flags,b.vectorBindings.trans a.vectorBindings,
    b.scopedState.trans a.scopedState,b.slots.trans a.slots,b.scalarBindings.trans a.scalarBindings,
    b.base.trans a.base,b.memoryLength.trans a.memoryLength,b.scalarLive.trans a.scalarLive⟩

theorem CallEffects.contexts {s t : NState} (effects : CallEffects s t)
    (before : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    ∀ owner scope, t.frame.state.forest.context owner = some scope → scope ≤ t.scope := by
  intro owner scope found
  rw [effects.headers.forest] at found
  rw [effects.scopedState]
  exact before owner scope found

theorem CallEffects.grant {s t : NState} (effects : CallEffects s t) (reference : Reference) :
    t.frame.grant reference = s.frame.grant reference := by
  simp only [Frame.grant,Frame.maximum,effects.vectorBindings,effects.flags,effects.headers.forest]

theorem finish_scalar_frame (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (flags : callee.frame.rootWritable = caller.frame.rootWritable)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) : CallEffects caller out := by
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner callee.scope found
    rw [scopeEq] at bound
    omega
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
      · rename_i guarded
        try dsimp only at actual
        split at actual
        · obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj finished)
          change callee.frame = frame at eq
          subst frame
          obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
          obtain ⟨post,rw⟩ := retire_frame callee.frame retired callee.scope fresh ran
          have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = out at eq
          subst out
          refine ⟨headers.trans post,rw.trans flags,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
          · change (callee.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length
            simp [List.length_take,Nat.min_eq_left guarded.1]
          · change (callee.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
                caller.scalars.bindings.length = liveS caller
            simp [List.length_take,Nat.min_eq_left guarded.1,liveS]
        · simp at actual
      · simp at actual

theorem call_headers (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument) (ret : Ret) (retType : Ty)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : program.callFuel fuel caller args = .finished (out,ret)) : CallEffects caller out := by
  cases prep : prepare caller program.parameters args with
  | none => simp [NProgram.callFuel,prep,liftChecked,bind,Outcome.bind] at actual
  | some init =>
    have initFrame := prepare_frame caller init program.parameters args prep
    have initScope := prepare_scope caller init program.parameters args prep
    have innerContexts : ∀ owner scope, init.frame.state.forest.context owner = some scope → scope ≤ init.scope := by
      intro owner scope found
      rw [initFrame.1] at found
      rw [initScope]
      exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
    cases ran : CppNestedProgram.runFuel fuel program.body init with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | finished step =>
      have body := Proofs.CppNoResizeRun.run_headers fuel program.body init step allowed innerContexts ran
      have headers : SameHeaders caller.frame.state step.state.frame.state := by
        rw [← initFrame.1]
        exact body.headers
      simp only [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
      split at actual
      · simp at actual
      · cases ended : Proofs.CppNestedCall.finish caller step.state program.result step.returned with
        | none => simp [ended,liftChecked] at actual
        | some pair =>
          simp only [ended,liftChecked] at actual
          have eq := Outcome.finished.inj actual
          subst pair
          rw [scalar] at ended
          exact finish_scalar_frame caller step.state out _ step.returned ret headers
            (body.flags.trans initFrame.2) (body.scopedState.trans initScope) contexts ended

end Proofs.CppCallFrame
