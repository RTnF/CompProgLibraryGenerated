import Proofs.DynamicStmtEffects

namespace Proofs.DynamicEffectRuns
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicControlBridge Proofs.DynamicPhysicalEffects Proofs.DynamicForestEffects

-- Coupled execution with physical effects retained through composition.
def Runs (params : List Parameter) (command : Command) (st : DynamicStmt.State) (s : NState)
    (Q : DynamicControl.Step → NStep → Prop) : Prop :=
  DynamicControlBridge.Runs params command st s (fun p a => Change s a.state ∧ Q p a)

theorem Runs.mono {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {P Q : DynamicControl.Step → NStep → Prop} (run : Runs params command st s P)
    (weaker : ∀ p a, P p a → Q p a) : Runs params command st s Q :=
  DynamicControlBridge.Runs.mono run (fun p a post => ⟨post.1,weaker p a post.2⟩)

theorem Runs.inspect {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {Q : DynamicControl.Step → NStep → Prop} (run : Runs params command st s Q) :
    Runs params command st s (fun p a => Matches params p a ∧ Q p a) :=
  DynamicControlBridge.Runs.mono (DynamicControlBridge.Runs.inspect run) (fun _ _ post => ⟨post.2.1,post.1,post.2.2⟩)

theorem Runs.primitive (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) (stmt : NStmt) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params stmt st = some result) (available : DynamicAppendAuto.Available params st s stmt) :
    Runs params (.primitive stmt) st s (fun p _ => p = DynamicControl.ofStmt result) := by
  obtain ⟨a,ran,matched,effect⟩ := DynamicStmtEffects.sound params st s real stmt result pure available
  exact DynamicControlBridge.Runs.primitive pure ran matched ⟨effect,rfl⟩

theorem Runs.breakLoop (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) :
    Runs params .breakLoop st s (fun p _ => p = ⟨st,none,true⟩) :=
  DynamicControlBridge.Runs.of_run (fuel := 1) rfl rfl ⟨⟨real.locals,real.heap⟩,rfl,rfl⟩ ⟨charge s 1 0,rfl⟩

theorem Runs.sequence {params : List Parameter} {first rest : Command} {st : DynamicStmt.State} {s : NState}
    {Q : DynamicControl.Step → NStep → Prop}
    (run : Runs params first st s fun p a =>
      ((p.returned.isSome = true ∨ p.breaking = true) ∧ Q p a) ∨
      (p.returned = none ∧ p.breaking = false ∧ Runs params rest p.state a.state Q)) :
    Runs params (.sequence first rest) st s Q := by
  apply DynamicControlBridge.Runs.sequence
  apply DynamicControlBridge.Runs.mono run
  intro p a ⟨effect,paths⟩
  rcases paths with ⟨stop,post⟩ | ⟨ret,br,tail⟩
  · exact Or.inl ⟨stop,effect,post⟩
  · exact Or.inr ⟨ret,br,DynamicControlBridge.Runs.mono tail (fun _ _ post => ⟨effect.trans post.1,post.2⟩)⟩

theorem Runs.seq {params : List Parameter} {first rest : Command} {st : DynamicStmt.State} {s : NState}
    {Q : DynamicControl.Step → NStep → Prop}
    (run : Runs params first st s fun p a => p.returned = none ∧ p.breaking = false ∧
      Runs params rest p.state a.state Q) : Runs params (.sequence first rest) st s Q :=
  Runs.sequence (run.mono fun _ _ post => Or.inr post)

theorem Runs.branch {params : List Parameter} {condition : NExpr} {yes no : Command}
    {st : DynamicStmt.State} {s : NState} {v : Int} {Q : DynamicControl.Step → NStep → Prop}
    (real : Realizes params st.locals st.contents s) (value : denote params st.locals st.contents condition = some v)
    (branches : ∀ next, condition.eval s = some (next,v) →
      Realizes params st.locals st.contents ((next.release s).charge 1 0) →
      Runs params (if v = 0 then no else yes) st ((next.release s).charge 1 0) Q) :
    Runs params (.branch condition yes no) st s Q := by
  obtain ⟨_,next,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) v value) s real
  apply DynamicControlBridge.Runs.branch real (DynamicExprAuto.ready _ _ _ _) value
  intro t evaluated after
  have same : next = t := (Prod.mk.inj (Option.some.inj (ev.1.symm.trans evaluated))).1
  subst t
  have effect : Change s ((next.release s).charge 1 0) :=
    (goodF ev.2.1).trans ((release next s).trans (charge _ 1 0))
  exact DynamicControlBridge.Runs.mono (branches next ev.1 after) (fun _ _ post => ⟨effect.trans post.1,post.2⟩)

-- No owned vector is created in this scope. Pure body preservation supplies
-- the scalar leave check, while the physical certificate preserves absence.
theorem Runs.scope {params : List Parameter} {body : Command} {st : DynamicStmt.State} {s : NState}
    {Q : DynamicControl.Step → NStep → Prop}
    (real : Realizes params st.locals st.contents s) (absent : NoScope s.frame.state.forest (s.scope+1))
    (run : Runs params body st {s with scope := s.scope+1} fun p a =>
      ∀ final, DynamicControl.leave st p.state = some final →
        Q {p with state := final} {a with state := s.left a.state}) :
    Runs params (.scope body) st s Q := by
  apply DynamicScopeAuto.scope params body st s real
  apply DynamicControlBridge.Runs.mono (DynamicControlPreserve.coupled run)
  intro p a ⟨preserved,effect,post⟩
  obtain ⟨final,left⟩ := DynamicPreserve.leave_exists st p.state preserved.2
  exact ⟨final,left,effect.1.absent _ absent,⟨effect.1,rfl⟩,post final left⟩

-- The ghost counter proves termination of continuing iterations; physical
-- effects are accumulated independently, including return and break exits.
theorem Runs.whileGhostStop {params : List Parameter} {condition : NExpr} {body : Command}
    (I : Nat → DynamicStmt.State → NState → Prop) (Q : DynamicControl.Step → NStep → Prop)
    (step : ∀ g st s, Realizes params st.locals st.contents s → I g st s →
      ∃ v, denote params st.locals st.contents condition = some v ∧
      ∀ next, condition.eval s = some (next,v) →
        Realizes params st.locals st.contents ((next.release s).charge 1 0) →
        (v = 0 → Q ⟨st,none,false⟩ ⟨(next.release s).charge 1 0,none,false⟩) ∧
        (v ≠ 0 → Runs params body st ((next.release s).charge 1 0) fun p a =>
          (p.returned.isSome = true ∧ Q p a) ∨
          (p.returned = none ∧ ((p.breaking = true ∧ Q {p with breaking := false} {a with breaking := false}) ∨
            (p.breaking = false ∧ ∃ g', g' < g ∧ I g' p.state a.state))))) :
    ∀ g st s, Realizes params st.locals st.contents s → I g st s → Runs params (.whileLoop condition body) st s Q := by
  intro g st seed real inv
  apply DynamicControlBridge.Runs.whileGhostStop
    (fun g st s => I g st s ∧ Change seed s)
    (fun p a => Change seed a.state ∧ Q p a) ?_ g st seed real ⟨inv,Change.refl seed⟩
  intro count current s before ⟨inv,priorEffect⟩
  obtain ⟨v,value,paths⟩ := step count current s before inv
  refine ⟨v,value,DynamicExprAuto.ready _ _ _ _,?_⟩
  intro next evaluated after
  obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) v value) s before
  have same : t = next := (Prod.mk.inj (Option.some.inj (ev.1.symm.trans evaluated))).1
  subst t
  have guard : Change seed ((next.release s).charge 1 0) :=
    priorEffect.trans ((goodF ev.2.1).trans ((release next s).trans (charge _ 1 0)))
  obtain ⟨exit,continues⟩ := paths next evaluated after
  refine ⟨fun zero => ⟨guard,exit zero⟩,?_⟩
  intro nonzero
  apply DynamicControlBridge.Runs.mono (continues nonzero)
  intro p a ⟨effect,post⟩
  have total := guard.trans effect
  rcases post with ⟨ret,good⟩ | ⟨ret,⟨br,good⟩ | ⟨br,count',less,inv'⟩⟩
  · exact Or.inl ⟨ret,total,good⟩
  · exact Or.inr ⟨ret,Or.inl ⟨br,total,good⟩⟩
  · exact Or.inr ⟨ret,Or.inr ⟨br,count',less,inv',total⟩⟩

-- All physical exit conditions are obtained from the compositional body
-- certificate. The caller only supplies absence in the prospective scope.
theorem call (params : List Parameter) (st : DynamicStmt.State) (caller : NState)
    (real : Realizes params st.locals st.contents caller) (program : NProgram) (arguments : List NArgument)
    (rs : List Proofs.CppNestedCall.Resolved)
    (args : DynamicArguments.resolveAll params st program.parameters arguments = some rs)
    (absent : NoScope caller.frame.state.forest (caller.scope+1))
    (body : ∀ initial, Proofs.CppNestedCall.prepare caller program.parameters arguments = some initial →
      Realizes (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) (snapshot initial) st.contents initial →
      Runs (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) program.body ⟨snapshot initial,st.contents⟩ initial
        (fun p _ => p.breaking = false ∧ ∃ value, DynamicFinish.resultValue program.result p.returned = some value)) :
    ∃ (fuel : Nat) (final : DynamicStmt.State) (next : NState) (value : Ret),
      program.callFuel fuel caller arguments = .finished (next,value) ∧ Realizes params final.locals final.contents next := by
  apply DynamicCallEffects.sound params st caller real program arguments rs args absent
  intro initial prepared initialReal
  exact DynamicControlBridge.Runs.mono (body initial prepared initialReal)
    (fun _ _ post => ⟨post.2.1,post.1,post.2.2⟩)

end Proofs.DynamicEffectRuns
