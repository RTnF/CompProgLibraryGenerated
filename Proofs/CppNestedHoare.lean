import Proofs.CppNestedSim

namespace Proofs.CppNestedHoare
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppLoop (Outcome liftChecked)

theorem runFuel_success_mono (fuel extra : Nat) (command : Command) (s : NState) (step : NStep)
    (success : runFuel fuel command s = .finished step) :
    runFuel (fuel+extra) command s = .finished step := by
  induction fuel generalizing command s step with
  | zero => simp [runFuel] at success
  | succ fuel ih =>
      have added : fuel+1+extra = (fuel+extra)+1 := by omega
      rw [added]
      cases command with
      | primitive statement => simpa [runFuel] using success
      | breakLoop => simpa [runFuel] using success
      | scope body =>
          cases ran : runFuel fuel body {s with scope := s.scope+1} with
          | fault => simp [runFuel,ran,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
          | finished middle =>
              have more := ih body {s with scope := s.scope+1} middle ran
              simpa [runFuel,ran,more,bind,Outcome.bind] using success
      | sequence first rest =>
          cases ran : runFuel fuel first s with
          | fault => simp [runFuel,ran,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
          | finished middle =>
              have more := ih first s middle ran
              by_cases stop : (middle.returned.isSome || middle.breaking) = true
              · simpa [runFuel,ran,more,bind,pure,Outcome.bind,stop] using success
              · have tail : runFuel fuel rest middle.state = .finished step := by
                  simpa [runFuel,ran,bind,Outcome.bind,stop] using success
                have moreTail := ih rest middle.state step tail
                simp [runFuel,more,moreTail,bind,Outcome.bind,stop]
      | branch condition yes no =>
          cases evaluated : condition.eval s with
          | none => simp [runFuel,evaluated,liftChecked,bind,Outcome.bind] at success
          | some pair =>
              rcases pair with ⟨next,value⟩
              by_cases zero : value = 0
              · have ran : runFuel fuel no ((next.release s).charge 1 0) = .finished step := by
                  simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using success
                have more := ih no ((next.release s).charge 1 0) step ran
                simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using more
              · have ran : runFuel fuel yes ((next.release s).charge 1 0) = .finished step := by
                  simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using success
                have more := ih yes ((next.release s).charge 1 0) step ran
                simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using more
      | whileLoop condition body =>
          cases evaluated : condition.eval s with
          | none => simp [runFuel,evaluated,liftChecked,bind,Outcome.bind] at success
          | some pair =>
              rcases pair with ⟨next,value⟩
              by_cases zero : value = 0
              · simpa [runFuel,evaluated,liftChecked,bind,pure,Outcome.bind,zero] using success
              · cases ran : runFuel fuel body ((next.release s).charge 1 0) with
                | fault => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero] at success
                | exhausted => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero] at success
                | finished middle =>
                    have more := ih body ((next.release s).charge 1 0) middle ran
                    by_cases returned : middle.returned.isSome = true
                    · simpa [runFuel,evaluated,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned] using success
                    · by_cases breaking : middle.breaking = true
                      · simpa [runFuel,evaluated,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned,breaking] using success
                      · have tail : runFuel fuel (.whileLoop condition body) middle.state = .finished step := by
                          simpa [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero,returned,breaking] using success
                        have moreTail := ih (.whileLoop condition body) middle.state step tail
                        simp [runFuel,evaluated,more,moreTail,liftChecked,bind,Outcome.bind,zero,returned,breaking]
      | invokeScalar program arguments =>
          cases evaluated : arguments.mapM s.scalars.evaluate with
          | none => simp [runFuel,evaluated,liftChecked,bind,Outcome.bind] at success
          | some values =>
              cases ran : program.callFuel fuel s.scalars.memory
                  (values.map fun value => CppState.Argument.value value.value) with
              | fault => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind] at success
              | exhausted => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind] at success
              | finished result =>
                  have more := Proofs.CppLoop.LoopProgram.callFuel_success_mono program fuel extra _ _ _ ran
                  simpa [runFuel,evaluated,ran,more,liftChecked,bind,Outcome.bind] using success

theorem runFuel_success_unique (first second : Nat) (command : Command) (s : NState)
    (a b : NStep) (one : runFuel first command s = .finished a)
    (two : runFuel second command s = .finished b) : a = b := by
  have oneMore := runFuel_success_mono first second command s a one
  have twoMore := runFuel_success_mono second first command s b two
  rw [Nat.add_comm second first,oneMore] at twoMore
  exact Outcome.finished.inj twoMore

-- A successful run with some fuel, and its post-condition on the final step.
def RunsTo (command : Command) (s : NState) (post : NStep → Prop) : Prop :=
  ∃ fuel step, runFuel fuel command s = .finished step ∧ post step

theorem RunsTo.mono {command : Command} {s : NState} {P Q : NStep → Prop}
    (ran : RunsTo command s P) (weaker : ∀ step, P step → Q step) : RunsTo command s Q := by
  obtain ⟨fuel,step,run,post⟩ := ran
  exact ⟨fuel,step,run,weaker step post⟩

theorem RunsTo.primitive {statement : NStmt} {s : NState} {step : NStep} {Q : NStep → Prop}
    (ran : statement.run s = some step) (post : Q step) : RunsTo (.primitive statement) s Q :=
  ⟨1,step,by simp [runFuel,ran,liftChecked],post⟩

theorem RunsTo.sequence {first rest : Command} {s : NState} {Q : NStep → Prop}
    (ran : RunsTo first s fun middle =>
      (middle.returned.isSome = true ∨ middle.breaking = true ∧ True) ∧ Q middle ∨
      (middle.returned = none ∧ middle.breaking = false ∧ RunsTo rest middle.state Q)) :
    RunsTo (.sequence first rest) s Q := by
  obtain ⟨fuel,middle,run,post⟩ := ran
  rcases post with ⟨stop,good⟩ | ⟨none,notBreaking,tail⟩
  · refine ⟨fuel+1,middle,?_,good⟩
    have halted : (middle.returned.isSome || middle.breaking) = true := by
      rcases stop with h | ⟨h,_⟩ <;> simp [h]
    simp [runFuel,run,halted,bind,pure,Outcome.bind]
  · obtain ⟨tailFuel,step,tailRun,tailPost⟩ := tail
    have continues : ¬ (middle.returned.isSome || middle.breaking) = true := by
      simp [none,notBreaking]
    refine ⟨fuel+tailFuel+1,step,?_,tailPost⟩
    have first' := runFuel_success_mono fuel tailFuel first s middle run
    have rest' := runFuel_success_mono tailFuel fuel rest middle.state step tailRun
    rw [Nat.add_comm tailFuel fuel] at rest'
    simp [runFuel,first',continues,rest',bind,Outcome.bind]

theorem RunsTo.scope {body : Command} {s : NState} {Q : NStep → Prop}
    (ran : RunsTo body {s with scope := s.scope+1} fun inner =>
      ∃ restored, s.leave inner.state inner.returned = some restored ∧
        Q {inner with state := restored}) : RunsTo (.scope body) s Q := by
  obtain ⟨fuel,inner,run,restored,leave,post⟩ := ran
  refine ⟨fuel+1,{inner with state := restored},?_,post⟩
  simp [runFuel,run,leave,liftChecked,bind,Outcome.bind]
  rfl

theorem RunsTo.branch {condition : NExpr} {yes no : Command} {s next : NState} {value : Int}
    {Q : NStep → Prop} (evaluated : condition.eval s = some (next,value))
    (ran : RunsTo (if value = 0 then no else yes) ((next.release s).charge 1 0) Q) :
    RunsTo (.branch condition yes no) s Q := by
  obtain ⟨fuel,step,run,post⟩ := ran
  refine ⟨fuel+1,step,?_,post⟩
  by_cases zero : value = 0
  · simp only [zero,if_true] at run
    simp [runFuel,evaluated,zero,run,liftChecked,bind,Outcome.bind]
  · simp only [zero,if_false] at run
    simp [runFuel,evaluated,zero,run,liftChecked,bind,Outcome.bind]

-- Loop rule: a measure strictly decreases on every iteration that continues.
theorem RunsTo.whileLoop {condition : NExpr} {body : Command} (I : NState → Prop)
    (measure : NState → Nat) (Q : NStep → Prop)
    (step : ∀ t, I t → ∃ u v, condition.eval t = some (u,v) ∧
      (v = 0 → Q ⟨(u.release t).charge 1 0,none,false⟩) ∧
      (v ≠ 0 → RunsTo body ((u.release t).charge 1 0) fun inner =>
        inner.returned = none ∧ inner.breaking = false ∧ I inner.state ∧ measure inner.state < measure t)) :
    ∀ bound s, measure s ≤ bound → I s → RunsTo (.whileLoop condition body) s Q := by
  intro bound
  induction bound with
  | zero =>
      intro s small good
      obtain ⟨next,value,evaluated,exit,continues⟩ := step s good
      by_cases zero : value = 0
      · exact ⟨1,_,by simp [runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
      · obtain ⟨fuel,inner,run,_,_,_,smaller⟩ := continues zero
        omega
  | succ bound ih =>
      intro s small good
      obtain ⟨next,value,evaluated,exit,continues⟩ := step s good
      by_cases zero : value = 0
      · exact ⟨1,_,by simp [runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
      · obtain ⟨fuel,inner,run,none,notBreaking,good',smaller⟩ := continues zero
        obtain ⟨tailFuel,final,tailRun,post⟩ := ih inner.state (by omega) good'
        refine ⟨fuel+tailFuel+1,final,?_,post⟩
        have first := runFuel_success_mono fuel tailFuel body _ inner run
        have rest := runFuel_success_mono tailFuel fuel (.whileLoop condition body) inner.state final tailRun
        rw [Nat.add_comm tailFuel fuel] at rest
        simp [runFuel,evaluated,zero,first,none,notBreaking,rest,liftChecked,bind,pure,Outcome.bind]

theorem RunsTo.seq {first rest : Command} {s : NState} {Q : NStep → Prop}
    (ran : RunsTo first s fun middle => middle.returned = none ∧ middle.breaking = false ∧
      RunsTo rest middle.state Q) : RunsTo (.sequence first rest) s Q :=
  RunsTo.sequence (ran.mono fun middle post => Or.inr post)

theorem RunsTo.skip {s : NState} {Q : NStep → Prop} (post : Q ⟨s,none,false⟩) :
    RunsTo (.primitive .skip) s Q :=
  RunsTo.primitive (by simp [NStmt.run]) post

theorem RunsTo.seqSkip {command : Command} {s : NState} {Q : NStep → Prop}
    (ran : RunsTo command s fun step => step.returned = none ∧ step.breaking = false ∧ Q ⟨step.state,none,false⟩) :
    RunsTo (.sequence command (.primitive .skip)) s Q :=
  RunsTo.seq (ran.mono fun step ⟨noReturn,notBreaking,post⟩ =>
    ⟨noReturn,notBreaking,RunsTo.skip post⟩)

-- A scope whose body returns nothing: leaving it restores the enclosing state.
theorem RunsTo.scopeSimple {body : Command} {s : NState} {Q : NStep → Prop}
    (ran : RunsTo body {s with scope := s.scope+1} fun inner => inner.returned = none ∧ inner.breaking = false ∧
      ∃ restored, s.leave inner.state none = some restored ∧ Q ⟨restored,none,false⟩) :
    RunsTo (.scope body) s Q :=
  RunsTo.scope (ran.mono fun inner ⟨noReturn,notBreaking,restored,leave,post⟩ =>
    ⟨restored,by simpa [noReturn] using leave,by simpa [noReturn,notBreaking] using post⟩)

-- Loop rule with an explicit ghost counter that strictly decreases.
theorem RunsTo.whileGhost {condition : NExpr} {body : Command} (I : Nat → NState → Prop) (Q : NStep → Prop)
    (step : ∀ g t, I g t → ∃ u v, condition.eval t = some (u,v) ∧
      (v = 0 → Q ⟨(u.release t).charge 1 0,none,false⟩) ∧
      (v ≠ 0 → RunsTo body ((u.release t).charge 1 0) fun inner => inner.returned = none ∧
        inner.breaking = false ∧ ∃ g', g' < g ∧ I g' inner.state)) :
    ∀ bound g s, g ≤ bound → I g s → RunsTo (.whileLoop condition body) s Q := by
  intro bound
  induction bound with
  | zero =>
      intro g s small good
      obtain ⟨next,value,evaluated,exit,continues⟩ := step g s good
      by_cases zero : value = 0
      · exact ⟨1,_,by simp [runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
      · obtain ⟨fuel,inner,run,_,_,g',smaller,_⟩ := continues zero
        omega
  | succ bound ih =>
      intro g s small good
      obtain ⟨next,value,evaluated,exit,continues⟩ := step g s good
      by_cases zero : value = 0
      · exact ⟨1,_,by simp [runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
      · obtain ⟨fuel,inner,run,noReturn,notBreaking,g',smaller,good'⟩ := continues zero
        obtain ⟨tailFuel,final,tailRun,post⟩ := ih g' inner.state (by omega) good'
        refine ⟨fuel+tailFuel+1,final,?_,post⟩
        have first := runFuel_success_mono fuel tailFuel body _ inner run
        have rest := runFuel_success_mono tailFuel fuel (.whileLoop condition body) inner.state final tailRun
        rw [Nat.add_comm tailFuel fuel] at rest
        simp [runFuel,evaluated,zero,first,noReturn,notBreaking,rest,liftChecked,bind,pure,Outcome.bind]

end Proofs.CppNestedHoare
