import Proofs.DynamicControl

namespace Proofs.DynamicControlHoare
open Proofs.CppNestedProgram Proofs.DynamicControl Proofs.DynamicExpr Proofs.MultiVecDynamic
open Proofs.CppLoop (Outcome liftChecked)

def Runs (params : List Parameter) (command : Command) (s : DynamicStmt.State) (Q : Step → Prop) : Prop :=
  ∃ fuel step, DynamicControl.runFuel params fuel command s = .finished step ∧ Q step

theorem Runs.mono {params : List Parameter} {command : Command} {s : DynamicStmt.State} {P Q : Step → Prop}
    (run : Runs params command s P) (weaker : ∀ step, P step → Q step) : Runs params command s Q := by
  obtain ⟨fuel,step,ran,post⟩ := run
  exact ⟨fuel,step,ran,weaker step post⟩

theorem Runs.primitive {params : List Parameter} {stmt : NStmt} {s : DynamicStmt.State}
    {step : DynamicStmt.Step} {Q : Step → Prop} (run : DynamicStmt.run params stmt s = some step)
    (post : Q (ofStmt step)) : Runs params (.primitive stmt) s Q :=
  ⟨1,(ofStmt step),by simp [DynamicControl.runFuel,run,liftChecked,bind,pure,Outcome.bind],post⟩

theorem Runs.sequence {params : List Parameter} {first rest : Command} {s : DynamicStmt.State} {Q : Step → Prop}
    (run : Runs params first s fun middle =>
      ((middle.returned.isSome = true ∨ middle.breaking = true) ∧ Q middle) ∨
      (middle.returned = none ∧ middle.breaking = false ∧ Runs params rest middle.state Q)) :
    Runs params (.sequence first rest) s Q := by
  obtain ⟨fuel,middle,ran,post⟩ := run
  rcases post with ⟨stop,good⟩ | ⟨ret,br,tail⟩
  · have stop' : (middle.returned.isSome || middle.breaking) = true := by
      rcases stop with x | x <;> simp [x]
    exact ⟨fuel+1,middle,by simp [DynamicControl.runFuel,ran,stop',bind,pure,Outcome.bind],good⟩
  · obtain ⟨tailFuel,final,tailRun,good⟩ := tail
    have first' := success_mono params fuel tailFuel first s middle ran
    have rest' := success_mono params tailFuel fuel rest middle.state final tailRun
    rw [Nat.add_comm tailFuel fuel] at rest'
    exact ⟨fuel+tailFuel+1,final,by simp [DynamicControl.runFuel,first',rest',ret,br,bind,Outcome.bind],good⟩

theorem Runs.seq {params : List Parameter} {first rest : Command} {s : DynamicStmt.State} {Q : Step → Prop}
    (run : Runs params first s fun middle => middle.returned = none ∧ middle.breaking = false ∧
      Runs params rest middle.state Q) : Runs params (.sequence first rest) s Q :=
  Runs.sequence (run.mono fun _ post => Or.inr post)

theorem Runs.branch {params : List Parameter} {condition : NExpr} {yes no : Command}
    {s : DynamicStmt.State} {v : Int} {Q : Step → Prop}
    (value : denote params s.locals s.contents condition = some v)
    (run : Runs params (if v = 0 then no else yes) s Q) : Runs params (.branch condition yes no) s Q := by
  obtain ⟨fuel,step,ran,post⟩ := run
  refine ⟨fuel+1,step,?_,post⟩
  by_cases zero : v = 0
  · simp only [zero,ite_true] at ran
    simp [DynamicControl.runFuel,value,zero,ran,liftChecked,bind,Outcome.bind]
  · simp only [zero,ite_false] at ran
    simp [DynamicControl.runFuel,value,zero,ran,liftChecked,bind,Outcome.bind]

theorem Runs.scope {params : List Parameter} {body : Command} {s : DynamicStmt.State} {Q : Step → Prop}
    (run : Runs params body s fun inner => ∃ restored, leave s inner.state = some restored ∧
      Q {inner with state := restored}) : Runs params (.scope body) s Q := by
  obtain ⟨fuel,inner,ran,restored,left,post⟩ := run
  refine ⟨fuel+1,{inner with state := restored},?_,post⟩
  simp [DynamicControl.runFuel,ran,left,liftChecked,bind,Outcome.bind]
  rfl

-- A strictly decreasing ghost counter is needed only for iterations that
-- continue. An immediate return or break may occur even when it is zero.
theorem Runs.whileGhostStop {params : List Parameter} {condition : NExpr} {body : Command}
    (I : Nat → DynamicStmt.State → Prop) (Q : Step → Prop)
    (step : ∀ g s, I g s → ∃ v, denote params s.locals s.contents condition = some v ∧
      (v = 0 → Q ⟨s,none,false⟩) ∧
      (v ≠ 0 → Runs params body s fun inner =>
        (inner.returned.isSome = true ∧ Q inner) ∨
        (inner.returned = none ∧ ((inner.breaking = true ∧ Q {inner with breaking := false}) ∨
          (inner.breaking = false ∧ ∃ g', g' < g ∧ I g' inner.state))))) :
    ∀ g s, I g s → Runs params (.whileLoop condition body) s Q := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro s initial
    obtain ⟨v,value,exit,bodyRun⟩ := step g s initial
    by_cases zero : v = 0
    · exact ⟨1,⟨s,none,false⟩,by simp [DynamicControl.runFuel,value,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
    · obtain ⟨fuel,inner,ran,post⟩ := bodyRun zero
      rcases post with ⟨ret,good⟩ | ⟨ret,⟨br,good⟩ | ⟨br,g',less,inv⟩⟩
      · exact ⟨fuel+1,inner,by simp [DynamicControl.runFuel,value,zero,ran,ret,liftChecked,bind,pure,Outcome.bind],good⟩
      · exact ⟨fuel+1,{inner with breaking := false},by simp [DynamicControl.runFuel,value,zero,ran,ret,br,liftChecked,bind,pure,Outcome.bind],good⟩
      · obtain ⟨tailFuel,final,tailRun,post⟩ := ih g' less inner.state inv
        have first := success_mono params fuel tailFuel body s inner ran
        have rest := success_mono params tailFuel fuel (.whileLoop condition body) inner.state final tailRun
        rw [Nat.add_comm tailFuel fuel] at rest
        exact ⟨fuel+tailFuel+1,final,by simp [DynamicControl.runFuel,value,zero,first,ret,br,rest,liftChecked,bind,pure,Outcome.bind],post⟩

end Proofs.DynamicControlHoare
