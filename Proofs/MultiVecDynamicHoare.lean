import Proofs.MultiVecDynamicSteps
import Proofs.DynamicContents
import Proofs.CppNestedHoare

namespace Proofs.MultiVecDynamicHoare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt Proofs.CppNestedHoare
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.CppLoop (Outcome liftChecked)

abbrev Post := Heap → Resources → NStep → Prop

def Runs (params : List Parameter) (command : Command) (s : NState) (Q : Post) : Prop :=
  RunsTo command s fun step => ∃ h m, Family params h step.state.frame m ∧ Q h m step

theorem Runs.mono {params : List Parameter} {command : Command} {s : NState} {P Q : Post}
    (run : Runs params command s P) (weaker : ∀ h m step, P h m step → Q h m step) :
    Runs params command s Q :=
  RunsTo.mono run fun step ⟨h,m,family,post⟩ => ⟨h,m,family,weaker h m step post⟩

theorem Runs.primitive {params : List Parameter} {statement : NStmt} {s : NState} {step : NStep}
    {h : Heap} {m : Resources} {Q : Post} (run : statement.run s = some step)
    (family : Family params h step.state.frame m) (post : Q h m step) :
    Runs params (.primitive statement) s Q :=
  RunsTo.primitive run ⟨h,m,family,post⟩

theorem Runs.sequence {params : List Parameter} {first rest : Command} {s : NState} {Q : Post}
    (run : Runs params first s fun h m middle =>
      ((middle.returned.isSome = true ∨ middle.breaking = true) ∧ Q h m middle) ∨
      (middle.returned = none ∧ middle.breaking = false ∧ Runs params rest middle.state Q)) :
    Runs params (.sequence first rest) s Q := by
  apply RunsTo.sequence
  apply RunsTo.mono run
  intro middle ⟨h,m,family,post⟩
  rcases post with ⟨stop,good⟩ | ⟨ret,br,tail⟩
  · left
    refine ⟨?_,h,m,family,good⟩
    rcases stop with r | b
    · exact Or.inl r
    · exact Or.inr ⟨b,True.intro⟩
  · exact Or.inr ⟨ret,br,tail⟩

theorem Runs.seq {params : List Parameter} {first rest : Command} {s : NState} {Q : Post}
    (run : Runs params first s fun _ _ middle =>
      middle.returned = none ∧ middle.breaking = false ∧ Runs params rest middle.state Q) :
    Runs params (.sequence first rest) s Q :=
  Runs.sequence (run.mono fun _ _ _ post => Or.inr post)

theorem scalar_condition (s : NState) (params : List Parameter) (h : Heap) (m : Resources)
    (family : Family params h s.frame m) (condition : NExpr) (v : Int)
    (scalar : condition.scalarOnly = true) (value : condition.denote (envOf s) = some v) :
    ∃ next, condition.eval s = some (next,v) ∧
      Family params h ((next.release s).charge 1 0).frame m ∧
      ((next.release s).charge 1 0).scalars.memory = s.scalars.memory ∧
      s.scalars.work ≤ ((next.release s).charge 1 0).scalars.work ∧
      ((next.release s).charge 1 0).scalars.work ≤ s.scalars.work+condition.nodes+1 := by
  obtain ⟨next,eval,good⟩ := scalar_eval condition s v scalar value
  have frame : ((next.release s).charge 1 0).frame = s.frame := by
    simp [NState.release,good.1.1]
  refine ⟨next,eval,?_,?_,?_,?_⟩
  · rw [frame]; exact family
  · simpa [NState.release] using good.1.2.2.2.1
  · have lower := good.2.1
    rw [charge_work]
    simpa [NState.release] using Nat.le_trans lower (Nat.le_add_right _ 1)
  · have upper := good.2.2.1
    rw [charge_work]
    simpa [NState.release] using Nat.add_le_add_right upper 1

theorem Runs.branch_scalar {params : List Parameter} {h : Heap} {m : Resources}
    {s : NState} {condition : NExpr} {yes no : Command} {Q : Post}
    (family : Family params h s.frame m) (v : Int)
    (scalar : condition.scalarOnly = true) (value : condition.denote (envOf s) = some v)
    (branches : ∀ next, condition.eval s = some (next,v) →
      Family params h ((next.release s).charge 1 0).frame m →
      Runs params (if v = 0 then no else yes) ((next.release s).charge 1 0) Q) :
    Runs params (.branch condition yes no) s Q := by
  obtain ⟨next,eval,family',_⟩ := scalar_condition s params h m family condition v scalar value
  exact RunsTo.branch eval (branches next eval family')

-- The ghost index can count logical work remaining even when allocations,
-- capacities, row IDs and the number of slots all change during the loop.
theorem Runs.whileGhost {params : List Parameter} {condition : NExpr} {body : Command}
    (I : Nat → Heap → Resources → NState → Prop) (Q : Post)
    (step : ∀ g h m s, Family params h s.frame m → I g h m s →
      ∃ next v, condition.eval s = some (next,v) ∧
        (v = 0 → ∃ h' m', Family params h' ((next.release s).charge 1 0).frame m' ∧
          Q h' m' ⟨(next.release s).charge 1 0,none,false⟩) ∧
        (v ≠ 0 → Runs params body ((next.release s).charge 1 0) fun h' m' inner =>
          inner.returned = none ∧ inner.breaking = false ∧
            ∃ g', g' < g ∧ I g' h' m' inner.state)) :
    ∀ bound g h m s, g ≤ bound → Family params h s.frame m → I g h m s →
      Runs params (.whileLoop condition body) s Q := by
  intro bound g h m s small family initial
  apply RunsTo.whileGhost (fun g s => ∃ h m, Family params h s.frame m ∧ I g h m s)
    (fun inner => ∃ h m, Family params h inner.state.frame m ∧ Q h m inner)
    (step := ?_) bound g s small ⟨h,m,family,initial⟩
  intro g t ⟨h,m,family,inv⟩
  obtain ⟨next,v,eval,exit,bodyRun⟩ := step g h m t family inv
  refine ⟨next,v,eval,exit,?_⟩
  intro nz
  apply RunsTo.mono (bodyRun nz)
  intro inner ⟨h',m',family',ret,br,g',less,inv'⟩
  exact ⟨ret,br,g',less,h',m',family',inv'⟩

-- Early return and break are terminal paths, so only a continuing iteration
-- needs to decrease the ghost counter. A loop consumes its own break flag.
theorem Runs.whileGhostStop {params : List Parameter} {condition : NExpr} {body : Command}
    (I : Nat → Heap → Resources → NState → Prop) (Q : Post)
    (step : ∀ g h m s, Family params h s.frame m → I g h m s →
      ∃ next v, condition.eval s = some (next,v) ∧
        (v = 0 → ∃ h' m', Family params h' ((next.release s).charge 1 0).frame m' ∧
          Q h' m' ⟨(next.release s).charge 1 0,none,false⟩) ∧
        (v ≠ 0 → Runs params body ((next.release s).charge 1 0) fun h' m' inner =>
          (inner.returned.isSome = true ∧ Q h' m' inner) ∨
          (inner.returned = none ∧ ((inner.breaking = true ∧ Q h' m' {inner with breaking := false}) ∨
            (inner.breaking = false ∧ ∃ g', g' < g ∧ I g' h' m' inner.state))))) :
    ∀ g h m s, Family params h s.frame m → I g h m s →
      Runs params (.whileLoop condition body) s Q := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro h m s family inv
    obtain ⟨next,v,eval,exit,continues⟩ := step g h m s family inv
    by_cases zero : v = 0
    · exact ⟨1,⟨(next.release s).charge 1 0,none,false⟩,by simp [runFuel,eval,zero,liftChecked,bind,pure,Outcome.bind],exit zero⟩
    · obtain ⟨fuel,inner,run,h',m',family',post⟩ := continues zero
      rcases post with ⟨ret,good⟩ | ⟨ret,⟨br,good⟩ | ⟨br,g',less,inv'⟩⟩
      · exact ⟨fuel+1,inner,by simp [runFuel,eval,zero,run,ret,liftChecked,bind,pure,Outcome.bind],h',m',family',good⟩
      · exact ⟨fuel+1,{inner with breaking := false},
          by simp [runFuel,eval,zero,run,ret,br,liftChecked,bind,pure,Outcome.bind],h',m',family',good⟩
      · obtain ⟨tailFuel,final,tailRun,post⟩ := ih g' less h' m' inner.state family' inv'
        have first := runFuel_success_mono fuel tailFuel body _ inner run
        have rest := runFuel_success_mono tailFuel fuel (.whileLoop condition body) inner.state final tailRun
        rw [Nat.add_comm tailFuel fuel] at rest
        exact ⟨fuel+tailFuel+1,final,
          by simp [runFuel,eval,zero,first,ret,br,rest,liftChecked,bind,pure,Outcome.bind],post⟩

end Proofs.MultiVecDynamicHoare
