import Proofs.CppCompactScalarPeak

namespace Proofs.CppCompactWork
open Proofs.CppNestedProgram Proofs.CppNestedHoare Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.QuotientFrame Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.CppCompactScalarPeak

def scalarBudget (s : NState) (locals : PS) (res : PRW) : Nat :=
  max s.scalars.peak (max (locals.mem.length+locals.bs.length) res.need)

theorem actual_post (s : NState) (vc : VCtx) (w : Bool)
    (permission : w = true → vc.wV = true ∧ vc.flag = true) (body : Command) (allowed : WrV w body = true)
    (logicalFuel : Nat) (locals : PS) (vec : List Int) (res : PRW)
    (executed : pexecW vc.ty logicalFuel body locals vec = some res) (buffer : Buffer Value)
    (qs : QS s [] s.scalars.baseMemory s.scope locals.mem locals.bs (sl1 locals.bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ locals.mem.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep) (actual : Proofs.CppNestedProgram.runFuel fuel body s = .finished step) :
    QpostW vc res s.scalars.baseMemory s.scope (scalarBudget s locals res) (outerBudget s vc) s.scalars.work 0 step := by
  obtain ⟨chosen,after,ran,post⟩ := body_run s vc w permission body allowed logicalFuel locals vec res executed buffer
    (scalarBudget s locals res) qs frame (Nat.le_max_left _ _) base
    (by unfold scalarBudget; omega) (by unfold scalarBudget; omega) scope
  have same := Proofs.CppNestedHoare.runFuel_success_unique chosen fuel body s after step ran actual
  subst step
  exact post

theorem post_work (s : NState) (vc : VCtx) (locals : PS) (res : PRW) (vec : List Int) (buffer : Buffer Value)
    (frame : FW vc vec buffer 0 s.frame) (step : NStep)
    (post : QpostW vc res s.scalars.baseMemory s.scope (scalarBudget s locals res) (outerBudget s vc) s.scalars.work 0 step) :
    step.state.work ≤ s.work+res.cost+res.wk := by
  have scalar := post.2.2.2.2.work
  obtain ⟨after,frameAfter⟩ := post.2.2.2.1
  have heap := frameAfter.work
  have before := frame.work
  unfold NState.work
  omega

theorem post_fresh (s : NState) (vc : VCtx) (locals : PS) (res : PRW) (step : NStep)
    (scope : vc.sc ≤ s.scope)
    (post : QpostW vc res s.scalars.baseMemory s.scope (scalarBudget s locals res) (outerBudget s vc) s.scalars.work 0 step) :
    ∀ owner, step.state.frame.state.forest.context owner ≠ some step.state.scope := by
  intro owner found
  obtain ⟨buffer,frame⟩ := post.2.2.2.1
  have strict := frame.strict owner step.state.scope found
  have kept := post.2.2.1.scope
  rw [kept] at strict
  omega

end Proofs.CppCompactWork
