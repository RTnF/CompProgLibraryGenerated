import Proofs.VecWrite
import Proofs.CppMoveCallLayout

namespace Proofs.CppCompactScalarPeak
open Proofs.CppNestedProgram Proofs.CppNestedHoare Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.QuotientFrame Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppMoveCallLayout Proofs.CppLoop

-- A loose auxiliary total bound keeps the scalar bound independent of outer peak.
def outerBudget (s : NState) (vc : VCtx) : Nat :=
  max s.peak (max s.frame.state.storage.peak (vc.L0+1))

theorem body_run (s : NState) (vc : VCtx) (w : Bool)
    (permission : w = true → vc.wV = true ∧ vc.flag = true) (body : Command)
    (allowed : WrV w body = true) (fuel : Nat) (locals : PS) (vec : List Int) (res : PRW)
    (executed : pexecW vc.ty fuel body locals vec = some res) (buffer : Buffer Value) (bound : Nat)
    (qs : QS s [] s.scalars.baseMemory s.scope locals.mem locals.bs (sl1 locals.bs.length))
    (frame : FW vc vec buffer 0 s.frame) (initial : s.scalars.peak ≤ bound)
    (base : s.scalars.baseMemory ≤ locals.mem.length)
    (resident : locals.mem.length+locals.bs.length ≤ bound+s.scalars.baseMemory)
    (need : res.need ≤ bound+s.scalars.baseMemory) (scope : vc.sc ≤ s.scope) :
    ∃ chosen step, Proofs.CppNestedProgram.runFuel chosen body s = .finished step ∧
      QpostW vc res s.scalars.baseMemory s.scope bound (outerBudget s vc) s.scalars.work 0 step := by
  have cq : Cq bound (outerBudget s vc) s.scalars.work s := by
    refine ⟨Nat.le_refl _,initial,?_,?_⟩
    · change s.frame.state.storage.peak ≤ outerBudget s vc
      unfold outerBudget
      omega
    · change s.peak ≤ bound+outerBudget s vc
      unfold outerBudget
      omega
  exact soundW vc w permission body allowed fuel locals vec res executed s qs frame cq base resident need scope
    (by unfold outerBudget; omega)

theorem actual_body_peak (s : NState) (vc : VCtx) (w : Bool)
    (permission : w = true → vc.wV = true ∧ vc.flag = true) (body : Command)
    (allowed : WrV w body = true) (logicalFuel : Nat) (locals : PS) (vec : List Int) (res : PRW)
    (executed : pexecW vc.ty logicalFuel body locals vec = some res) (buffer : Buffer Value) (bound : Nat)
    (qs : QS s [] s.scalars.baseMemory s.scope locals.mem locals.bs (sl1 locals.bs.length))
    (frame : FW vc vec buffer 0 s.frame) (initial : s.scalars.peak ≤ bound)
    (base : s.scalars.baseMemory ≤ locals.mem.length)
    (resident : locals.mem.length+locals.bs.length ≤ bound+s.scalars.baseMemory)
    (need : res.need ≤ bound+s.scalars.baseMemory) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep) (actual : Proofs.CppNestedProgram.runFuel fuel body s = .finished step) :
    step.state.scalars.peak ≤ bound := by
  obtain ⟨chosen,after,ran,post⟩ := body_run s vc w permission body allowed logicalFuel locals vec res executed
    buffer bound qs frame initial base resident need scope
  have same := Proofs.CppNestedHoare.runFuel_success_unique chosen fuel body s after step ran actual
  subst step
  exact post.2.2.2.2.scalarPeak

theorem call_parts (program : NProgram) (fuel : Nat) (s out : Context) (ty : Proofs.CppScalar.Ty)
    (arguments : List NArgument) (result : Ret)
    (actual : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) :
    ∃ (prepared : Context) (initial : NState) (step : NStep) (after : NState),
      prepareArguments s ty program.parameters arguments = some prepared ∧
      Proofs.CppMoveCallBindings.compact (project prepared ty) = some initial ∧
      Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished step ∧ step.breaking = false ∧
      Proofs.CppNestedCall.finish (project s ty) step.state program.result step.returned = some (after,result) ∧
      Proofs.CppMoveRestore.restoreContext s ty after = some out := by
  unfold Proofs.CppMoveCallBindings.callFuel at actual
  split at actual
  next =>
    obtain ⟨prepared,prep,rest⟩ := checked_bind_finished _ _ _ actual
    obtain ⟨initial,compacted,rest⟩ := checked_bind_finished _ _ _ rest
    obtain ⟨step,ran,rest⟩ := outcome_bind_finished _ _ _ rest
    split at rest
    next => simp at rest
    next normal =>
      obtain ⟨pair,finished,rest⟩ := checked_bind_finished _ _ _ rest
      rcases pair with ⟨after,value⟩
      obtain ⟨last,restored,done⟩ := checked_bind_finished _ _ _ rest
      have same := Prod.mk.inj (Outcome.finished.inj done)
      rw [same.2] at finished
      rw [same.1] at restored
      exact ⟨prepared,initial,step,after,prep,compacted,ran,by simpa using normal,finished,restored⟩
  next => simp at actual

end Proofs.CppCompactScalarPeak
