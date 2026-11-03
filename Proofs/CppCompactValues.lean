import Proofs.CppCompactScalarPeak
import Proofs.CppFixedCall

namespace Proofs.CppCompactValues
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveCallBindings
open Proofs.CppCompactScalarPeak Proofs.CppMoveFrame Proofs.CppScalar

theorem call_other (program : NProgram) (fuel : Nat) (s out prepared : Context) (initial : NState)
    (ty retType : Ty) (arguments : List NArgument) (result : Ret) (root : Nat)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (prep : prepareArguments s ty program.parameters arguments = some prepared)
    (compacted : compact (project prepared ty) = some initial)
    (target : Proofs.CppFixedWrite.Target initial root)
    (contexts : ∀ owner scope, (project s ty).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (actual : callFuel program fuel s ty arguments = .finished (out,result)) :
    ∀ owner, owner ≠ root → (project out ty).frame.state.storage.lookup owner = (project s ty).frame.state.storage.lookup owner := by
  obtain ⟨preparedActual,initialActual,step,after,prepActual,compactActual,body,breaking,finished,restored⟩ :=
    call_parts program fuel s out ty arguments result actual
  have samePrepared := Option.some.inj (prepActual.symm.trans prep)
  subst preparedActual
  have sameInitial := Option.some.inj (compactActual.symm.trans compacted)
  subst initialActual
  have preparedEffects := Proofs.CppMovePreparedCall.prepareArguments_effects s prepared ty _ _ prep
  have metadata := compact_metadata (project prepared ty) initial compacted
  have projected : (project prepared ty).frame.state = (project s ty).frame.state := by
    simp only [project,materialize,preparedEffects.1]
  have initialFrame := metadata.1.trans projected
  have initialScope : initial.scope = s.scope+1 := metadata.2.2.2.1.trans preparedEffects.2
  have initialContexts : ∀ owner scope, initial.frame.state.forest.context owner = some scope → scope ≤ initial.scope := by
    intro owner scope found
    rw [initialFrame] at found
    have bound := contexts owner scope found
    rw [initialScope]
    omega
  have effects := Proofs.CppFixedRun.run_values fuel program.body initial step root allowed target initialContexts body
  have headers : Proofs.CppBufferHeaders.SameHeaders (project s ty).frame.state step.state.frame.state := by
    rw [← initialFrame]
    exact effects.base.headers
  rw [scalar] at finished
  have finalLookups := Proofs.CppFixedCall.finish_values (project s ty) step.state after retType step.returned result
    headers (effects.base.scopedState.trans initialScope) contexts finished
  have projectedOut := Proofs.CppMoveRestore.restoreContext_project s out ty after restored covered
  intro owner different
  rw [projectedOut,finalLookups owner,effects.other owner different,initialFrame]

end Proofs.CppCompactValues
