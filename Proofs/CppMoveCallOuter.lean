import Proofs.CppMoveArgumentOuter
import Proofs.CppCompactScalarPeak
import Proofs.CppPeakRun

namespace Proofs.CppMoveCallOuter
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppScalar
open Proofs.CppCompactScalarPeak Proofs.CppMoveArgumentWork Proofs.CppMoveArgumentOuter

theorem call_outer (program : NProgram) (fuel : Nat) (s out : Context) (ty retType : Ty)
    (arguments : List NArgument) (result : Ret)
    (pure : ∀ argument ∈ arguments, argumentPure argument)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true) (scalar : program.result = .scalar retType)
    (contexts : ∀ owner scope, (project s ty).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (actual : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) :
    out.peak ≤ max s.peak (out.scalars.peak+out.objects.heap.peak) := by
  obtain ⟨prepared,initial,step,after,prep,compacted,body,breaking,finished,restored⟩ :=
    call_parts program fuel s out ty arguments result actual
  have prepEffects := prepare_effects s prepared ty program.parameters arguments pure prep
  have prepScope := (Proofs.CppMovePreparedCall.prepareArguments_effects s prepared ty _ _ prep).2
  have metadata := Proofs.CppMoveCallBindings.compact_metadata (project prepared ty) initial compacted
  have projected : (project prepared ty).frame.state = (project s ty).frame.state := by
    simp only [project,Proofs.CppMoveFrame.materialize,prepEffects.heap]
  have frame := metadata.1.trans projected
  have initialScope : initial.scope = s.scope+1 := metadata.2.2.2.1.trans prepScope
  have readyContexts : ∀ owner scope, initial.frame.state.forest.context owner = some scope → scope ≤ initial.scope := by
    intro owner scope found
    rw [frame] at found
    have smaller := contexts owner scope found
    rw [initialScope]
    omega
  have grows := (Proofs.CppPeakRun.run_grows fuel program.body initial step allowed readyContexts body).growth
  rw [scalar] at finished
  have counters := Proofs.CppMovePreparedCall.restored_finish_counters s out ty retType step.state after step.returned result
    finished restored covered
  have scalarGrow := grows.scalar
  have heapGrow := grows.storage
  have outer := grows.outer
  have prepOuter := prepEffects.outer
  rw [metadata.2.2.1] at scalarGrow
  change prepared.scalars.peak ≤ step.state.scalars.peak at scalarGrow
  rw [frame] at heapGrow
  change s.objects.heap.peak ≤ step.state.frame.state.storage.peak at heapGrow
  rw [metadata.2.2.2.2.1] at outer
  change step.state.peak ≤ max prepared.peak (step.state.scalars.peak+step.state.frame.state.storage.peak) at outer
  rw [counters.2.2]
  have scalarCounter := counters.1
  have heapCounter := counters.2.1
  clear * - scalarGrow heapGrow outer prepOuter scalarCounter heapCounter
  omega

end Proofs.CppMoveCallOuter
