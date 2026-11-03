namespace BeatsBindingRunExamples
open Proofs.CppScalar Proofs.CppNestedProgram
open Proofs.BeatsBindingCycle
open Proofs.BeatsSlotCycle (CoreCommand)
open BeatsSlotEvalExamples
open BeatsSlotRunExamples (loop stopping returning failing spinning)

def commands : List Command := [loop,stopping,returning,failing,spinning,
  .primitive (.retVector 0),.primitive .retUnit,.primitive (.retVector 1000)]
#guard commands.all CoreCommand
#guard (List.range 4).all (fun j => commands.all (fun c =>
  outcomeView (runFuel ([0,1,8,80].getD j 0) c flat) ==
    runFuel ([0,1,8,80].getD j 0) c (view flat)))

def finalState : NState := match runFuel 80 loop flat with | .finished step => step.state | _ => flat
#guard (finalState.scalarCell 16 i32).map (·.2.value) == some 3
#guard (finalState.frame.state.storage.lookup 0).map (·.items) == some [.integer 3,.integer 100]
#guard finalState.frame.bindings.length == 16
#guard finalState.slots.length == 17
#guard (match runFuel 30 stopping (view flat) with
  | .finished step => step.breaking == false && step.returned.isNone
  | _ => false)
#guard (match runFuel 30 returning (view flat) with
  | .finished step => step.returned == some (.scalar 42)
  | _ => false)
#guard runFuel 8 failing (view flat) == .fault
#guard runFuel 8 spinning (view flat) == .exhausted
#guard (match runFuel 2 (.primitive (.retVector 0)) (view flat) with
  | .finished step => step.returned == some (.vector 0 atom)
  | _ => false)
#guard runFuel 2 (.primitive (.retVector 1000)) (view flat) == .fault

-- The coverage boundary is explicit, shared with the existing slot theorem.
#guard CoreCommand (.primitive (.fillVector i32 true (.literal i32 1) (.literal i32 0))) == false

example (fuel : Nat) (c : Command) (s : NState) (core : CoreCommand c = true)
    (long : 16 ≤ s.frame.bindings.length) :
    outcomeView (runFuel fuel c s) = runFuel fuel c (view s) := run_view fuel c s core long

example (fuel : Nat) (c : Command) (s : NState) (r : NStep) (core : CoreCommand c = true)
    (long : 16 ≤ s.frame.bindings.length) (ran : runFuel fuel c s = .finished r) :
    16 ≤ r.state.frame.bindings.length := run_long fuel c s r core long ran

end BeatsBindingRunExamples
