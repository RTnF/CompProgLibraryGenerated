namespace BeatsSlotRunExamples
open Proofs.CppNestedProgram Proofs.CppScalar
open Proofs.CppLoop (Outcome)
open Proofs.BeatsSlotCycle Proofs.CppSlotRename
open BeatsSlotEvalExamples

def lit (v : Int) : NExpr := .literal i32 v
def counter : NExpr := .variable i32 16
def body : Command := .scope
  (.sequence (.primitive (.declare i32 true (.read i32 (.local 0) (.literal u64 0))))
    (.sequence (.primitive (.write (.local 0) i32 (.literal u64 0)
      (.binary i32 .add (.variable i32 17) counter)))
      (.primitive (.assign 16 i32 (.binary i32 .add counter (lit 1))))))
def loop : Command := .whileLoop (.binary i32 .lt counter (lit 3)) body
def actual : Command := command cycle loop
def outcome := runFuel 80 actual flat
def finalState : NState := match outcome with | .finished step => step.state | _ => flat

#guard CoreCommand loop
#guard (match outcome with | .finished _ => true | _ => false)
#guard (finalState.scalarCell 16 i32).map (·.2.value) == some 3
#guard (finalState.frame.state.storage.lookup 1).map (·.items) == some [.integer 4,.integer 101]
#guard (finalState.frame.state.storage.lookup 0).map (·.items) == some [.integer 0,.integer 100]
#guard finalState.slots.length == 17
#guard finalState.scalars.memory.length == 1
#guard outcomeView outcome == runFuel 80 loop (permute flat)
#guard runFuel 0 actual flat == .exhausted
#guard runFuel 1 actual flat == .exhausted
#guard outcomeView (runFuel 1 actual flat) == runFuel 1 loop (permute flat)

def stopping : Command := .whileLoop (lit 1)
  (.scope (.sequence (.primitive (.assign 16 i32 (lit 7)))
    (.sequence .breakLoop (.primitive (.check (lit 0))))))
def stopped := runFuel 30 (command cycle stopping) flat
#guard (match stopped with | .finished step => step.breaking == false && step.returned.isNone | _ => false)
#guard (match stopped with | .finished step => (step.state.scalarCell 16 i32).map (·.2.value) == some 7 | _ => false)
#guard outcomeView stopped == runFuel 30 stopping (permute flat)

def returning : Command := .sequence
  (.whileLoop (lit 1) (.scope (.sequence (.primitive (.ret (lit 42))) (.primitive (.check (lit 0))))))
  (.primitive (.check (lit 0)))
def returned := runFuel 30 (command cycle returning) flat
#guard (match returned with | .finished step => step.returned == some (.scalar 42) | _ => false)
#guard outcomeView returned == runFuel 30 returning (permute flat)

def failing : Command := .branch (lit 1) (.primitive (.check (lit 0))) (.primitive (.check (lit 1)))
#guard runFuel 8 (command cycle failing) flat == .fault
#guard outcomeView (runFuel 8 (command cycle failing) flat) == runFuel 8 failing (permute flat)
def spinning : Command := .whileLoop (lit 1) (.primitive .skip)
#guard runFuel 8 (command cycle spinning) flat == .exhausted
#guard outcomeView (runFuel 8 (command cycle spinning) flat) == runFuel 8 spinning (permute flat)

-- Unsupported operations are rejected by the theorem's coverage predicate.
#guard CoreCommand (.primitive (.fillVector i32 true (lit 1) (lit 0))) == false

example (fuel : Nat) (c : Command) (s : NState) (core : CoreCommand c = true)
    (long : 16 ≤ s.slots.length) :
    outcomeView (runFuel fuel (command cycle c) s) = runFuel fuel c (permute s) :=
  run_permute fuel c s core long

end BeatsSlotRunExamples
