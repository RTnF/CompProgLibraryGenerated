import Proofs.Cpp.Prelude

namespace Proofs.Cpp

/-- The FIFO elements in order from front to back. The clock counts standard deque operations. -/
abbrev Queue (α : Type) := List α

def queuePush {α : Type} (queue : Queue α) (x : α) : M (Queue α) := do
  tick
  return queue ++ [x]

def queueFront {α : Type} (queue : Queue α) : M α := do
  tick
  match queue with
  | [] => failure
  | x :: _ => return x

def queuePop {α : Type} (queue : Queue α) : M (Queue α) := do
  tick
  match queue with
  | [] => failure
  | _ :: tail => return tail

end Proofs.Cpp
