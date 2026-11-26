import Proofs.Cpp.Prelude

namespace Proofs.Cpp

abbrev OrderedSet (α : Type) := List α

def insertOrdered {α : Type} (less : α → α → Bool) (key : α) : OrderedSet α → OrderedSet α
  | [] => [key]
  | head :: tail =>
    if less key head then key :: head :: tail
    else if less head key then head :: insertOrdered less key tail
    else head :: tail

def equivalentKey {α : Type} (less : α → α → Bool) (a b : α) : Bool :=
  !(less a b || less b a)

def eraseOrdered {α : Type} (less : α → α → Bool) (key : α) (s : OrderedSet α) : OrderedSet α :=
  s.filter fun v => !(equivalentKey less key v)

def orderedSetLookupCost (n : Nat) : Nat := 1 + Nat.log2 (n + 1)

def orderedSetInsert {α : Type} (less : α → α → Bool) (s : OrderedSet α) (key : α) : M (OrderedSet α) := do
  tickN (orderedSetLookupCost s.length)
  return insertOrdered less key s

def orderedSetErase {α : Type} (less : α → α → Bool) (s : OrderedSet α) (key : α) : M (OrderedSet α) := do
  tickN (orderedSetLookupCost s.length + 1)
  return eraseOrdered less key s

def orderedSetCount {α : Type} (less : α → α → Bool) (s : OrderedSet α) (key : α) : M UInt64 := do
  tickN (orderedSetLookupCost s.length + 1)
  return if s.any (equivalentKey less key) then 1 else 0

def orderedSetFirst {α : Type} (s : OrderedSet α) : M α := do
  tick
  match s.head? with
  | some key => return key
  | none => fun _ => none

def orderedSetLast {α : Type} (s : OrderedSet α) : M α := do
  tick
  match s.getLast? with
  | some key => return key
  | none => fun _ => none

end Proofs.Cpp
