import Proofs.Cpp.Gen.TreeMultiset

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

def prioritySeed : UInt64 := 192865741288175612

def xorshift (state : UInt64) : UInt64 :=
  let x := state ^^^ (state <<< 7)
  x ^^^ (x >>> 9)

def priorityState (globals : cp.GlobalState_ce115a401cd87c22) : UInt64 :=
  globals.multiset_priority_offset ^^^ prioritySeed

theorem generated_priority_init (start : Nat) :
    ∃ globals, cp.initializeGlobals_ce115a401cd87c22.run start = some (globals, start + 1) ∧ priorityState globals = prioritySeed :=
  ⟨⟨0⟩, rfl, by simp [priorityState]⟩

theorem generated_next_priority (globals : cp.GlobalState_ce115a401cd87c22) (start : Nat) :
    ∃ after, (cp.multiset_next_priority globals).run start =
      some ((xorshift (priorityState globals), after), start + 1) ∧
      priorityState after = xorshift (priorityState globals) := by
  let updated := xorshift (priorityState globals)
  refine ⟨⟨updated ^^^ prioritySeed⟩, rfl, ?_⟩
  change updated ^^^ prioritySeed ^^^ prioritySeed = updated
  simp [UInt64.xor_assoc]

end Proofs.Cpp.TreeMultiset
