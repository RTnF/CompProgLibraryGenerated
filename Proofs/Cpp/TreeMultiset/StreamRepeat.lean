import Proofs.Math.TreeMultiset.TreapClosedRange
import Proofs.Cpp.Prelude

open Proofs Proofs.Cpp

namespace Proofs.Cpp.TreeMultiset

section Output

variable {K : Type} [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar]

def printLine (stream : Cpp.OStream) (key : K) : Cpp.M Cpp.OStream := do
  let stream ← Cpp.StreamWrite.write stream key
  Cpp.StreamWrite.write stream (⟨10⟩ : Cpp.StreamChar)

def repeatPrint (key : K) : Nat → Cpp.OStream → Cpp.M Cpp.OStream
  | 0, stream => do
    tick
    pure stream
  | count + 1, stream => do
    tick
    let stream ← printLine stream key
    repeatPrint key count stream

def printStep (key : K) (count : UInt64) (_ : Unit) (state : Cpp.OStream × UInt64) :
    Cpp.M (ForInStep (Cpp.OStream × UInt64)) := do
  tick
  if !(decide (state.2 < count)) then return .done state
  let output ← printLine state.1 key
  return .yield (output, state.2 + 1)

theorem print_loop_spec (key : K) (count : UInt64) (remaining fuel : Nat) (i : UInt64)
    (stream : Cpp.OStream) (position : i.toNat + remaining = count.toNat) (enough : remaining < fuel) :
    Cpp.loopFuel fuel (stream, i) (printStep key count) = (do
      let out ← repeatPrint key remaining stream
      pure (out, count)) := by
  induction remaining generalizing fuel i stream with
  | zero =>
    have current : i = count := UInt64.toNat_inj.mp (by simpa using position)
    subst i
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [Cpp.loopFuel, printStep, repeatPrint]
  | succ remaining ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have proceed : i < count := UInt64.lt_iff_toNat_lt.mpr (by omega)
      have capacity : count.toNat < 2 ^ 64 := count.toNat_lt_size
      have next : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]
        change (i.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have moved : (i + 1).toNat + remaining = count.toNat := by rw [next]; omega
      simp [Cpp.loopFuel, printStep, proceed, repeatPrint, bind_assoc, ih fuel (i + 1) _ moved (by omega)]

theorem print_loop_from_zero (key : K) (count : UInt64) (stream : Cpp.OStream) :
    forIn Cpp.forever (stream, 0) (printStep key count) = (do
      let out ← repeatPrint key count.toNat stream
      pure (out, count)) := by
  have capacity : count.toNat < 2 ^ 64 := count.toNat_lt_size
  apply print_loop_spec
  · simp
  · exact capacity

end Output
end Proofs.Cpp.TreeMultiset
