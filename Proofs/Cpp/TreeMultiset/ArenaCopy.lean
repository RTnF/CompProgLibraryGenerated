import Proofs.Cpp.TreeMultiset.ArenaDump

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

abbrev CopyState (K : Type) := Array (cp.TreeMultiSet_Slot K) × UInt64

def copyStep {K : Type} (source : cp.TreeMultiSet K) (_ : Unit) (state : CopyState K) :
    Cpp.M (ForInStep (CopyState K)) := do
  tick
  let index := state.2
  let position := Cpp.toSigned 64 index.toNat
  if !(decide (index < UInt64.ofInt (Cpp.size source.slots))) then return .done state
  tick
  let raw := Cpp.get source.slots position
  let blank : cp.TreeMultiSet_Slot K := ⟨none, 0, 0, 0, 0, 0⟩
  let mut slots := state.1.push blank
  if raw.key.isSome then
    let key ← Cpp.optionalValue raw.key
    slots := Cpp.set slots position {Cpp.get slots position with key := some key}
  slots := Cpp.set slots position {Cpp.get slots position with priority := raw.priority}
  slots := Cpp.set slots position {Cpp.get slots position with count := raw.count}
  slots := Cpp.set slots position {Cpp.get slots position with total := raw.total}
  slots := Cpp.set slots position {Cpp.get slots position with left := raw.left}
  slots := Cpp.set slots position {Cpp.get slots position with right := raw.right}
  return .yield (slots, index + 1)

theorem generated_copy_program {K : Type} [Inhabited K] (source : cp.TreeMultiSet K) :
    cp.TreeMultiSet.init_copy source = (do
      tick
      let copied ← forIn Cpp.forever ((List.toArray []), 0) (copyStep source)
      pure ⟨copied.1, source.root, source.free_head⟩) := by
  cases source
  unfold cp.TreeMultiSet.init_copy copyStep
  rfl

theorem generated_move_spec {K : Type} (source : cp.TreeMultiSet K) (start : Nat) :
    (cp.TreeMultiSet.init_move source).run start =
      some ((source, ⟨(List.toArray []), endIndex, endIndex⟩), start + 4) := by
  cases source
  rfl

private theorem size_word {A : Type} (cells : Array A) (fits : cells.size ≤ 2 ^ 63) :
    (UInt64.ofInt (Cpp.size cells)).toNat = cells.size := by
  have bounded : (cells.size : Int) < 2 ^ 64 := by omega
  dsimp only [Cpp.size, UInt64.ofInt]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) bounded, Int.toNat_natCast]
  exact UInt64.toNat_ofNat_of_lt' (by change cells.size < 2 ^ 64; omega)

private theorem append_write {A : Type} (cells : Array A) (before after : A) :
    Cpp.set (cells.push before) (cells.size : Int) after = cells.push after := by
  apply Array.ext_getElem?
  intro index
  by_cases same : index = cells.size
  · subst index
    simp [Cpp.set]
  · simp [Cpp.set, same, Ne.symm same, Array.getElem?_push]

private theorem append_read {A : Type} [Inhabited A] (cells : Array A) (row : A) :
    Cpp.get (cells.push row) (cells.size : Int) = row := by
  simp [Cpp.get_eq]

private theorem copy_step_more {K : Type} (source : cp.TreeMultiSet K) (cells : Array (cp.TreeMultiSet_Slot K))
    (index : UInt64) (atEnd : index.toNat = cells.size)
    (fits : source.slots.size ≤ 2 ^ 63) (more : index.toNat < source.slots.size) (start : Nat) :
    (copyStep source () (cells, index)).run start =
      some (.yield (cells.push (Cpp.get source.slots (cells.size : Int)), index + 1), start + 2) := by
  have position : Cpp.toSigned 64 index.toNat = (cells.size : Int) := by
    rw [signed_model_index (by omega), atEnd]
  have keepGoing : index < UInt64.ofInt (Cpp.size source.slots) := by
    rwa [UInt64.lt_iff_toNat_lt, size_word source.slots fits]
  have first : Cpp.tick.run start = some ((), start + 1) := rfl
  have second : Cpp.tick.run (start + 1) = some ((), start + 2) := rfl
  generalize sourceRow : Cpp.get source.slots (cells.size : Int) = row
  cases row with
  | mk key priority count total left right =>
    cases key <;>
      simp [copyStep, StateT.run_bind, keepGoing, first, second, position, sourceRow,
        Cpp.optionalValue, append_write]

private theorem copy_step_done {K : Type} (source : cp.TreeMultiSet K) (cells : Array (cp.TreeMultiSet_Slot K))
    (index : UInt64) (fits : source.slots.size ≤ 2 ^ 63) (stop : source.slots.size ≤ index.toNat) (start : Nat) :
    (copyStep source () (cells, index)).run start = some (.done (cells, index), start + 1) := by
  have finished : ¬ index < UInt64.ofInt (Cpp.size source.slots) := by
    rw [UInt64.lt_iff_toNat_lt, size_word source.slots fits]
    omega
  have first : Cpp.tick.run start = some ((), start + 1) := rfl
  simp [copyStep, first, finished]

private theorem bind_some {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem copy_loop_spec {K : Type} (source : cp.TreeMultiSet K) (cells : Array (cp.TreeMultiSet_Slot K))
    (index : UInt64) (fits : source.slots.size ≤ 2 ^ 63)
    (copied : cells.toList = source.slots.toList.take index.toNat)
    (atEnd : index.toNat = cells.size) (remaining fuel start : Nat)
    (length : index.toNat + remaining = source.slots.size) (enough : remaining < fuel) :
    (Cpp.loopFuel fuel (cells, index) (copyStep source)).run start =
      some ((source.slots, UInt64.ofInt (Cpp.size source.slots)), start + 1 + 2 * remaining) := by
  induction remaining generalizing cells index fuel start with
  | zero =>
    have final : index.toNat = source.slots.size := by omega
    have sameCells : cells = source.slots := by
      apply Array.toList_inj.mp
      rw [copied, final]
      exact List.take_of_length_le (by simp)
    have sameIndex : index = UInt64.ofInt (Cpp.size source.slots) :=
      UInt64.toNat_inj.mp (final.trans (size_word source.slots fits).symm)
    cases fuel with
    | zero => omega
    | succ fuel =>
      have step := copy_step_done source cells index fits final.ge start
      simp only [Cpp.loopFuel, StateT.run_bind, step, bind_some]
      simp [sameCells, sameIndex]
  | succ remaining ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have before : cells.size < source.slots.size := by omega
      let value := Cpp.get source.slots (cells.size : Int)
      let next := cells.push value
      have nextIndex : (index + 1).toNat = index.toNat + 1 := by
        rw [UInt64.toNat_add]
        change (index.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have cell : value = source.slots.toList[cells.size]'(by simpa using before) := by
        simp [value, Cpp.get_eq, getElem!_pos, before]
      have nextCopied : next.toList = source.slots.toList.take (index + 1).toNat := by
        rw [nextIndex, atEnd]
        rw [List.take_succ_eq_append_getElem (by simpa using before)]
        simp only [next, Array.toList_push, copied, atEnd, cell]
      have nextEnd : (index + 1).toNat = next.size := by simp [nextIndex, atEnd, next]
      have nextLength : (index + 1).toNat + remaining = source.slots.size := by omega
      have step : (copyStep source () (cells, index)).run start =
          some (.yield (next, index + 1), start + 2) :=
        copy_step_more source cells index atEnd fits (by omega) start
      have loop := ih next (index + 1) nextCopied nextEnd fuel (start + 2) nextLength (by omega)
      have clock : start + 2 + 1 + 2 * remaining = start + 1 + 2 * (remaining + 1) := by omega
      simp only [Cpp.loopFuel, StateT.run_bind, step, bind_some, loop, clock]

theorem generated_copy_spec {K : Type} [Inhabited K] (source : cp.TreeMultiSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeMultiSet.init_copy source).run start = some (source, start + 2 + 2 * source.slots.size) := by
  have enough : source.slots.size < Cpp.fuel := by unfold Cpp.fuel; omega
  have scan := copy_loop_spec source (List.toArray []) 0 fits (by simp) rfl source.slots.size Cpp.fuel (start + 1)
    (by simp) enough
  have loop : (forIn Cpp.forever ((List.toArray []), (0 : UInt64)) (copyStep source)).run (start + 1) =
    some ((source.slots, UInt64.ofInt (Cpp.size source.slots)), start + 2 + 2 * source.slots.size) := scan
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  rw [generated_copy_program]
  simp [StateT.run_bind, tickRun, loop]

end Proofs.Cpp.TreeMultiset
