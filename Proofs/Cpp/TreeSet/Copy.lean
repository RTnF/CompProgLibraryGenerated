import Proofs.Cpp.TreeSet.Extrema

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

abbrev CopyState (K : Type) := Array (cp.TreeSet_Slot K) × UInt64

def copyStep {K : Type} (source : cp.TreeSet K) (_ : Unit) (state : CopyState K) :
    Cpp.M (ForInStep (CopyState K)) := do
  tick
  let index := state.2
  let position := Cpp.toSigned 64 index.toNat
  if !(decide (index < UInt64.ofInt (Cpp.size source.slots))) then return .done state
  tick
  let raw := Cpp.get source.slots position
  let blank : cp.TreeSet_Slot K := ⟨none, 0, 0, 0, 0, 0, 0⟩
  let mut slots := state.1.push blank
  if raw.key.isSome then
    let key ← Cpp.optionalValue raw.key
    slots := Cpp.set slots position {Cpp.get slots position with key := some key}
  slots := Cpp.set slots position {Cpp.get slots position with left := raw.left}
  slots := Cpp.set slots position {Cpp.get slots position with right := raw.right}
  slots := Cpp.set slots position {Cpp.get slots position with height := raw.height}
  slots := Cpp.set slots position {Cpp.get slots position with size_ := raw.size_}
  slots := Cpp.set slots position {Cpp.get slots position with first := raw.first}
  slots := Cpp.set slots position {Cpp.get slots position with last := raw.last}
  return .yield (slots, index + 1)

theorem generated_copy_program {K : Type} [Inhabited K] (self source : cp.TreeSet K) :
    cp.TreeSet.copy_contents self source = (do
      tick
      let copied ← forIn Cpp.forever (self.slots, 0) (copyStep source)
      pure ⟨copied.1, source.root, source.free_head⟩) := by
  cases self
  cases source
  unfold cp.TreeSet.copy_contents copyStep
  rfl

theorem generated_move_spec {K : Type} (source : cp.TreeSet K) (start : Nat) :
    (cp.TreeSet.init_move source).run start =
      some ((source, ⟨(List.toArray []), endIndex, endIndex⟩), start + 4) := by
  cases source
  rfl

private theorem signed_offset (index : UInt64) (fits : index.toNat < 2 ^ 63) :
    Cpp.toSigned 64 index.toNat = (index.toNat : Int) := by
  unfold Cpp.toSigned
  rw [Nat.mod_eq_of_lt (by omega), ite_eq_left fits]

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

private theorem copy_step_more {K : Type} (source : cp.TreeSet K) (cells : Array (cp.TreeSet_Slot K))
    (index : UInt64) (atEnd : index.toNat = cells.size)
    (fits : source.slots.size ≤ 2 ^ 63) (more : index.toNat < source.slots.size) (start : Nat) :
    (copyStep source () (cells, index)).run start =
      some (.yield (cells.push (Cpp.get source.slots (cells.size : Int)), index + 1), start + 2) := by
  have position : Cpp.toSigned 64 index.toNat = (cells.size : Int) := by
    rw [signed_offset index (by omega), atEnd]
  have keepGoing : index < UInt64.ofInt (Cpp.size source.slots) := by
    rwa [UInt64.lt_iff_toNat_lt, size_word source.slots fits]
  have first : Cpp.tick.run start = some ((), start + 1) := rfl
  have second : Cpp.tick.run (start + 1) = some ((), start + 2) := rfl
  generalize sourceRow : Cpp.get source.slots (cells.size : Int) = row
  cases row with
  | mk key left right height count firstIndex lastIndex =>
    cases key <;>
      simp [copyStep, StateT.run_bind, keepGoing, first, second, position, sourceRow,
        Cpp.optionalValue, append_write]

private theorem copy_step_done {K : Type} (source : cp.TreeSet K) (cells : Array (cp.TreeSet_Slot K))
    (index : UInt64) (fits : source.slots.size ≤ 2 ^ 63) (stop : source.slots.size ≤ index.toNat) (start : Nat) :
    (copyStep source () (cells, index)).run start = some (.done (cells, index), start + 1) := by
  have finished : ¬ index < UInt64.ofInt (Cpp.size source.slots) := by
    rw [UInt64.lt_iff_toNat_lt, size_word source.slots fits]
    omega
  have first : Cpp.tick.run start = some ((), start + 1) := rfl
  simp [copyStep, first, finished]

private theorem bind_some {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem copy_loop_spec {K : Type} (source : cp.TreeSet K) (cells : Array (cp.TreeSet_Slot K))
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

private def emptyArena {K : Type} : cp.TreeSet K := ⟨List.toArray [], endIndex, endIndex⟩

private theorem copy_contents_spec {K : Type} [Inhabited K] (source : cp.TreeSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeSet.copy_contents emptyArena source).run start = some (source, start + 2 + 2 * source.slots.size) := by
  have enough : source.slots.size < Cpp.fuel := by unfold Cpp.fuel; omega
  have scan := copy_loop_spec source (List.toArray []) 0 fits (by simp) rfl source.slots.size Cpp.fuel (start + 1)
    (by simp) enough
  have loop : (forIn Cpp.forever (emptyArena.slots, (0 : UInt64)) (copyStep source)).run (start + 1) =
    some ((source.slots, UInt64.ofInt (Cpp.size source.slots)), start + 2 + 2 * source.slots.size) := scan
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  rw [generated_copy_program]
  simp [StateT.run_bind, tickRun, loop]

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl
private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

theorem generated_copy_spec {K : Type} [Inhabited K] (source : cp.TreeSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeSet.init_copy source).run start = some (source, start + 5 + 2 * source.slots.size) := by
  have copied := copy_contents_spec source fits (start + 3)
  simp only [cp.TreeSet.init_copy, StateT.run_bind, tick_run, sentinel_run, bind_some, pure_run]
  change (do
    let p ← (cp.TreeSet.copy_contents emptyArena source).run (start + 3)
    some (p.1, p.2)) = _
  simp only [copied, bind_some]

private theorem generated_swap_run {K : Type} (a b : cp.TreeSet K) (start : Nat) :
    (cp.TreeSet.swap_contents a b).run start = some ((a, b), start + 2) := by
  cases a
  cases b
  rfl

theorem generated_copy_assignment_spec {K : Type} [Inhabited K] (target source : cp.TreeSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeSet.op_assign_copy target source).run start =
      some ((source, source), start + 8 + 2 * source.slots.size) := by
  have copied := copy_contents_spec source fits (start + 4)
  have init : (cp.TreeSet.init (T := K)).run (start + 1) = some (emptyArena, start + 4) := rfl
  rcases target with ⟨slots, root, free⟩
  simp only [cp.TreeSet.op_assign_copy, StateT.run_bind, tick_run, init, bind_some, pure_run, copied,
    generated_swap_run]
  congr 2
  omega

theorem generated_move_assignment_spec {K : Type} (target source : cp.TreeSet K) (start : Nat) :
    (cp.TreeSet.op_assign_move target source).run start = some ((source, target, source), start + 2) := by
  cases target
  cases source
  rfl

end Proofs.Cpp.TreeSet
