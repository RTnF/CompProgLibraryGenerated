import Proofs.Cpp.Gen.TreeMultiset
import Proofs.Cpp.TreeMultiset.ArenaLayout
import Proofs.Cpp.Lib.Basic

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

def endIndex : UInt64 := ~~~0

def decode (value : UInt64) : Option Nat :=
  if value = endIndex then none else some value.toNat

def slotView (slot : cp.TreeMultiSet_Slot K) : StoredNode K :=
  ⟨slot.key, slot.priority, slot.count.toNat, slot.total.toNat, decode slot.left, decode slot.right⟩

def storageView (arena : cp.TreeMultiSet K) : Array (StoredNode K) := arena.slots.map slotView

theorem decode_none (value : UInt64) : decode value = none ↔ value = endIndex := by
  by_cases h : value = endIndex <;> simp [decode, h]

theorem decode_some (value : UInt64) (index : Nat) (decoded : decode value = some index) :
    value ≠ endIndex ∧ value.toNat = index := by
  by_cases h : value = endIndex
  · simp [decode, h] at decoded
  · exact ⟨h, by simpa [decode, h] using decoded⟩

theorem signed_model_index {value : UInt64} (fits : value.toNat < 2 ^ 63) :
    Cpp.toSigned 64 value.toNat = (value.toNat : Int) := by
  have fit64 : value.toNat < 2 ^ 64 := by omega
  simp [Cpp.toSigned]
  omega

theorem generated_weight_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (index : UInt64)
    (start : Nat) :
    (cp.TreeMultiSet.weight arena index).run start =
      some ((if index = endIndex then 0 else (Cpp.get arena.slots (Cpp.toSigned 64 index.toNat)).total), start + 2) := by
  by_cases matchIndex : index = endIndex <;>
    simp [cp.TreeMultiSet.weight, cp.TreeMultiSet.none, Cpp.tick, StateT.run_bind, endIndex] at matchIndex ⊢

theorem generated_weight_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (tree : Tree K) (slots : List Nat) (layout : Realizes (storageView arena) (decode code) tree slots)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ total, (cp.TreeMultiSet.weight arena code).run start = some (total, start + 2) ∧ total.toNat = tree.weight := by
  generalize eq : decode code = index at layout
  cases layout with
  | empty =>
    have endOfTree := (decode_none code).mp eq
    exact ⟨0, by simp [generated_weight_run, endOfTree], rfl⟩
  | @node index key p count left right l r _ _ reads gl gr hl hr sep =>
    obtain ⟨notEnd, asNat⟩ := decode_some code index eq
    unfold storageView at reads
    rw [Array.getElem?_map] at reads
    cases physical : arena.slots[index]? with
    | none => simp [physical] at reads
    | some slot =>
      simp only [physical, Option.map_some, Option.some.injEq] at reads
      have inBounds : index < arena.slots.size := by
        by_contra missing
        have impossible : arena.slots[index]? = none := Array.getElem?_eq_none (by omega)
        rw [physical] at impossible
        contradiction
      have indexFits : code.toNat < 2 ^ 63 := by omega
      have actual : Cpp.get arena.slots (Cpp.toSigned 64 code.toNat) = slot := by
        rw [signed_model_index indexFits, asNat, Cpp.get_eq]
        have found : arena.slots[index] = slot := by simpa [getElem?_pos, inBounds] using physical
        simpa [getElem!_pos, inBounds] using found
      have total : slot.total.toNat = count + left.weight + right.weight :=
        congrArg StoredNode.total reads
      exact ⟨slot.total, by simp [generated_weight_run, notEnd, actual], total⟩

theorem generated_release_frame {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (fits : code.toNat < 2 ^ 63) (start : Nat) :
    ∃ out, (cp.TreeMultiSet.release arena code).run start = some (out, start + 1) ∧
      out.root = arena.root ∧ out.free_head = code ∧ out.slots.size = arena.slots.size ∧
      ∀ index, index ≠ code.toNat → (storageView out)[index]? = (storageView arena)[index]? := by
  let position := Cpp.toSigned 64 code.toNat
  let old := Cpp.get arena.slots position
  let empty := Cpp.set arena.slots position { old with key := none }
  let linked := Cpp.set empty position { Cpp.get empty position with left := arena.free_head }
  let out : cp.TreeMultiSet K := ⟨linked, arena.root, code⟩
  refine ⟨out, rfl, rfl, rfl, by simp [out, linked, empty, Cpp.set], ?_⟩
  intro index external
  have positionNat : position.toNat = code.toNat := by
    simp [position, signed_model_index fits]
  have different : position.toNat ≠ index := by rwa [positionNat, ne_comm]
  simp [storageView, out, linked, empty, Cpp.set, different]

private theorem local_tick_run (clock : Nat) : tick.run clock = some ((), clock + 1) := rfl
private theorem local_pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : M A).run clock = some (value, clock) := rfl
private theorem local_some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

def modelCell {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) : cp.TreeMultiSet_Slot K :=
  Cpp.get arena.slots (Cpp.toSigned 64 code.toNat)

def modelWeight {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) : UInt64 :=
  if code = endIndex then 0 else (modelCell arena code).total

theorem generated_update_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (start : Nat) :
    let old := modelCell arena code
    let next := { old with total := old.count + modelWeight arena old.left + modelWeight arena old.right }
    (cp.TreeMultiSet.update arena code).run start =
      some ({ arena with slots := Cpp.set arena.slots (Cpp.toSigned 64 code.toNat) next }, start + 5) := by
  cases arena
  simp only [cp.TreeMultiSet.update, modelCell, StateT.run_bind, local_tick_run, local_some_bind,
    generated_weight_run, modelWeight, local_pure_run]
  congr 2

theorem read_at_written {A : Type} [Inhabited A] (slots : Array A) (index : Int) (value : A)
    (inside : index.toNat < slots.size) : Cpp.get (Cpp.set slots index value) index = value := by
  simp [Cpp.get_eq, Cpp.getElemBang_set _ _ _ _ inside]

theorem write_same_cell {A : Type} (slots : Array A) (index : Int) (before after : A) :
    Cpp.set (Cpp.set slots index before) index after = Cpp.set slots index after := by
  unfold Cpp.set
  apply Array.ext_getElem?
  intro reference
  by_cases same : reference = index.toNat
  · subst reference
    simp [Array.getElem?_setIfInBounds_self]
  · simp [Ne.symm same]

private theorem generated_none_run {K : Type} (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

theorem generated_reuse_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (key : K) (count priority : UInt64) (notEnd : arena.free_head ≠ endIndex)
    (inside : (Cpp.toSigned 64 arena.free_head.toNat).toNat < arena.slots.size) (start : Nat) :
    let index := arena.free_head
    let newSlot : cp.TreeMultiSet_Slot K := ⟨some key, priority, count, count, endIndex, endIndex⟩
    (cp.TreeMultiSet.allocate arena key count priority).run start =
      some ((index, ⟨Cpp.set arena.slots (Cpp.toSigned 64 index.toNat) newSlot,
                       arena.root, (modelCell arena index).left⟩), start + 4) := by
  cases arena with
  | mk slots root free =>
    simp only [cp.TreeMultiSet.allocate, StateT.run_bind, local_tick_run, generated_none_run, local_some_bind,
      local_pure_run, modelCell, notEnd, decide_false, Bool.false_eq_true, ite_false]
    simp only [read_at_written _ _ _ inside, write_same_cell]

private theorem write_appended {A : Type} (slots : Array A) (before after : A) :
    Cpp.set (slots.push before) (slots.size : Int) after = slots.push after := by
  apply Array.ext_getElem?
  intro index
  by_cases same : index = slots.size
  · subst index
    simp [Cpp.set]
  · simp [Cpp.set, same, Ne.symm same, Array.getElem?_push]

theorem generated_append_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (key : K) (count priority : UInt64) (noFree : arena.free_head = endIndex)
    (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    let index := UInt64.ofNat arena.slots.size
    let newSlot : cp.TreeMultiSet_Slot K := ⟨some key, priority, count, count, endIndex, endIndex⟩
    (cp.TreeMultiSet.allocate arena key count priority).run start =
      some ((index, ⟨arena.slots.push newSlot, arena.root, endIndex⟩), start + 6) := by
  cases arena with
  | mk slots root free =>
    dsimp at noFree fits ⊢
    have sizeAsInt (row : cp.TreeMultiSet_Slot K) : Cpp.size (slots.push row) - 1 = (slots.size : Int) := by
      simp [Cpp.size]
    have indexCode : UInt64.ofInt (slots.size : Int) = UInt64.ofNat slots.size := by
      unfold UInt64.ofInt
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
    have indexNat : (UInt64.ofNat slots.size).toNat = slots.size :=
      UInt64.toNat_ofNat_of_lt' (by change slots.size < 2 ^ 64; omega)
    have signedIndex : Cpp.toSigned 64 slots.size = (slots.size : Int) := by
      have indexFits : (UInt64.ofNat slots.size).toNat < 2 ^ 63 := by rwa [indexNat]
      simpa only [indexNat] using signed_model_index indexFits
    have readWritten (before after : cp.TreeMultiSet_Slot K) :
        Cpp.get (Cpp.set (slots.push before) (slots.size : Int) after) (slots.size : Int) = after :=
      read_at_written _ _ _ (by simp)
    have lastRead (row : cp.TreeMultiSet_Slot K) : Cpp.get (slots.push row) (slots.size : Int) = row := by
      simp [Cpp.get_eq]
    change (cp.TreeMultiSet.allocate ⟨slots, root, free⟩ key count priority).run start = _
    simp only [cp.TreeMultiSet.allocate, StateT.run_bind, local_tick_run, generated_none_run, local_some_bind,
      local_pure_run, noFree, decide_true, ite_true]
    simp only [sizeAsInt, indexCode, indexNat, signedIndex]
    simp only [write_same_cell, readWritten, lastRead]
    simp only [write_appended]

end Proofs.Cpp.TreeMultiset
