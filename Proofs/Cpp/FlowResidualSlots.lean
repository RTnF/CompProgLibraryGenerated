import Proofs.Cpp.FlowEdgeBindings
import Proofs.Math.FlowResidualMath

open Proofs.Cpp Proofs.FlowResidual

namespace Proofs.Cpp.FlowResidualSlots

abbrev Slot := Nat × Nat

def readSlot {E : Type} [Inhabited E] (adj : Array (Array E)) (a : Slot) : E :=
  get (get adj (a.1 : Int)) (a.2 : Int)

def InBounds {E : Type} (adj : Array (Array E)) (a : Slot) : Prop :=
  a.1 < adj.size ∧ a.2 < adj[a.1]!.size

def writeSlot {E : Type} (adj : Array (Array E)) (a : Slot) (e : E) : Array (Array E) :=
  set adj (a.1 : Int) (set (get adj (a.1 : Int)) (a.2 : Int) e)

@[simp] theorem writeSlot_size {E : Type} (adj : Array (Array E)) (a : Slot) (e : E) :
    (writeSlot adj a e).size = adj.size := size_set ..

@[simp] theorem writeSlot_row_size {E : Type} (adj : Array (Array E)) (a : Slot) (e : E) (u : Nat)
    (h : a.1 < adj.size) : (writeSlot adj a e)[u]!.size = adj[u]!.size := by
  have hv : (a.1 : Int).toNat < adj.size := by simpa using h
  unfold writeSlot
  rw [getElemBang_set _ _ _ _ hv]
  by_cases hu : u = a.1
  · simp [hu, get_eq]
  · simp [hu]

theorem read_writeSlot {E : Type} [Inhabited E] (adj : Array (Array E)) (a b : Slot) (e : E)
    (ha : InBounds adj a) : readSlot (writeSlot adj a e) b = if b = a then e else readSlot adj b := by
  have row : (a.1 : Int).toNat < adj.size := by simpa using ha.1
  have col : (a.2 : Int).toNat < (get adj (a.1 : Int)).size := by simpa [get_eq] using ha.2
  unfold readSlot writeSlot
  rw [get_eq _ (b.1 : Int), getElemBang_set _ _ _ _ row]
  simp only [Int.toNat_natCast]
  by_cases hv : b.1 = a.1
  · rw [ite_eq_left hv, get_eq, getElemBang_set _ _ _ _ col]
    simp [hv, Prod.ext_iff, get_eq]
  · rw [ite_eq_right hv, ite_eq_right (fun h => hv (congrArg Prod.fst h))]
    rfl

section Edge

variable {E : Type} [Inhabited E] [Field "cap" E Int] [Field "to" E Int] [Field "rev" E Int]
  [Field "cost" E Int] [WriteField "cap" E Int]

abbrev cap (e : E) := Field.get (member := "cap") (Value := Int) e
abbrev dest (e : E) := Field.get (member := "to") (Value := Int) e
abbrev revIdx (e : E) := Field.get (member := "rev") (Value := Int) e
abbrev price (e : E) := Field.get (member := "cost") (Value := Int) e
abbrev withCap (e : E) (d : Int) := WriteField.set (member := "cap") e d

structure CapLaws : Prop where
  cap_set : ∀ (e : E) d, cap (withCap e d) = d
  to_same : ∀ (e : E) d, dest (withCap e d) = dest e
  rev_same : ∀ (e : E) d, revIdx (withCap e d) = revIdx e
  cost_same : ∀ (e : E) d, price (withCap e d) = price e

theorem flow_edge_cap_laws : CapLaws (E := Gen.cp.FlowEdge Int) := by
  constructor <;> intros <;> rfl

def reverseSlot (adj : Array (Array E)) (a : Slot) : Slot :=
  ((dest (readSlot adj a)).toNat, (revIdx (readSlot adj a)).toNat)

def adjust (adj : Array (Array E)) (a : Slot) (d : Int) : Array (Array E) :=
  let e := readSlot adj a
  let updated := writeSlot adj a (withCap e (cap e - d))
  let b := reverseSlot updated a
  let f := readSlot updated b
  writeSlot updated b (withCap f (cap f + d))

/-- The same two array writes as the generated augmentation, including both slots of a self-loop. -/
theorem adjust_slots (laws : CapLaws (E := E)) (adj : Array (Array E)) (a : Slot) (d : Int)
    (ha : InBounds adj a) (hr : InBounds adj (reverseSlot adj a)) (distinct : reverseSlot adj a ≠ a) :
    let out := adjust adj a d
    ∀ b, readSlot out b =
      if b = a then withCap (readSlot adj b) (cap (readSlot adj b) - d)
      else if b = reverseSlot adj a then withCap (readSlot adj b) (cap (readSlot adj b) + d)
      else readSlot adj b := by
  dsimp only
  let e := readSlot adj a
  let updated := writeSlot adj a (withCap e (cap e - d))
  have hf : readSlot updated a = withCap e (cap e - d) := by simp [updated, read_writeSlot _ _ _ _ ha]
  have reverse_unchanged : reverseSlot updated a = reverseSlot adj a := by
    unfold reverseSlot
    rw [hf, laws.to_same, laws.rev_same]
  let r := reverseSlot adj a
  have rb : InBounds updated r := by
    unfold InBounds at hr ⊢
    simpa [updated, writeSlot_row_size _ _ _ _ ha.1] using hr
  have hb : readSlot updated r = readSlot adj r := by
    rw [show readSlot updated r = if r = a then withCap e (cap e - d) else readSlot adj r from
      read_writeSlot _ _ _ _ ha, ite_eq_right distinct]
  change ∀ b, readSlot (writeSlot updated (reverseSlot updated a)
    (withCap (readSlot updated (reverseSlot updated a)) (cap (readSlot updated (reverseSlot updated a)) + d))) b = _
  rw [reverse_unchanged, hb]
  intro b
  rw [read_writeSlot _ _ _ _ rb]
  by_cases h : b = r
  · subst b
    simp [r, distinct]
  · rw [ite_eq_right h, ite_eq_right h]
    rw [show readSlot updated b = if b = a then withCap e (cap e - d) else readSlot adj b from
      read_writeSlot _ _ _ _ ha]
    by_cases hba : b = a
    · subst b
      simp [e]
    · simp [hba]

theorem adjust_bounds (laws : CapLaws (E := E)) (adj : Array (Array E)) (a : Slot) (d : Int)
    (ha : InBounds adj a) (hr : InBounds adj (reverseSlot adj a)) (b : Slot) :
    InBounds (adjust adj a d) b ↔ InBounds adj b := by
  let e := readSlot adj a
  let updated := writeSlot adj a (withCap e (cap e - d))
  have hf : readSlot updated a = withCap e (cap e - d) := by simp [updated, read_writeSlot _ _ _ _ ha]
  have reverse_unchanged : reverseSlot updated a = reverseSlot adj a := by
    unfold reverseSlot
    rw [hf, laws.to_same, laws.rev_same]
  have rb : (reverseSlot adj a).1 < updated.size := by simpa [updated] using hr.1
  unfold adjust InBounds
  change (b.1 < (writeSlot updated (reverseSlot updated a) _).size ∧
    b.2 < (writeSlot updated (reverseSlot updated a) _)[b.1]!.size) ↔ _
  simp [reverse_unchanged, writeSlot_row_size _ _ _ _ rb, updated, writeSlot_row_size _ _ _ _ ha.1]

theorem adjust_shape (laws : CapLaws (E := E)) (adj : Array (Array E)) (a : Slot) (d : Int)
    (ha : InBounds adj a) (hr : InBounds adj (reverseSlot adj a)) :
    (adjust adj a d).size = adj.size ∧ ∀ v : Nat, (adjust adj a d)[v]!.size = adj[v]!.size := by
  let e := readSlot adj a
  let updated := writeSlot adj a (withCap e (cap e - d))
  have hf : readSlot updated a = withCap e (cap e - d) := by simp [updated, read_writeSlot _ _ _ _ ha]
  have reverse_unchanged : reverseSlot updated a = reverseSlot adj a := by
    unfold reverseSlot
    rw [hf, laws.to_same, laws.rev_same]
  have rb : (reverseSlot adj a).1 < updated.size := by simpa [updated] using hr.1
  refine ⟨by simp only [adjust, writeSlot_size], ?_⟩
  intro v
  change (writeSlot updated (reverseSlot updated a) _)[v]!.size = _
  rw [reverse_unchanged, writeSlot_row_size _ _ _ _ rb, writeSlot_row_size _ _ _ _ ha.1]

theorem adjust_metadata (laws : CapLaws (E := E)) (adj : Array (Array E)) (a : Slot) (d : Int)
    (ha : InBounds adj a) (hr : InBounds adj (reverseSlot adj a)) (distinct : reverseSlot adj a ≠ a)
    (b : Slot) :
    let old := readSlot adj b
    let new := readSlot (adjust adj a d) b
    dest new = dest old ∧ revIdx new = revIdx old ∧ price new = price old := by
  dsimp only
  rw [adjust_slots laws adj a d ha hr distinct b]
  split
  · exact ⟨laws.to_same .., laws.rev_same .., laws.cost_same ..⟩
  split
  · exact ⟨laws.to_same .., laws.rev_same .., laws.cost_same ..⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem adjust_projects {Arc : Type} [DecidableEq Arc] (n : Network Arc Nat) (slot : Arc → Slot)
    (injective : Function.Injective slot) (laws : CapLaws (E := E)) (adj : Array (Array E))
    (valid : ∀ a, InBounds adj (slot a)) (reverse_eq : ∀ a, reverseSlot adj (slot a) = slot (n.reverse a))
    (a : Arc) (d : Int) :
    (fun b => cap (readSlot (adjust adj (slot a) d) (slot b))) =
      update n (fun b => cap (readSlot adj (slot b))) a d := by
  have reverse_valid : InBounds adj (reverseSlot adj (slot a)) := by rw [reverse_eq]; exact valid _
  have reverse_ne : reverseSlot adj (slot a) ≠ slot a := by
    rw [reverse_eq]
    exact fun h => n.reverse_ne a (injective h)
  funext b
  rw [adjust_slots laws _ _ _ (valid a) reverse_valid reverse_ne, reverse_eq]
  unfold update
  by_cases h : b = a
  · simp [h, laws.cap_set]
  by_cases hr : b = n.reverse a
  · subst b
    have hslot : slot (n.reverse a) ≠ slot a := fun h' => n.reverse_ne a (injective h')
    simp [h, hslot, laws.cap_set]
  · have hf : slot b ≠ slot a := fun h' => h (injective h')
    have hb : slot b ≠ slot (n.reverse a) := fun h' => hr (injective h')
    simp [h, hr, hf, hb]

end Edge

end Proofs.Cpp.FlowResidualSlots
