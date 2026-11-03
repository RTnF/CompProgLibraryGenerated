import Proofs.CppVector

namespace Proofs.CppVectorRange
open Proofs.CppVector

-- A half-open range of live contiguous iterators, including end().
structure IteratorRange where
  owner : Nat
  epoch : Nat
  first : Nat
  last : Nat
deriving DecidableEq, Repr

def rangeBetween (b : Buffer α) (accept : α → Bool) (first last : Int) : Option IteratorRange :=
  if b.Valid accept ∧ 0 ≤ first ∧ first ≤ last ∧ last.toNat ≤ b.items.length then
    some ⟨b.owner,b.epoch,first.toNat,last.toNat⟩
  else none

def slice (items : List α) (first last : Nat) : List α :=
  (items.drop first).take (last-first)

def assignResult (target source : Buffer α) (first last : Nat) : Result α Unit :=
  let count := last-first
  ⟨{target with items := slice source.items first last, capacity := max target.capacity count, epoch := target.epoch+1},(),count+1,
    if target.capacity < count then target.capacity+count+2 else target.capacity+2⟩

-- Only forward/random-access ranges from a distinct vector are supported.
-- The fixed-width copy/assignment/destruction contract assumes allocation
-- succeeds. Every assign invalidates previous destination element refs.
def assignRange (target source : Buffer α) (accept : α → Bool) (writable : Bool)
    (range : IteratorRange) : Option (Result α Unit) :=
  if target.Valid accept ∧ source.Valid accept ∧ writable = true ∧
      target.owner ≠ source.owner ∧ range.owner = source.owner ∧ range.epoch = source.epoch ∧
      range.first ≤ range.last ∧ range.last ≤ source.items.length ∧
      range.last-range.first ≤ target.limit then
    some (assignResult target source range.first range.last)
  else none

def fill (owner limit count : Nat) (value : α) (accept : α → Bool) : Option (Result α Unit) :=
  if count ≤ limit ∧ accept value = true then
    some ⟨⟨owner,List.replicate count value,count,limit,0⟩,(),count+1,count+2⟩
  else none

theorem slice_length (items : List α) (first last : Nat)
    (ordered : first ≤ last) (bounded : last ≤ items.length) :
    (slice items first last).length = last-first := by
  have h : last-first ≤ items.length-first := by omega
  simp [slice,List.length_take,List.length_drop,Nat.min_eq_left h]

theorem slice_accepted (items : List α) (first last : Nat) (accept : α → Bool)
    (accepted : items.all accept = true) : (slice items first last).all accept = true := by
  apply List.all_eq_true.mpr
  intro value member
  have old := List.mem_of_mem_drop (List.mem_of_mem_take member)
  exact List.all_eq_true.mp accepted value old

theorem rangeBetween_runs (b : Buffer α) (accept : α → Bool) (first last : Int)
    (valid : b.Valid accept) (nonnegative : 0 ≤ first) (ordered : first ≤ last)
    (bounded : last.toNat ≤ b.items.length) :
    rangeBetween b accept first last = some ⟨b.owner,b.epoch,first.toNat,last.toNat⟩ := by
  simp [rangeBetween,valid,nonnegative,ordered,bounded]

theorem rangeBetween_negative (b : Buffer α) (accept : α → Bool) (first last : Int)
    (negative : first < 0) : rangeBetween b accept first last = none := by
  have h : ¬ 0 ≤ first := by omega
  simp [rangeBetween,h]

theorem rangeBetween_reversed (b : Buffer α) (accept : α → Bool) (first last : Int)
    (reversed : last < first) : rangeBetween b accept first last = none := by
  have h : ¬ first ≤ last := by omega
  simp [rangeBetween,h]

theorem rangeBetween_past_end (b : Buffer α) (accept : α → Bool) (first last : Int)
    (past : b.items.length < last.toNat) : rangeBetween b accept first last = none := by
  have h : ¬ last.toNat ≤ b.items.length := by omega
  simp [rangeBetween,h]

theorem assignRange_runs (target source : Buffer α) (accept : α → Bool) (first last : Nat)
    (tv : target.Valid accept) (sv : source.Valid accept) (distinct : target.owner ≠ source.owner)
    (ordered : first ≤ last) (bounded : last ≤ source.items.length)
    (limit : last-first ≤ target.limit) :
    assignRange target source accept true ⟨source.owner,source.epoch,first,last⟩ =
      some (assignResult target source first last) := by
  simp [assignRange,tv,sv,distinct,ordered,bounded,limit]

theorem assign_preserves_valid (target source : Buffer α) (accept : α → Bool) (first last : Nat)
    (tv : target.Valid accept) (sv : source.Valid accept) (ordered : first ≤ last)
    (bounded : last ≤ source.items.length) (limit : last-first ≤ target.limit) :
    (assignResult target source first last).buffer.Valid accept := by
  refine ⟨?_,?_,?_⟩
  · simp only [assignResult,slice_length source.items first last ordered bounded]
    exact Nat.le_max_right _ _
  · exact Nat.max_le_of_le_of_le tv.2.1 limit
  · exact slice_accepted source.items first last accept sv.2.2

theorem assign_contents (target source : Buffer α) (first last : Nat) :
    (assignResult target source first last).buffer.items = slice source.items first last := rfl

theorem assign_owner (target source : Buffer α) (first last : Nat) :
    (assignResult target source first last).buffer.owner = target.owner := rfl

theorem assign_invalidates (target source : Buffer α) (accept : α → Bool) (first last index : Nat) :
    readRef (assignResult target source first last).buffer accept
      ⟨target.owner,target.epoch,index⟩ = none := by
  apply readRef_stale
  simp [assignResult]

theorem assign_cost (target source : Buffer α) (first last : Nat) :
    (assignResult target source first last).work = last-first+1 ∧
    (assignResult target source first last).peak ≤ target.capacity+(last-first)+2 := by
  constructor
  · rfl
  · simp only [assignResult]
    split <;> omega

theorem assign_readonly (target source : Buffer α) (accept : α → Bool) (range : IteratorRange) :
    assignRange target source accept false range = none := by simp [assignRange]

theorem assign_alias (target source : Buffer α) (accept : α → Bool) (writable : Bool)
    (range : IteratorRange) (alias : target.owner = source.owner) :
    assignRange target source accept writable range = none := by simp [assignRange,alias]

theorem assign_stale (target source : Buffer α) (accept : α → Bool) (writable : Bool)
    (range : IteratorRange) (stale : range.epoch ≠ source.epoch) :
    assignRange target source accept writable range = none := by simp [assignRange,stale]

theorem reserve_invalidates_range (target source : Buffer α) (accept : α → Bool)
    (writable : Bool) (first last requested : Nat) :
    assignRange target ({source with capacity := requested,epoch := source.epoch+1} : Buffer α)
      accept writable ⟨source.owner,source.epoch,first,last⟩ = none := by
  apply assign_stale
  dsimp
  omega

theorem assign_wrong_owner (target source : Buffer α) (accept : α → Bool) (writable : Bool)
    (range : IteratorRange) (wrong : range.owner ≠ source.owner) :
    assignRange target source accept writable range = none := by simp [assignRange,wrong]

theorem fill_runs (owner limit count : Nat) (value : α) (accept : α → Bool)
    (bounded : count ≤ limit) (accepted : accept value = true) :
    fill owner limit count value accept =
      some ⟨⟨owner,List.replicate count value,count,limit,0⟩,(),count+1,count+2⟩ := by
  simp [fill,bounded,accepted]

theorem fill_valid (owner limit count : Nat) (value : α) (accept : α → Bool)
    (bounded : count ≤ limit) (accepted : accept value = true) :
    (⟨owner,List.replicate count value,count,limit,0⟩ : Buffer α).Valid accept := by
  refine ⟨by simp,bounded,?_⟩
  apply List.all_eq_true.mpr
  intro item member
  have same := List.eq_of_mem_replicate member
  simpa [same] using accepted

theorem fill_over_limit (owner limit count : Nat) (value : α) (accept : α → Bool)
    (over : limit < count) : fill owner limit count value accept = none := by
  have h : ¬ count ≤ limit := by omega
  simp [fill,h]

theorem fill_invalid_value (owner limit count : Nat) (value : α) (accept : α → Bool)
    (rejected : accept value = false) : fill owner limit count value accept = none := by
  simp [fill,rejected]

end Proofs.CppVectorRange
