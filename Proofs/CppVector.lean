import Proofs.CppScalar

namespace Proofs.CppVector

-- Ownership identities are fresh for each object lifetime. A store adapter
-- must enforce that condition; an identity must never be recycled.
structure Buffer (α : Type) where
  owner : Nat
  items : List α
  capacity : Nat
  limit : Nat
  epoch : Nat := 0
deriving DecidableEq, Repr

structure ElementRef where
  owner : Nat
  epoch : Nat
  index : Nat
deriving DecidableEq, Repr

structure Result (α β : Type) where
  buffer : Buffer α
  value : β
  work : Nat
  peak : Nat
deriving DecidableEq, Repr

def Buffer.Valid (b : Buffer α) (accept : α → Bool) : Prop :=
  b.items.length ≤ b.capacity ∧ b.capacity ≤ b.limit ∧ b.items.all accept = true

instance (b : Buffer α) (accept : α → Bool) : Decidable (b.Valid accept) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- Costs count logical element moves and control work. Peak includes the
-- buffer object, simultaneously live old/new storage, and one temporary.
-- These operations assume allocation succeeds; allocator internals are not
-- a Lean implementation of libstdc++. Growing push_back is not supported.
def reserve (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (requested : Nat) : Option (Result α Unit) :=
  if b.Valid accept ∧ writable = true ∧ requested ≤ b.limit then
    if b.capacity < requested then
      some ⟨{b with capacity := requested, epoch := b.epoch+1}, (),
            b.items.length+1, b.capacity+requested+2⟩
    else some ⟨b, (), 1, b.capacity+1⟩
  else none

def appendReserved (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (value : α) : Option (Result α Unit) :=
  if b.Valid accept ∧ writable = true ∧ accept value = true ∧
      b.items.length < b.capacity then
    some ⟨{b with items := b.items ++ [value]}, (), 2, b.capacity+2⟩
  else none

def elementRef (b : Buffer α) (accept : α → Bool) (index : Int) : Option ElementRef :=
  if b.Valid accept ∧ 0 ≤ index ∧ index.toNat < b.items.length then
    some ⟨b.owner,b.epoch,index.toNat⟩
  else none

def readRef (b : Buffer α) (accept : α → Bool) (reference : ElementRef) : Option (Result α α) := do
  if b.Valid accept ∧ reference.owner = b.owner ∧ reference.epoch = b.epoch then
    let value ← b.items[reference.index]?
    some ⟨b,value,1,b.capacity+2⟩
  else none

def read (b : Buffer α) (accept : α → Bool) (index : Int) : Option (Result α α) := do
  let reference ← elementRef b accept index
  readRef b accept reference

def writeRef (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (reference : ElementRef) (value : α) : Option (Result α Unit) :=
  if b.Valid accept ∧ writable = true ∧ reference.owner = b.owner ∧
      reference.epoch = b.epoch ∧ reference.index < b.items.length ∧ accept value = true then
    some ⟨{b with items := b.items.set reference.index value},(),1,b.capacity+2⟩
  else none

theorem reserve_grow (b : Buffer α) (accept : α → Bool) (requested : Nat)
    (valid : b.Valid accept) (bounded : requested ≤ b.limit) (grow : b.capacity < requested) :
    reserve b accept true requested = some ⟨{b with capacity := requested,epoch := b.epoch+1},
      (),b.items.length+1,b.capacity+requested+2⟩ := by
  simp [reserve,valid,bounded,grow]

theorem reserve_keep (b : Buffer α) (accept : α → Bool) (requested : Nat)
    (valid : b.Valid accept) (bounded : requested ≤ b.capacity) :
    reserve b accept true requested = some ⟨b,(),1,b.capacity+1⟩ := by
  have limit := Nat.le_trans bounded valid.2.1
  have noGrow : ¬ b.capacity < requested := by omega
  simp [reserve,valid,limit,noGrow]

theorem reserve_preserves_valid (b : Buffer α) (accept : α → Bool) (requested : Nat)
    (valid : b.Valid accept) (bounded : requested ≤ b.limit) (grow : b.capacity < requested) :
    ({b with capacity := requested,epoch := b.epoch+1} : Buffer α).Valid accept := by
  exact ⟨by have h := valid.1; dsimp; omega,bounded,valid.2.2⟩

theorem reserve_readonly (b : Buffer α) (accept : α → Bool) (requested : Nat) :
    reserve b accept false requested = none := by simp [reserve]

theorem reserve_over_limit (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (requested : Nat) (over : b.limit < requested) :
    reserve b accept writable requested = none := by
  have h : ¬ requested ≤ b.limit := by omega
  simp [reserve,h]

theorem append_runs (b : Buffer α) (accept : α → Bool) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true) (space : b.items.length < b.capacity) :
    appendReserved b accept true value =
      some ⟨{b with items := b.items ++ [value]},(),2,b.capacity+2⟩ := by
  simp [appendReserved,valid,accepted,space]

theorem append_preserves_valid (b : Buffer α) (accept : α → Bool) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true) (space : b.items.length < b.capacity) :
    ({b with items := b.items ++ [value]} : Buffer α).Valid accept := by
  refine ⟨?_,valid.2.1,?_⟩
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · simp [valid.2.2,accepted]

theorem append_readonly (b : Buffer α) (accept : α → Bool) (value : α) :
    appendReserved b accept false value = none := by simp [appendReserved]

theorem append_full (b : Buffer α) (accept : α → Bool) (writable : Bool) (value : α)
    (full : b.capacity ≤ b.items.length) : appendReserved b accept writable value = none := by
  have noSpace : ¬ b.items.length < b.capacity := by omega
  simp [appendReserved,noSpace]

theorem append_invalid_value (b : Buffer α) (accept : α → Bool) (writable : Bool) (value : α)
    (rejected : accept value = false) : appendReserved b accept writable value = none := by
  simp [appendReserved,rejected]

theorem elementRef_runs (b : Buffer α) (accept : α → Bool) (index : Int)
    (valid : b.Valid accept) (nonnegative : 0 ≤ index) (bounded : index.toNat < b.items.length) :
    elementRef b accept index = some ⟨b.owner,b.epoch,index.toNat⟩ := by
  simp [elementRef,valid,nonnegative,bounded]

theorem elementRef_negative (b : Buffer α) (accept : α → Bool) (index : Int)
    (negative : index < 0) : elementRef b accept index = none := by
  have h : ¬ 0 ≤ index := by omega
  simp [elementRef,h]

theorem elementRef_over_end (b : Buffer α) (accept : α → Bool) (index : Int)
    (over : b.items.length ≤ index.toNat) : elementRef b accept index = none := by
  have h : ¬ index.toNat < b.items.length := by omega
  simp [elementRef,h]

theorem readRef_runs (b : Buffer α) (accept : α → Bool) (index : Nat) (value : α)
    (valid : b.Valid accept) (lookup : b.items[index]? = some value) :
    readRef b accept ⟨b.owner,b.epoch,index⟩ = some ⟨b,value,1,b.capacity+2⟩ := by
  simp [readRef,valid,lookup]

theorem readRef_wrong_owner (b : Buffer α) (accept : α → Bool) (reference : ElementRef)
    (wrong : reference.owner ≠ b.owner) : readRef b accept reference = none := by
  simp [readRef,wrong]

theorem readRef_stale (b : Buffer α) (accept : α → Bool) (reference : ElementRef)
    (stale : reference.epoch ≠ b.epoch) : readRef b accept reference = none := by
  simp [readRef,stale]

theorem reserve_invalidates (b : Buffer α) (accept : α → Bool) (index requested : Nat) :
    readRef ({b with capacity := requested,epoch := b.epoch+1} : Buffer α) accept
      ⟨b.owner,b.epoch,index⟩ = none := by
  apply readRef_stale
  dsimp
  omega

theorem append_preserves_reference (b : Buffer α) (accept : α → Bool) (index : Nat)
    (value newValue : α) (valid : b.Valid accept) (lookup : b.items[index]? = some value)
    (accepted : accept newValue = true) (space : b.items.length < b.capacity) :
    readRef ({b with items := b.items ++ [newValue]} : Buffer α) accept
      ⟨b.owner,b.epoch,index⟩ = some ⟨{b with items := b.items ++ [newValue]},value,1,b.capacity+2⟩ := by
  have bound : index < b.items.length := by
    have h := List.getElem?_eq_some_iff.mp lookup
    exact h.1
  have updated : (b.items ++ [newValue])[index]? = some value := by
    simpa [List.getElem?_append,bound] using lookup
  exact readRef_runs _ _ _ _ (append_preserves_valid b accept newValue valid accepted space) updated

theorem read_runs (b : Buffer α) (accept : α → Bool) (index : Int) (value : α)
    (valid : b.Valid accept) (nonnegative : 0 ≤ index)
    (lookup : b.items[index.toNat]? = some value) :
    read b accept index = some ⟨b,value,1,b.capacity+2⟩ := by
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [read,elementRef_runs b accept index valid nonnegative bound]
  simpa using readRef_runs b accept index.toNat value valid lookup

theorem writeRef_runs (b : Buffer α) (accept : α → Bool) (index : Nat) (value : α)
    (valid : b.Valid accept) (bounded : index < b.items.length) (accepted : accept value = true) :
    writeRef b accept true ⟨b.owner,b.epoch,index⟩ value =
      some ⟨{b with items := b.items.set index value},(),1,b.capacity+2⟩ := by
  simp [writeRef,valid,bounded,accepted]

theorem writeRef_preserves_valid (b : Buffer α) (accept : α → Bool) (index : Nat) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true) :
    ({b with items := b.items.set index value} : Buffer α).Valid accept := by
  refine ⟨?_,valid.2.1,?_⟩
  · simpa using valid.1
  · apply List.all_eq_true.mpr
    intro item member
    rcases List.mem_or_eq_of_mem_set member with old | changed
    · exact List.all_eq_true.mp valid.2.2 item old
    · simpa [changed] using accepted

theorem writeRef_readonly (b : Buffer α) (accept : α → Bool) (reference : ElementRef) (value : α) :
    writeRef b accept false reference value = none := by simp [writeRef]

theorem writeRef_wrong_owner (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (reference : ElementRef) (value : α) (wrong : reference.owner ≠ b.owner) :
    writeRef b accept writable reference value = none := by simp [writeRef,wrong]

theorem writeRef_stale (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (reference : ElementRef) (value : α) (stale : reference.epoch ≠ b.epoch) :
    writeRef b accept writable reference value = none := by simp [writeRef,stale]

theorem writeRef_read_same (b : Buffer α) (accept : α → Bool) (index : Nat) (value : α)
    (valid : b.Valid accept) (bounded : index < b.items.length) (accepted : accept value = true) :
    readRef ({b with items := b.items.set index value} : Buffer α) accept
      ⟨b.owner,b.epoch,index⟩ =
      some ⟨{b with items := b.items.set index value},value,1,b.capacity+2⟩ := by
  apply readRef_runs _ _ _ _ (writeRef_preserves_valid b accept index value valid accepted)
  exact List.getElem?_set_self bounded

theorem writeRef_preserves_other (b : Buffer α) (accept : α → Bool) (index other : Nat)
    (value old : α) (valid : b.Valid accept) (accepted : accept value = true)
    (different : index ≠ other) (lookup : b.items[other]? = some old) :
    readRef ({b with items := b.items.set index value} : Buffer α) accept
      ⟨b.owner,b.epoch,other⟩ =
      some ⟨{b with items := b.items.set index value},old,1,b.capacity+2⟩ := by
  apply readRef_runs _ _ _ _ (writeRef_preserves_valid b accept index value valid accepted)
  simpa [List.getElem?_set_ne different] using lookup

end Proofs.CppVector
