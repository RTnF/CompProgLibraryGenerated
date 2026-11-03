import Proofs.CppVectorCopyAssign

namespace Proofs.CppMoveHeaders
open Proofs.CppVector
open Proofs.CppVectorCopyAssign (Tracked)

-- Header IDs denote vector objects. Allocation IDs denote element storage.
-- Header/grant ID tables and per-element generations are model bookkeeping.
structure Header where
  allocation : Option Nat
  scope : Nat
  writable : Bool
  limit : Nat
  deriving DecidableEq, Repr

structure Grant where
  reference : Proofs.CppVectorCopyAssign.Reference
  writable : Bool
  deriving DecidableEq, Repr

structure Heap (α : Type) where
  headers : List (Option Header)
  allocations : List (Option (Tracked α))
  grants : List Grant
  work : Nat := 0
  peak : Nat := 0
  baseSpace : Nat := 0

def Heap.header (s : Heap α) (id : Nat) : Option Header := (s.headers[id]?).join
def Heap.allocation (s : Heap α) (id : Nat) : Option (Tracked α) := (s.allocations[id]?).join

-- One unit per live vector header, plus element capacities. Grant tables,
-- tombstones, identities and lifetime generations are not C++ resident space.
def Heap.liveSpace (s : Heap α) : Nat :=
  s.headers.countP (·.isSome) + (s.allocations.map fun allocation =>
    match allocation with | none => 0 | some tracked => tracked.buffer.capacity).sum

def readable (s : Heap α) (header : Header) (accept : α → Bool) : Bool :=
  match header.allocation with
  | none => true
  | some id => match s.allocation id with
    | none => false
    | some tracked => decide (tracked.buffer.owner = id ∧ tracked.buffer.limit = header.limit ∧ tracked.buffer.Valid accept)

-- Captured grants do not follow the mutable header after allocation transfer.
def read (s : Heap α) (accept : α → Bool) (id : Nat) : Option α := do
  let grant ← s.grants[id]?
  let tracked ← s.allocation grant.reference.element.owner
  let result ← Proofs.CppVectorCopyAssign.read tracked accept grant.reference
  pure result.value

-- Like read/capture, this is a data helper; caller expression evaluation
-- accounts for the reference access, not the ghost grant lookup algorithm.
def write (s : Heap α) (accept : α → Bool) (id : Nat) (value : α) : Option (Heap α) := do
  let grant ← s.grants[id]?
  let tracked ← s.allocation grant.reference.element.owner
  if grant.reference.generation = tracked.generation grant.reference.element.index then
    let result ← Proofs.CppVector.writeRef tracked.buffer accept grant.writable grant.reference.element value
    some {s with allocations := s.allocations.set grant.reference.element.owner (some {tracked with buffer := result.buffer})}
  else none

def capture (s : Heap α) (accept : α → Bool) (headerId : Nat) (index : Int) (writable : Bool) :
    Option (Heap α × Nat) := do
  let header ← s.header headerId
  if writable = true → header.writable = true then
    let owner ← header.allocation
    let tracked ← s.allocation owner
    if tracked.buffer.owner = owner ∧ tracked.buffer.limit = header.limit then
      let reference ← Proofs.CppVectorCopyAssign.reference tracked accept index
      some ({s with grants := s.grants++[⟨reference,writable⟩]},s.grants.length)
    else none
  else none

-- Allocation payload and generations are transferred unchanged. Destination
-- constness changes access through that object, not existing captured grants.
def constructed (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) : Heap α :=
  {s with
    headers := (s.headers.set source (some {header with allocation := none}))++[some ⟨header.allocation,scope,writable,header.limit⟩]
    work := s.work+1
    peak := max s.peak (s.liveSpace+1-s.baseSpace)}

def moveConstruct (s : Heap α) (accept : α → Bool) (source scope : Nat) (writable : Bool) : Option (Heap α × Nat) := do
  let header ← s.header source
  if header.writable ∧ readable s header accept then
    some (constructed s source header scope writable,s.headers.length)
  else none

def Unique (s : Heap α) : Prop :=
  ∀ i j hi hj owner, s.header i = some hi → s.header j = some hj →
    hi.allocation = some owner → hj.allocation = some owner → i = j

theorem constructed_grants (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) :
    (constructed s source header scope writable).grants = s.grants := rfl

theorem constructed_allocations (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) :
    (constructed s source header scope writable).allocations = s.allocations := rfl

theorem constructed_read (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (accept : α → Bool) (reference : Nat) :
    read (constructed s source header scope writable) accept reference = read s accept reference := rfl

theorem source_inside (s : Heap α) (source : Nat) (header : Header) (found : s.header source = some header) :
    source < s.headers.length := by
  unfold Heap.header at found
  cases actual : s.headers[source]? with
  | none => simp [actual] at found
  | some value => exact (List.getElem?_eq_some_iff.mp actual).1

theorem constructed_length (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) :
    (constructed s source header scope writable).headers.length = s.headers.length+1 := by
  simp [constructed,List.length_set]

theorem constructed_source (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (found : s.header source = some header) :
    (constructed s source header scope writable).header source = some {header with allocation := none} := by
  have inside := source_inside s source header found
  simp only [Heap.header,constructed]
  rw [List.getElem?_append_left (by simpa using inside)]
  rw [List.getElem?_set_self inside]
  rfl

theorem constructed_target (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) :
    (constructed s source header scope writable).header s.headers.length = some ⟨header.allocation,scope,writable,header.limit⟩ := by
  simp [Heap.header,constructed,List.length_set]

theorem constructed_other (s : Heap α) (source other : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (inside : other < s.headers.length) (different : source ≠ other) :
    (constructed s source header scope writable).header other = s.header other := by
  simp only [Heap.header,constructed]
  rw [List.getElem?_append_left (by simpa using inside)]
  rw [List.getElem?_set_ne different]


theorem constructed_owner_cases (s : Heap α) (source i : Nat) (header hi : Header) (scope : Nat) (writable : Bool)
    (found : s.header source = some header)
    (nextFound : (constructed s source header scope writable).header i = some hi)
    (owner : Nat) (owns : hi.allocation = some owner) :
    (i = s.headers.length ∧ hi = ⟨header.allocation,scope,writable,header.limit⟩) ∨
      (i < s.headers.length ∧ i ≠ source ∧ s.header i = some hi) := by
  by_cases inside : i < s.headers.length
  · have different : i ≠ source := by
      intro equal
      subst i
      have same := Option.some.inj ((constructed_source s source header scope writable found).symm.trans nextFound)
      have allocation := congrArg Header.allocation same
      rw [owns] at allocation
      contradiction
    exact Or.inr ⟨inside,different,(constructed_other s source i header scope writable inside (Ne.symm different)).symm.trans nextFound⟩
  · have bound := source_inside (constructed s source header scope writable) i hi nextFound
    rw [constructed_length] at bound
    have equal : i = s.headers.length := by omega
    subst i
    exact Or.inl ⟨rfl,(Option.some.inj ((constructed_target s source header scope writable).symm.trans nextFound)).symm⟩

theorem constructed_unique (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (unique : Unique s) (found : s.header source = some header) :
    Unique (constructed s source header scope writable) := by
  intro i j hi hj owner iFound jFound iOwns jOwns
  rcases constructed_owner_cases s source i header hi scope writable found iFound owner iOwns with
    ⟨rfl,rfl⟩ | ⟨_,iDifferent,iOld⟩
  · rcases constructed_owner_cases s source j header hj scope writable found jFound owner jOwns with
      ⟨rfl,rfl⟩ | ⟨_,jDifferent,jOld⟩
    · rfl
    · have same := unique source j header hj owner found jOld iOwns jOwns
      exact False.elim (jDifferent same.symm)
  · rcases constructed_owner_cases s source j header hj scope writable found jFound owner jOwns with
      ⟨rfl,rfl⟩ | ⟨_,_,jOld⟩
    · have same := unique i source hi header owner iOld found iOwns jOwns
      exact False.elim (iDifferent same)
    · exact unique i j hi hj owner iOld jOld iOwns jOwns


theorem move_construct_runs (s : Heap α) (accept : α → Bool) (source scope : Nat) (header : Header) (writable : Bool)
    (found : s.header source = some header) (permission : header.writable = true) (valid : readable s header accept = true) :
    moveConstruct s accept source scope writable = some (constructed s source header scope writable,s.headers.length) := by
  simp [moveConstruct,found,permission,valid]

theorem move_construct_success (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (ran : moveConstruct s accept source scope writable = some (out,destination)) :
    ∃ header, s.header source = some header ∧ destination = s.headers.length ∧
      out = constructed s source header scope writable := by
  unfold moveConstruct at ran
  cases found : s.header source with
  | none => simp [found] at ran
  | some header =>
    simp only [found,Bind.bind,Option.bind] at ran
    split at ran
    · have same := Prod.mk.inj (Option.some.inj ran)
      exact ⟨header,rfl,same.2.symm,same.1.symm⟩
    · simp at ran

theorem move_construct_read (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (ran : moveConstruct s accept source scope writable = some (out,destination)) (reference : Nat) :
    read out accept reference = read s accept reference := by
  obtain ⟨header,_,_,same⟩ := move_construct_success s out accept source scope destination writable ran
  rw [same]
  rfl

theorem move_construct_unique (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (unique : Unique s) (ran : moveConstruct s accept source scope writable = some (out,destination)) : Unique out := by
  obtain ⟨header,found,_,same⟩ := move_construct_success s out accept source scope destination writable ran
  rw [same]
  exact constructed_unique s source header scope writable unique found


-- Every live allocation still has an owning vector header; aliases are IDs,
-- not additional owners. This is separate from at-most-one ownership.
def OwnsAll (s : Heap α) : Prop :=
  ∀ owner tracked, s.allocation owner = some tracked →
    ∃ id header, s.header id = some header ∧ header.allocation = some owner

theorem constructed_ownsAll (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (covered : OwnsAll s) (found : s.header source = some header) :
    OwnsAll (constructed s source header scope writable) := by
  intro owner tracked allocation
  have previous : s.allocation owner = some tracked := allocation
  obtain ⟨id,actual,oldFound,owns⟩ := covered owner tracked previous
  by_cases same : id = source
  · subst id
    have headerEq := Option.some.inj (oldFound.symm.trans found)
    subst actual
    exact ⟨s.headers.length,⟨header.allocation,scope,writable,header.limit⟩,
      constructed_target s source header scope writable,owns⟩
  · exact ⟨id,actual,(constructed_other s source id header scope writable
      (source_inside s id actual oldFound) (Ne.symm same)).trans oldFound,owns⟩

theorem move_construct_ownsAll (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (covered : OwnsAll s) (ran : moveConstruct s accept source scope writable = some (out,destination)) : OwnsAll out := by
  obtain ⟨header,found,_,same⟩ := move_construct_success s out accept source scope destination writable ran
  rw [same]
  exact constructed_ownsAll s source header scope writable covered found


theorem header_lookup (s : Heap α) (source : Nat) (header : Header) (found : s.header source = some header) :
    s.headers[source]? = some (some header) := by
  unfold Heap.header at found
  cases actual : s.headers[source]? with
  | none => simp [actual] at found
  | some value =>
    cases value with
    | none => simp [actual] at found
    | some h =>
      simp only [actual,Option.join] at found
      cases Option.some.inj found
      rfl

theorem constructed_space (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (found : s.header source = some header) :
    (constructed s source header scope writable).liveSpace = s.liveSpace+1 := by
  have raw := header_lookup s source header found
  have inside := source_inside s source header found
  have atIndex : s.headers[source] = some header := (List.getElem?_eq_some_iff.mp raw).2
  have count : 1 ≤ s.headers.countP (·.isSome) := by
    have bound := List.boole_getElem_le_countP (p := fun (h : Option Header) => h.isSome) inside
    simpa only [atIndex,Option.isSome_some,↓reduceIte] using bound
  have kept : (s.headers.set source (some {header with allocation := none})).countP (·.isSome) = s.headers.countP (·.isSome) := by
    rw [List.countP_set inside]
    simp only [atIndex,Option.isSome_some,↓reduceIte]
    omega
  simp only [Heap.liveSpace,constructed,List.countP_append,kept]
  simp [Nat.add_assoc,Nat.add_comm]

theorem constructed_resources (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool) :
    (constructed s source header scope writable).work = s.work+1 ∧
      (constructed s source header scope writable).peak = max s.peak (s.liveSpace+1-s.baseSpace) ∧
      (constructed s source header scope writable).baseSpace = s.baseSpace := ⟨rfl,rfl,rfl⟩

theorem move_construct_resources (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (ran : moveConstruct s accept source scope writable = some (out,destination)) :
    out.work = s.work+1 ∧ out.liveSpace = s.liveSpace+1 ∧
      out.peak = max s.peak (out.liveSpace-s.baseSpace) ∧ out.baseSpace = s.baseSpace := by
  obtain ⟨header,found,_,same⟩ := move_construct_success s out accept source scope destination writable ran
  rw [same]
  have space := constructed_space s source header scope writable found
  exact ⟨rfl,space,by rw [space]; rfl,rfl⟩


theorem constructed_write (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (accept : α → Bool) (reference : Nat) (value : α) :
    (write (constructed s source header scope writable) accept reference value).map (·.allocations) =
      (write s accept reference value).map (·.allocations) := by
  unfold write
  cases grantFound : s.grants[reference]? with
  | none => simp [constructed,grantFound]
  | some grant =>
    simp only [constructed,grantFound,Heap.allocation,Bind.bind,Option.bind]
    cases (s.allocations[grant.reference.element.owner]?).join with
    | none => rfl
    | some tracked =>
      dsimp only
      split
      · cases Proofs.CppVector.writeRef tracked.buffer accept grant.writable grant.reference.element value <;> rfl
      · rfl

theorem write_readonly (s : Heap α) (accept : α → Bool) (reference : Nat) (value : α) (grant : Grant)
    (found : s.grants[reference]? = some grant) (readonly : grant.writable = false) :
    write s accept reference value = none := by
  simp only [write,found,Bind.bind,Option.bind]
  cases trackedFound : s.allocation grant.reference.element.owner with
  | none => rfl
  | some tracked => simp [Proofs.CppVector.writeRef,readonly]


theorem move_construct_write (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (ran : moveConstruct s accept source scope writable = some (out,destination)) (reference : Nat) (value : α) :
    (write out accept reference value).map (·.allocations) = (write s accept reference value).map (·.allocations) := by
  obtain ⟨header,_,_,same⟩ := move_construct_success s out accept source scope destination writable ran
  rw [same]
  exact constructed_write s source header scope writable accept reference value

end Proofs.CppMoveHeaders
