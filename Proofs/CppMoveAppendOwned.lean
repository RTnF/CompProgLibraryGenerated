import Proofs.CppMoveSpace

namespace Proofs.CppMoveAppendOwned
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppMoveFrame Proofs.CppMoveSpace

-- Representation export of an already constructed owned buffer. Constructor
-- execution supplies its counters separately; this table operation adds none.
def appended (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) : Heap α :=
  {s with
    headers := s.headers++[some ⟨some s.allocations.length,scope,writable,buffer.limit⟩],
    allocations := s.allocations++[some ⟨{buffer with owner := s.allocations.length},fun _ => 0⟩]}

theorem append_lookup (entries : List (Option α)) (id : Nat) :
    ((entries++[some value])[id]?).join =
      if id = entries.length then some value else (entries[id]?).join := by
  by_cases old : id < entries.length
  · rw [List.getElem?_append_left old,ite_eq_right (by omega)]
  · by_cases same : id = entries.length
    · subst id
      simp
    · have outside : (entries++[some value]).length ≤ id := by simp only [List.length_append,List.length_cons,List.length_nil]; omega
      have original : entries.length ≤ id := by omega
      rw [List.getElem?_eq_none_iff.mpr outside,List.getElem?_eq_none_iff.mpr original,ite_eq_right same]

theorem header_lookup (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) (id : Nat) :
    (appended s buffer scope writable).header id =
      if id = s.headers.length then some ⟨some s.allocations.length,scope,writable,buffer.limit⟩ else s.header id :=
  append_lookup s.headers id

theorem allocation_lookup (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) (id : Nat) :
    (appended s buffer scope writable).allocation id =
      if id = s.allocations.length then some ⟨{buffer with owner := s.allocations.length},fun _ => 0⟩ else s.allocation id :=
  append_lookup s.allocations id

theorem old_header (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) (id : Nat)
    (inside : id < s.headers.length) :
    (appended s buffer scope writable).header id = s.header id := by
  rw [header_lookup,ite_eq_right (by omega)]

theorem old_allocation (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) (id : Nat)
    (inside : id < s.allocations.length) :
    (appended s buffer scope writable).allocation id = s.allocation id := by
  rw [allocation_lookup,ite_eq_right (by omega)]

theorem header_owner_bound (s : Heap α) (live : HeadersLive s) (id : Nat) (header : Header) (owner : Nat)
    (found : s.header id = some header) (allocation : header.allocation = some owner) : owner < s.allocations.length := by
  have present := live id header owner found allocation
  cases slot : s.allocation owner with
  | none => simp [slot] at present
  | some tracked => exact Proofs.CppMoveAssign.allocation_inside s owner tracked slot

theorem appended_unique (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool)
    (unique : Unique s) (live : HeadersLive s) : Unique (appended s buffer scope writable) := by
  intro i j hi hj owner fi fj ai aj
  rw [header_lookup] at fi fj
  by_cases ni : i = s.headers.length
  · subst i
    rw [ite_eq_left rfl] at fi
    cases Option.some.inj fi
    have ownerEq : owner = s.allocations.length := Option.some.inj ai.symm
    by_cases nj : j = s.headers.length
    · exact nj.symm
    · rw [ite_eq_right nj] at fj
      have bound := header_owner_bound s live j hj owner fj aj
      omega
  · rw [ite_eq_right ni] at fi
    by_cases nj : j = s.headers.length
    · subst j
      rw [ite_eq_left rfl] at fj
      cases Option.some.inj fj
      have ownerEq : owner = s.allocations.length := Option.some.inj aj.symm
      have bound := header_owner_bound s live i hi owner fi ai
      omega
    · rw [ite_eq_right nj] at fj
      exact unique i j hi hj owner fi fj ai aj

theorem appended_ownsAll (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool)
    (covered : OwnsAll s) : OwnsAll (appended s buffer scope writable) := by
  intro owner tracked found
  rw [allocation_lookup] at found
  by_cases fresh : owner = s.allocations.length
  · subst owner
    exact ⟨s.headers.length,⟨some s.allocations.length,scope,writable,buffer.limit⟩,by simp [header_lookup],rfl⟩
  · rw [ite_eq_right fresh] at found
    obtain ⟨id,header,hf,allocation⟩ := covered owner tracked found
    have inside := (List.getElem?_eq_some_iff.mp (Proofs.CppMoveHeaders.header_lookup s id header hf)).1
    exact ⟨id,header,(old_header s buffer scope writable id inside).trans hf,allocation⟩

theorem appended_headersLive (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool)
    (live : HeadersLive s) : HeadersLive (appended s buffer scope writable) := by
  intro id header owner found allocation
  rw [header_lookup] at found
  by_cases fresh : id = s.headers.length
  · rw [ite_eq_left fresh] at found
    cases Option.some.inj found
    have ownerEq : owner = s.allocations.length := Option.some.inj allocation.symm
    subst owner
    simp [allocation_lookup]
  · rw [ite_eq_right fresh] at found
    have inside := header_owner_bound s live id header owner found allocation
    rw [old_allocation s buffer scope writable owner inside]
    exact live id header owner found allocation

theorem appended_valid (s : Heap Int) (buffer : Buffer Int) (scope : Nat) (writable : Bool) (ty : Proofs.CppScalar.Ty)
    (oldValid : AllocationsValid s ty) (valid : buffer.Valid ty.valid) :
    AllocationsValid (appended s buffer scope writable) ty := by
  intro owner tracked found
  rw [allocation_lookup] at found
  by_cases fresh : owner = s.allocations.length
  · rw [ite_eq_left fresh] at found
    cases Option.some.inj found
    exact ⟨fresh.symm,valid⟩
  · rw [ite_eq_right fresh] at found
    exact oldValid owner tracked found

theorem old_read (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool)
    (accept : α → Bool) (id : Nat) (grant : Grant) (found : s.grants[id]? = some grant)
    (inside : grant.reference.element.owner < s.allocations.length) :
    Proofs.CppMoveHeaders.read (appended s buffer scope writable) accept id = Proofs.CppMoveHeaders.read s accept id := by
  unfold Proofs.CppMoveHeaders.read
  change (do let grant ← s.grants[id]?; let tracked ← (appended s buffer scope writable).allocation grant.reference.element.owner; let result ← Proofs.CppVectorCopyAssign.read tracked accept grant.reference; pure result.value) = _
  rw [found]
  change (do let tracked ← (appended s buffer scope writable).allocation grant.reference.element.owner; let result ← Proofs.CppVectorCopyAssign.read tracked accept grant.reference; pure result.value) =
    (do let tracked ← s.allocation grant.reference.element.owner; let result ← Proofs.CppVectorCopyAssign.read tracked accept grant.reference; pure result.value)
  rw [old_allocation s buffer scope writable _ inside]

theorem current_buffer (s : Heap Int) (buffer : Buffer Int) (scope : Nat) (writable : Bool) :
    currentBuffer (appended s buffer scope writable) s.headers.length
      ⟨some s.allocations.length,scope,writable,buffer.limit⟩ =
      some {buffer with owner := s.allocations.length} := by
  simp [currentBuffer,allocation_lookup]

theorem liveSpace (s : Heap α) (buffer : Buffer α) (scope : Nat) (writable : Bool) :
    (appended s buffer scope writable).liveSpace = s.liveSpace+1+buffer.capacity := by
  simp [Heap.liveSpace,appended,List.countP_append,List.map_append,List.sum_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end Proofs.CppMoveAppendOwned
