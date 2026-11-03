import Proofs.CppMoveFrame
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

namespace Proofs.CppMoveSpace
open Proofs.CppMoveHeaders

def headerAllocation (s : Heap α) (id : Nat) : Option Nat :=
  (s.header id).bind (fun header => header.allocation)

def allocatedHeaders (s : Heap α) : Finset Nat :=
  (Finset.range s.headers.length).filter (fun id => (headerAllocation s id).isSome)

def liveAllocations (s : Heap α) : Finset Nat :=
  (Finset.range s.allocations.length).filter (fun owner => (s.allocation owner).isSome)

def HeadersLive (s : Heap α) : Prop :=
  ∀ id header owner, s.header id = some header → header.allocation = some owner →
    (s.allocation owner).isSome

theorem allocated_parts (s : Heap α) (id : Nat) (member : id ∈ allocatedHeaders s) :
    ∃ header owner, s.header id = some header ∧ header.allocation = some owner := by
  have live := (Finset.mem_filter.mp member).2
  cases hf : s.header id with
  | none => simp [headerAllocation,hf] at live
  | some header =>
    cases owns : header.allocation with
    | none => simp [headerAllocation,hf,owns] at live
    | some owner => exact ⟨header,owner,rfl,owns⟩

theorem live_parts (s : Heap α) (owner : Nat) (member : owner ∈ liveAllocations s) :
    ∃ tracked, s.allocation owner = some tracked := by
  have live := (Finset.mem_filter.mp member).2
  cases found : s.allocation owner with
  | none => simp [found] at live
  | some tracked => exact ⟨tracked,rfl⟩

-- A root header is counted exactly once for each live allocation. The other
-- live headers are empty objects and get capacity-zero projection entries.
theorem owner_count (s : Heap α) (unique : Unique s) (covered : OwnsAll s) (live : HeadersLive s) :
    (allocatedHeaders s).card = (liveAllocations s).card := by
  let f : ∀ id ∈ allocatedHeaders s, Nat := fun id _ => (headerAllocation s id).getD 0
  apply Finset.card_bij f
  · intro id member
    obtain ⟨header,owner,hf,owns⟩ := allocated_parts s id member
    have value : f id member = owner := by simp [f,headerAllocation,hf,owns]
    rw [value]
    have existsOwner := live id header owner hf owns
    cases found : s.allocation owner with
    | none => simp [found] at existsOwner
    | some tracked =>
      have inside := Proofs.CppMoveAssign.allocation_inside s owner tracked found
      simp [liveAllocations,inside,found]
  · intro first firstMem second secondMem same
    obtain ⟨fh,fo,ff,fa⟩ := allocated_parts s first firstMem
    obtain ⟨sh,so,sf,sa⟩ := allocated_parts s second secondMem
    have equal : fo = so := by simpa [f,headerAllocation,ff,sf,fa,sa] using same
    subst so
    exact unique first second fh sh fo ff sf fa sa
  · intro owner member
    obtain ⟨tracked,found⟩ := live_parts s owner member
    obtain ⟨id,header,hf,owns⟩ := covered owner tracked found
    have inside := source_inside s id header hf
    have idMem : id ∈ allocatedHeaders s := by
      simp only [allocatedHeaders,Finset.mem_filter,Finset.mem_range]
      exact ⟨inside,by simp [headerAllocation,hf,owns]⟩
    exact ⟨id,idMem,by simp [f,headerAllocation,hf,owns]⟩


def liveHeaders (s : Heap α) : Finset Nat :=
  (Finset.range s.headers.length).filter (fun id => (s.header id).isSome)

def emptyHeaders (s : Heap α) : Finset Nat :=
  (liveHeaders s).filter (fun id => headerAllocation s id = none)

theorem allocated_filter (s : Heap α) :
    allocatedHeaders s = (liveHeaders s).filter (fun id => (headerAllocation s id).isSome) := by
  ext id
  simp only [allocatedHeaders,liveHeaders,Finset.mem_filter]
  cases hf : s.header id <;> simp [headerAllocation,hf]

theorem header_partition (s : Heap α) :
    (allocatedHeaders s).card + (emptyHeaders s).card = (liveHeaders s).card := by
  rw [allocated_filter]
  have split := Finset.card_filter_add_card_filter_not (s := liveHeaders s)
    (fun id => (headerAllocation s id).isSome = true)
  simpa [emptyHeaders] using split

theorem header_allocation_count (s : Heap α) (unique : Unique s) (covered : OwnsAll s) (live : HeadersLive s) :
    (liveAllocations s).card + (emptyHeaders s).card = (liveHeaders s).card := by
  rw [← owner_count s unique covered live]
  exact header_partition s

theorem headersLive_of_readable (s : Heap α) (accept : α → Bool)
    (valid : ∀ id header, s.header id = some header → readable s header accept = true) : HeadersLive s := by
  intro id header owner found owns
  have good := valid id header found
  cases actual : s.allocation owner with
  | none => simp [readable,owns,actual] at good
  | some tracked => simp


-- The range traversal used by Frame.liveSpace enumerates each list slot once.
theorem range_join_list (xs : List (Option α)) :
    (List.range xs.length).map (fun i => (xs[i]?).join) = xs := by
  apply List.ext_getElem?
  intro i
  by_cases inside : i < xs.length
  · simp only [List.getElem?_map,List.getElem?_range inside,Option.map_some]
    have slot := List.getElem?_eq_getElem inside
    rw [slot]
    rfl
  · have outside : xs.length ≤ i := by omega
    have missing : xs[i]? = none := List.getElem?_eq_none_iff.mpr outside
    have rangeMissing : (List.range xs.length)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa using outside)
    simp [List.getElem?_map,rangeMissing,missing]

theorem list_some_count (xs : List (Option α)) :
    ((Finset.range xs.length).filter (fun i => (xs[i]?).join.isSome)).card = xs.countP (·.isSome) := by
  have counted := (show (List.range xs.length).Nodup from List.nodup_range).card_eq_countP
    (P := fun i => (xs[i]?).join.isSome = true)
  have traversal := congrArg (fun ys : List (Option α) => ys.countP (·.isSome)) (range_join_list xs)
  simp only [List.countP_map] at traversal
  have rangeFinset : (List.range xs.length).toFinset = Finset.range xs.length := by
    ext i
    simp
  have countedEq : ((Finset.range xs.length).filter (fun i => (xs[i]?).join.isSome)).card =
      (List.range xs.length).countP (fun i => (xs[i]?).join.isSome) := by simpa [rangeFinset] using counted
  exact countedEq.trans traversal

theorem liveHeaders_countP (s : Heap α) :
    (liveHeaders s).card = s.headers.countP (·.isSome) := by
  exact list_some_count s.headers

theorem liveAllocations_countP (s : Heap α) :
    (liveAllocations s).card = s.allocations.countP (·.isSome) := by
  exact list_some_count s.allocations

def entrySpace (entry : Option (Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value × Proofs.CppVectorOwnership.Tag)) : Nat :=
  match entry with
  | none => 0
  | some (buffer,tag) => buffer.capacity + if tag.parent = none then 1 else 0

theorem materialize_nodeSpace (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty) (owner : Nat) :
    (Proofs.CppMoveFrame.materialize s ty).frame.state.nodeSpace owner =
      entrySpace ((Proofs.CppMoveFrame.entries s.heap ty)[owner]?).join := by
  cases slot : (Proofs.CppMoveFrame.entries s.heap ty)[owner]? with
  | none => simp [Proofs.CppNestedVectorStore.State.nodeSpace,Proofs.CppMoveFrame.materialize,
      Proofs.CppVectorOwnership.Forest.lookup,Proofs.CppVectorStore.Store.lookup,List.getElem?_map,slot,entrySpace]
  | some entry =>
    cases entry with
    | none => simp [Proofs.CppNestedVectorStore.State.nodeSpace,Proofs.CppMoveFrame.materialize,
        Proofs.CppVectorOwnership.Forest.lookup,Proofs.CppVectorStore.Store.lookup,List.getElem?_map,slot,entrySpace]
    | some pair =>
      rcases pair with ⟨buffer,tag⟩
      simp [Proofs.CppNestedVectorStore.State.nodeSpace,Proofs.CppMoveFrame.materialize,
        Proofs.CppVectorOwnership.Forest.lookup,Proofs.CppVectorStore.Store.lookup,List.getElem?_map,slot,entrySpace]

theorem materialize_space_sum (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty) :
    (Proofs.CppMoveFrame.materialize s ty).frame.state.liveSpace =
      ((Proofs.CppMoveFrame.entries s.heap ty).map entrySpace).sum := by
  unfold Proofs.CppNestedVectorStore.State.liveSpace
  have lengthEq : (Proofs.CppMoveFrame.materialize s ty).frame.state.storage.objects.length =
      (Proofs.CppMoveFrame.entries s.heap ty).length := by simp [Proofs.CppMoveFrame.materialize]
  rw [lengthEq]
  have traversal := congrArg (fun xs => (xs.map entrySpace).sum)
    (range_join_list (Proofs.CppMoveFrame.entries s.heap ty))
  simp only [List.map_map] at traversal
  convert traversal using 2
  apply List.map_congr_left
  intro owner _
  exact materialize_nodeSpace s ty owner


def allocationWeight (entry : Option (Proofs.CppVectorCopyAssign.Tracked Int)) : Nat :=
  match entry with | none => 0 | some tracked => tracked.buffer.capacity+1

def emptyWeight (entry : Option Header) : Nat :=
  match entry with | none => 0 | some header => if header.allocation = none then 1 else 0

theorem projection_weights (s : Heap Int) (ty : Proofs.CppScalar.Ty) (covered : OwnsAll s) :
    (Proofs.CppMoveFrame.entries s ty).map entrySpace =
      (s.allocations.map allocationWeight) ++ (s.headers.map emptyWeight) := by
  unfold Proofs.CppMoveFrame.entries
  rw [List.map_append]
  congr 1
  · apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map,List.getElem?_mapIdx]
    cases slot : s.allocations[i]? with
    | none => simp
    | some entry =>
      cases entry with
      | none => simp [entrySpace,allocationWeight]
      | some tracked =>
        have actual : s.allocation i = some tracked := by simp [Heap.allocation,slot]
        obtain ⟨header,hf⟩ := Proofs.CppMoveFrame.ownerHeader_exists s i tracked covered actual
        simp [hf,entrySpace,allocationWeight,Proofs.CppMoveFrame.box]
  · apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map,List.getElem?_mapIdx]
    cases slot : s.headers[i]? with
    | none => simp
    | some entry =>
      cases entry with
      | none => simp [entrySpace,emptyWeight]
      | some header =>
        cases owns : header.allocation <;> simp [owns,entrySpace,emptyWeight]

theorem allocation_weight_sum (xs : List (Option (Proofs.CppVectorCopyAssign.Tracked Int))) :
    (xs.map allocationWeight).sum =
      (xs.map (fun entry => match entry with | none => 0 | some tracked => tracked.buffer.capacity)).sum +
        xs.countP (·.isSome) := by
  induction xs with
  | nil => simp
  | cons entry xs ih =>
    cases entry <;> simp [allocationWeight,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


theorem list_predicate_count (xs : List (Option α)) (predicate : Option α → Bool) :
    ((Finset.range xs.length).filter (fun i => predicate (xs[i]?).join)).card = xs.countP predicate := by
  have counted := (show (List.range xs.length).Nodup from List.nodup_range).card_eq_countP
    (P := fun i => predicate (xs[i]?).join = true)
  have traversal := congrArg (fun ys : List (Option α) => ys.countP predicate) (range_join_list xs)
  simp only [List.countP_map] at traversal
  have rangeFinset : (List.range xs.length).toFinset = Finset.range xs.length := by ext i; simp
  have countedEq : ((Finset.range xs.length).filter (fun i => predicate (xs[i]?).join)).card =
      (List.range xs.length).countP (fun i => predicate (xs[i]?).join) := by simpa [rangeFinset] using counted
  exact countedEq.trans traversal

def isEmptyHeader (entry : Option Header) : Bool := entry.any (fun header => header.allocation.isNone)

theorem empty_weight_sum (xs : List (Option Header)) :
    (xs.map emptyWeight).sum = xs.countP isEmptyHeader := by
  induction xs with
  | nil => simp
  | cons entry xs ih =>
    cases entry with
    | none => simp [emptyWeight,isEmptyHeader,ih]
    | some header => cases owns : header.allocation <;> simp [emptyWeight,isEmptyHeader,owns,ih,Nat.add_comm]

theorem emptyHeaders_weight (s : Heap Int) :
    (emptyHeaders s).card = (s.headers.map emptyWeight).sum := by
  have sets : emptyHeaders s =
      (Finset.range s.headers.length).filter (fun i => isEmptyHeader (s.headers[i]?).join) := by
    ext i
    simp only [emptyHeaders,liveHeaders,Finset.mem_filter]
    change ((i ∈ Finset.range s.headers.length ∧ (s.header i).isSome = true) ∧ headerAllocation s i = none) ↔
      (i ∈ Finset.range s.headers.length ∧ isEmptyHeader (s.header i) = true)
    cases hf : s.header i with
    | none => simp [headerAllocation,hf,isEmptyHeader]
    | some header => cases owns : header.allocation <;> simp [headerAllocation,hf,isEmptyHeader,owns]
  rw [sets,list_predicate_count,empty_weight_sum]

theorem materialize_liveSpace (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty)
    (unique : Unique s.heap) (covered : OwnsAll s.heap) (live : HeadersLive s.heap) :
    (Proofs.CppMoveFrame.materialize s ty).frame.state.liveSpace = s.heap.liveSpace := by
  rw [materialize_space_sum,projection_weights s.heap ty covered,List.sum_append,allocation_weight_sum]
  have count := header_allocation_count s.heap unique covered live
  rw [liveAllocations_countP,liveHeaders_countP,emptyHeaders_weight] at count
  calc
    _ = s.heap.headers.countP (·.isSome) +
        (s.heap.allocations.map (fun entry => match entry with | none => 0 | some tracked => tracked.buffer.capacity)).sum := by omega
    _ = s.heap.liveSpace := by
      unfold Heap.liveSpace
      congr 1
      congr 1
      apply List.map_congr_left
      intro entry _
      cases entry <;> rfl



theorem assigned_allocation_other (s : Heap α) (target source owner : Nat) (th sh : Header)
    (different : th.allocation ≠ some owner) :
    (Proofs.CppMoveAssign.assigned s target source th sh).allocation owner = s.allocation owner := by
  change (Proofs.CppMoveAssign.retire s th.allocation).allocation owner = _
  cases alloc : th.allocation with
  | none => rfl
  | some old =>
    have ne : old ≠ owner := by intro eq; subst old; exact different alloc
    exact Proofs.CppMoveAssign.retire_other s old owner ne

theorem assigned_headersLive (s : Heap α) (target source : Nat) (th sh : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh)
    (unique : Unique s) (live : HeadersLive s) :
    HeadersLive (Proofs.CppMoveAssign.assigned s target source th sh) := by
  intro id header owner found owns
  rcases Proofs.CppMoveAssign.assigned_owner_cases s target source id owner th sh header tf sf found owns with
    ⟨_,different,headerEq⟩ | ⟨notTarget,_,oldFound⟩
  · have sourceOwns : sh.allocation = some owner := by simpa [headerEq] using owns
    have separate : th.allocation ≠ some owner := by
      intro sameOwner
      exact different (unique target source th sh owner tf sf sameOwner sourceOwns)
    rw [assigned_allocation_other s target source owner th sh separate]
    exact live source sh owner sf sourceOwns
  · have separate : th.allocation ≠ some owner := by
      intro sameOwner
      exact notTarget (unique id target header th owner oldFound tf owns sameOwner)
    rw [assigned_allocation_other s target source owner th sh separate]
    exact live id header owner oldFound owns

theorem constructed_headersLive (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (found : s.header source = some header) (live : HeadersLive s) :
    HeadersLive (constructed s source header scope writable) := by
  intro id actual owner actualFound owns
  rcases constructed_owner_cases s source id header actual scope writable found actualFound owner owns with
    ⟨_,headerEq⟩ | ⟨_,_,oldFound⟩
  · have originalOwns : header.allocation = some owner := by simpa [headerEq] using owns
    exact live source header owner found originalOwns
  · exact live id actual owner oldFound owns

theorem assign_headersLive (s out : Proofs.CppMoveViews.State Int) (accept : Int → Bool) (target source : Nat)
    (run : Proofs.CppMoveViews.assign s accept target source = some out)
    (unique : Unique s.heap) (live : HeadersLive s.heap) : HeadersLive out.heap := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ := Proofs.CppMoveViews.assign_success s out accept target source run
  obtain ⟨th,sh,tf,sf,heapEq⟩ := Proofs.CppMoveAssign.move_assign_success s.heap out.heap accept tv.header sv.header core
  rw [heapEq]
  exact assigned_headersLive s.heap tv.header sv.header th sh tf sf unique live

theorem construct_headersLive (s out : Proofs.CppMoveViews.State Int) (accept : Int → Bool)
    (source scope slot : Nat) (writable : Bool)
    (run : Proofs.CppMoveViews.construct s accept source scope writable = some (out,slot))
    (live : HeadersLive s.heap) : HeadersLive out.heap := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := Proofs.CppMoveViews.construct_success s out accept source scope slot writable run
  obtain ⟨header,found,_,heapEq⟩ := move_construct_success s.heap out.heap accept view.header scope destination writable core
  rw [heapEq]
  exact constructed_headersLive s.heap view.header header scope writable found live

end Proofs.CppMoveSpace
