import Proofs.CppMoveWrite
import Proofs.CppMoveContext

namespace Proofs.CppMoveDestroy
open Proofs.CppMoveHeaders Proofs.CppMoveAssign

-- Header destruction ends the object lifetime and only its CURRENT allocation.
-- A moved-from empty header cannot retire storage now owned by another object.
def destroyed (s : Heap α) (id : Nat) (header : Header) : Heap α :=
  {retire s header.allocation with headers := s.headers.set id none,work := s.work+oldLength s header+1,peak := max s.peak (s.liveSpace-s.baseSpace)}

def destroyHeader (s : Heap α) (accept : α → Bool) (id : Nat) : Option (Heap α) := do
  let header ← s.header id
  if readable s header accept then some (destroyed s id header) else none

-- Scanning tombstones and scope IDs is interpreter bookkeeping, not C++ work.
-- Each actual destructor is charged separately by destroyHeader.
def destroyAtScope (s : Heap α) (accept : α → Bool) (scope id : Nat) : Option (Heap α) :=
  match s.header id with
  | none => some s
  | some header => if header.scope = scope then destroyHeader s accept id else some s

def destroyList : Heap α → (α → Bool) → Nat → List Nat → Option (Heap α)
  | s,_,_,[] => some s
  | s,accept,scope,id::tail => do
    let next ← destroyAtScope s accept scope id
    destroyList next accept scope tail

-- IDs are allocated by appending headers; assignment preserves the object ID.
-- Visit newest objects first, including moved-from headers, and skip tombstones.
def scopeOrder (s : Heap α) : List Nat := (List.range s.headers.length).reverse

theorem scopeOrder_mem (s : Heap α) (id : Nat) : id ∈ scopeOrder s ↔ id < s.headers.length := by
  simp [scopeOrder]

theorem scopeOrder_nodup (s : Heap α) : (scopeOrder s).Nodup := by simpa [scopeOrder] using (List.nodup_range (n := s.headers.length))

theorem scopeOrder_construct (s out : Heap α) (accept : α → Bool) (source scope destination : Nat) (writable : Bool)
    (run : moveConstruct s accept source scope writable = some (out,destination)) :
    scopeOrder out = destination :: scopeOrder s := by
  obtain ⟨header,_,dest,eq⟩ := move_construct_success s out accept source scope destination writable run
  subst out
  subst destination
  simp [scopeOrder,constructed,List.range_succ]

def destroyScope (s : Heap α) (accept : α → Bool) (scope : Nat) : Option (Heap α) :=
  destroyList s accept scope (scopeOrder s)

theorem destroyed_grants (s : Heap α) (id : Nat) (header : Header) :
    (destroyed s id header).grants = s.grants := retire_grants s header.allocation

theorem destroyed_sub (s : Heap α) (id : Nat) (header : Header) : AllocationSub s (destroyed s id header) :=
  retire_sub s header.allocation

theorem destroyed_none (s : Heap α) (id : Nat) (header : Header) (accept : α → Bool) (reference : Nat)
    (old : Proofs.CppMoveHeaders.read s accept reference = none) :
    Proofs.CppMoveHeaders.read (destroyed s id header) accept reference = none :=
  sub_read_none s _ accept reference (destroyed_grants s id header) (destroyed_sub s id header) old

theorem destroyed_header (s : Heap α) (id : Nat) (header : Header) (found : s.header id = some header) :
    (destroyed s id header).header id = none := by
  have inside := source_inside s id header found
  simp [destroyed,Heap.header,List.getElem?_set_self inside]

theorem destroyed_other (s : Heap α) (id other : Nat) (header : Header) (different : id ≠ other) :
    (destroyed s id header).header other = s.header other := by
  simp only [destroyed,Heap.header,List.getElem?_set_ne different]

theorem destroyed_header_cases (s : Heap α) (id other : Nat) (header actual : Header)
    (found : s.header id = some header) (actualFound : (destroyed s id header).header other = some actual) :
    id ≠ other ∧ s.header other = some actual := by
  by_cases same : id = other
  · subst other
    rw [destroyed_header s id header found] at actualFound
    contradiction
  · exact ⟨same,(destroyed_other s id other header same).symm.trans actualFound⟩

theorem destroyHeader_runs (s : Heap α) (accept : α → Bool) (id : Nat) (header : Header)
    (found : s.header id = some header) (valid : readable s header accept = true) :
    destroyHeader s accept id = some (destroyed s id header) := by simp [destroyHeader,found,valid]

theorem destroyHeader_success (s out : Heap α) (accept : α → Bool) (id : Nat)
    (run : destroyHeader s accept id = some out) :
    ∃ header, s.header id = some header ∧ out = destroyed s id header := by
  unfold destroyHeader at run
  cases found : s.header id with
  | none => simp [found] at run
  | some header =>
    simp only [found,Bind.bind,Option.bind] at run
    split at run
    · exact ⟨header,rfl,(Option.some.inj run).symm⟩
    · simp at run

theorem destroyed_allocation_other (s : Heap α) (id owner : Nat) (header : Header)
    (different : header.allocation ≠ some owner) :
    (destroyed s id header).allocation owner = s.allocation owner := by
  change (retire s header.allocation).allocation owner = _
  cases allocation : header.allocation with
  | none => rfl
  | some old =>
    have ne : old ≠ owner := by intro eq; subst old; exact different allocation
    exact retire_other s old owner ne

theorem destroyed_unique (s : Heap α) (id : Nat) (header : Header)
    (found : s.header id = some header) (unique : Unique s) : Unique (destroyed s id header) := by
  intro i j hi hj owner ifound jfound iowns jowns
  have a := destroyed_header_cases s id i header hi found ifound
  have b := destroyed_header_cases s id j header hj found jfound
  exact unique i j hi hj owner a.2 b.2 iowns jowns

theorem destroyed_ownsAll (s : Heap α) (id : Nat) (header : Header)
    (found : s.header id = some header) (covered : OwnsAll s) : OwnsAll (destroyed s id header) := by
  intro owner tracked nextFound
  have previous := destroyed_sub s id header owner tracked nextFound
  obtain ⟨other,actual,actualFound,owns⟩ := covered owner tracked previous
  have different : id ≠ other := by
    intro same
    subst other
    have sameHeader := Option.some.inj (found.symm.trans actualFound)
    subst actual
    have gone : (destroyed s id header).allocation owner = none := by
      change (retire s header.allocation).allocation owner = none
      rw [owns,retire_missing]
    rw [gone] at nextFound
    contradiction
  exact ⟨other,actual,(destroyed_other s id other header different).trans actualFound,owns⟩

theorem destroyed_headersLive (s : Heap α) (id : Nat) (header : Header)
    (found : s.header id = some header) (unique : Unique s) (live : Proofs.CppMoveSpace.HeadersLive s) :
    Proofs.CppMoveSpace.HeadersLive (destroyed s id header) := by
  intro other actual owner actualFound owns
  have previous := destroyed_header_cases s id other header actual found actualFound
  have different : header.allocation ≠ some owner := by
    intro sameOwner
    exact previous.1 (unique id other header actual owner found previous.2 sameOwner owns)
  rw [destroyed_allocation_other s id owner header different]
  exact live other actual owner previous.2 owns

theorem destroyed_read_target (s : Heap α) (id owner reference : Nat) (header : Header)
    (accept : α → Bool) (grant : Grant) (owned : header.allocation = some owner)
    (found : s.grants[reference]? = some grant) (refOwner : grant.reference.element.owner = owner) :
    Proofs.CppMoveHeaders.read (destroyed s id header) accept reference = none := by
  change Proofs.CppMoveHeaders.read (retire s header.allocation) accept reference = none
  rw [owned]
  exact retire_read_target s owner accept reference grant found refOwner

theorem destroyed_read_other (s : Heap α) (id reference : Nat) (header : Header)
    (accept : α → Bool) (grant : Grant) (found : s.grants[reference]? = some grant)
    (different : header.allocation ≠ some grant.reference.element.owner) :
    Proofs.CppMoveHeaders.read (destroyed s id header) accept reference = Proofs.CppMoveHeaders.read s accept reference := by
  change Proofs.CppMoveHeaders.read (retire s header.allocation) accept reference = _
  cases allocation : header.allocation with
  | none => rfl
  | some owner =>
    have ne : owner ≠ grant.reference.element.owner := by intro eq; subst owner; exact different allocation
    exact retire_read_other s owner accept reference grant found ne


theorem destroyed_lengths (s : Heap α) (id : Nat) (header : Header) :
    (destroyed s id header).headers.length = s.headers.length ∧
      (destroyed s id header).allocations.length = s.allocations.length := by
  cases allocation : header.allocation <;> simp [destroyed,retire,allocation,List.length_set]

theorem header_count_erase (xs : List (Option Header)) (id : Nat) (header : Header)
    (found : xs[id]? = some (some header)) : (xs.set id none).countP (·.isSome)+1 = xs.countP (·.isSome) := by
  induction xs generalizing id with
  | nil => simp at found
  | cons entry tail ih =>
    cases id with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst entry
      simp
    | succ id =>
      simp only [List.getElem?_cons_succ] at found
      have previous := ih id found
      cases entry <;> simp_all

theorem destroyed_space (s : Heap α) (id : Nat) (header : Header) (found : s.header id = some header) :
    (destroyed s id header).liveSpace+oldCapacity s header+1 = s.liveSpace := by
  have count := header_count_erase s.headers id header (header_lookup s id header found)
  have released := retire_space s header
  have erased : (destroyed s id header).liveSpace+1 = (retire s header.allocation).liveSpace := by
    change (s.headers.set id none).countP (·.isSome) +
      ((retire s header.allocation).allocations.map capacity).sum+1 =
      (retire s header.allocation).headers.countP (·.isSome)+((retire s header.allocation).allocations.map capacity).sum
    rw [retire_headers]
    omega
  omega

theorem destroyed_resources (s : Heap α) (id : Nat) (header : Header) :
    (destroyed s id header).work = s.work+oldLength s header+1 ∧
      (destroyed s id header).peak = max s.peak (s.liveSpace-s.baseSpace) ∧
      (destroyed s id header).baseSpace = s.baseSpace := by
  exact ⟨rfl,rfl,retire_base s header.allocation⟩

def HeaderSub (s out : Heap α) : Prop := ∀ id header, out.header id = some header → s.header id = some header

theorem destroyed_header_sub (s : Heap α) (id : Nat) (header : Header) (found : s.header id = some header) :
    HeaderSub s (destroyed s id header) := by
  intro other actual actualFound
  exact (destroyed_header_cases s id other header actual found actualFound).2

theorem destroyAtScope_success (s out : Heap α) (accept : α → Bool) (scope id : Nat)
    (run : destroyAtScope s accept scope id = some out) :
    out = s ∨ ∃ header, s.header id = some header ∧ header.scope = scope ∧ out = destroyed s id header := by
  unfold destroyAtScope at run
  cases found : s.header id with
  | none => simp only [found,Option.some.injEq] at run; exact Or.inl run.symm
  | some header =>
    by_cases same : header.scope = scope
    · simp only [found,same,ite_true] at run
      obtain ⟨actual,actualFound,eq⟩ := destroyHeader_success s out accept id run
      have headerEq := Option.some.inj (found.symm.trans actualFound)
      subst actual
      exact Or.inr ⟨header,rfl,same,eq⟩
    · simp only [found,same,ite_false,Option.some.injEq] at run
      exact Or.inl run.symm

theorem destroyAtScope_effects (s out : Heap α) (accept : α → Bool) (scope id : Nat)
    (run : destroyAtScope s accept scope id = some out) :
    AllocationSub s out ∧ HeaderSub s out ∧ out.grants = s.grants ∧
      out.headers.length = s.headers.length ∧ out.allocations.length = s.allocations.length := by
  rcases destroyAtScope_success s out accept scope id run with eq | ⟨header,found,_,eq⟩
  · subst out
    exact ⟨fun _ _ h => h,fun _ _ h => h,rfl,rfl,rfl⟩
  · subst out
    have lengths := destroyed_lengths s id header
    exact ⟨destroyed_sub s id header,destroyed_header_sub s id header found,destroyed_grants s id header,lengths.1,lengths.2⟩

theorem destroyList_effects (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) :
    AllocationSub s out ∧ HeaderSub s out ∧ out.grants = s.grants ∧
      out.headers.length = s.headers.length ∧ out.allocations.length = s.allocations.length := by
  induction ids generalizing s with
  | nil =>
    have eq := Option.some.inj run
    subst out
    exact ⟨fun _ _ h => h,fun _ _ h => h,rfl,rfl,rfl⟩
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have a := destroyAtScope_effects s next accept scope id first
    have b := ih next rest
    exact ⟨fun owner tracked h => a.1 owner tracked (b.1 owner tracked h),
      fun headerId header h => a.2.1 headerId header (b.2.1 headerId header h),
      b.2.2.1.trans a.2.2.1,b.2.2.2.1.trans a.2.2.2.1,b.2.2.2.2.trans a.2.2.2.2⟩

theorem destroyScope_no_resurrection (s out : Heap α) (accept : α → Bool) (scope reference : Nat)
    (run : destroyScope s accept scope = some out) (old : Proofs.CppMoveHeaders.read s accept reference = none) :
    Proofs.CppMoveHeaders.read out accept reference = none := by
  have effects := destroyList_effects s out accept scope (scopeOrder s) run
  exact sub_read_none s out accept reference effects.2.2.1 effects.1 old


def ReadableHeaders (s : Heap α) (accept : α → Bool) : Prop :=
  ∀ id header, s.header id = some header → readable s header accept = true

theorem destroyed_readable (s : Heap α) (accept : α → Bool) (id : Nat) (header : Header)
    (found : s.header id = some header) (unique : Unique s) (valid : ReadableHeaders s accept) :
    ReadableHeaders (destroyed s id header) accept := by
  intro other actual actualFound
  have previous := destroyed_header_cases s id other header actual found actualFound
  have readable := valid other actual previous.2
  cases owns : actual.allocation with
  | none => simp [Proofs.CppMoveHeaders.readable,owns]
  | some owner =>
    have different : header.allocation ≠ some owner := by
      intro sameOwner
      exact previous.1 (unique id other header actual owner found previous.2 sameOwner owns)
    simp only [Proofs.CppMoveHeaders.readable,owns,destroyed_allocation_other s id owner header different]
    simpa [Proofs.CppMoveHeaders.readable,owns] using readable

theorem destroyAtScope_ready (s : Heap α) (accept : α → Bool) (scope id : Nat)
    (unique : Unique s) (valid : ReadableHeaders s accept) :
    ∃ out, destroyAtScope s accept scope id = some out ∧ Unique out ∧ ReadableHeaders out accept := by
  cases found : s.header id with
  | none => exact ⟨s,by simp [destroyAtScope,found],unique,valid⟩
  | some header =>
    by_cases same : header.scope = scope
    · have run := destroyHeader_runs s accept id header found (valid id header found)
      exact ⟨destroyed s id header,by simp [destroyAtScope,found,same,run],
        destroyed_unique s id header found unique,destroyed_readable s accept id header found unique valid⟩
    · exact ⟨s,by simp [destroyAtScope,found,same],unique,valid⟩

theorem destroyList_ready (s : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (unique : Unique s) (valid : ReadableHeaders s accept) :
    ∃ out, destroyList s accept scope ids = some out ∧ Unique out ∧ ReadableHeaders out accept := by
  induction ids generalizing s with
  | nil => exact ⟨s,rfl,unique,valid⟩
  | cons id tail ih =>
    obtain ⟨next,first,nextUnique,nextValid⟩ := destroyAtScope_ready s accept scope id unique valid
    obtain ⟨out,rest,outUnique,outValid⟩ := ih next nextUnique nextValid
    exact ⟨out,by simp [destroyList,first,rest],outUnique,outValid⟩

theorem destroyScope_ready (s : Heap α) (accept : α → Bool) (scope : Nat)
    (unique : Unique s) (valid : ReadableHeaders s accept) :
    ∃ out, destroyScope s accept scope = some out ∧ Unique out ∧ ReadableHeaders out accept :=
  destroyList_ready s accept scope (scopeOrder s) unique valid

theorem destroyAtScope_closed (s out : Heap α) (accept : α → Bool) (scope id : Nat)
    (run : destroyAtScope s accept scope id = some out) (header : Header)
    (found : out.header id = some header) : header.scope ≠ scope := by
  cases previous : s.header id with
  | none =>
    simp only [destroyAtScope,previous,Option.some.injEq] at run
    subst out
    rw [previous] at found
    contradiction
  | some actual =>
    by_cases same : actual.scope = scope
    · have destroyedRun : destroyHeader s accept id = some out := by simpa [destroyAtScope,previous,same] using run
      obtain ⟨h,hf,eq⟩ := destroyHeader_success s out accept id destroyedRun
      subst out
      rw [destroyed_header s id h hf] at found
      contradiction
    · simp only [destroyAtScope,previous,same,ite_false,Option.some.injEq] at run
      subst out
      have eq := Option.some.inj (previous.symm.trans found)
      subst header
      exact same

theorem destroyList_closed (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) :
    ∀ id ∈ ids, ∀ header, out.header id = some header → header.scope ≠ scope := by
  induction ids generalizing s with
  | nil => simp
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have effects := destroyList_effects next out accept scope tail rest
    intro other member header found
    rcases List.mem_cons.mp member with same | member
    · subst other
      exact destroyAtScope_closed s next accept scope id first header (effects.2.1 id header found)
    · exact ih next rest other member header found

theorem destroyScope_closed (s out : Heap α) (accept : α → Bool) (scope : Nat)
    (run : destroyScope s accept scope = some out) :
    ∀ id header, out.header id = some header → header.scope ≠ scope := by
  have effects := destroyList_effects s out accept scope (scopeOrder s) run
  intro id header found
  have inside := source_inside out id header found
  rw [effects.2.2.2.1] at inside
  exact destroyList_closed s out accept scope (scopeOrder s) run id ((scopeOrder_mem s id).mpr inside) header found

theorem destroyScope_all (s out : Heap α) (accept : α → Bool) (scope : Nat)
    (run : destroyScope s accept scope = some out) :
    (out.headers.all fun entry => match entry with | none => true | some header => header.scope != scope) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  cases entry with
  | none => rfl
  | some header =>
    obtain ⟨id,slot⟩ := List.mem_iff_getElem?.mp member
    have found : out.header id = some header := by simp [Heap.header,slot]
    have different := destroyScope_closed s out accept scope run id header found
    simpa using different



-- These invariants hold for every successful run, including lists with duplicate IDs.
theorem destroyList_ownsAll (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) (covered : OwnsAll s) : OwnsAll out := by
  induction ids generalizing s with
  | nil => cases Option.some.inj run; exact covered
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    apply ih next rest
    rcases destroyAtScope_success s next accept scope id first with eq | ⟨header,found,_,eq⟩
    · subst next; exact covered
    · subst next; exact destroyed_ownsAll s id header found covered

theorem destroyList_allocationsValid (s out : Heap Int) (accept : Int → Bool)
    (ty : Proofs.CppScalar.Ty) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out)
    (valid : Proofs.CppMoveFrame.AllocationsValid s ty) : Proofs.CppMoveFrame.AllocationsValid out ty := by
  have sub := (destroyList_effects s out accept scope ids run).1
  intro owner tracked found
  exact valid owner tracked (sub owner tracked found)

theorem destroyList_grantBounds (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) (bounds : Proofs.CppMoveWrite.GrantBounds s) :
    Proofs.CppMoveWrite.GrantBounds out := by
  have effects := destroyList_effects s out accept scope ids run
  exact Proofs.CppMoveWrite.grantBounds_metadata s out bounds effects.2.2.1 effects.2.2.2.2

-- No allocation occurs. Historical peaks remain observable, and the baseline is fixed.
theorem destroyAtScope_resources (s out : Heap α) (accept : α → Bool) (scope id : Nat)
    (run : destroyAtScope s accept scope id = some out) :
    out.liveSpace ≤ s.liveSpace ∧ out.baseSpace = s.baseSpace ∧ s.work ≤ out.work ∧
      s.peak ≤ out.peak ∧ out.peak ≤ max s.peak (s.liveSpace-s.baseSpace) := by
  rcases destroyAtScope_success s out accept scope id run with eq | ⟨header,found,_,eq⟩
  · subst out; exact ⟨le_refl _,rfl,le_refl _,le_refl _,Nat.le_max_left _ _⟩
  · subst out
    have space := destroyed_space s id header found
    have resources := destroyed_resources s id header
    exact ⟨by omega,resources.2.2,by omega,by omega,by omega⟩

theorem destroyList_resources (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) :
    out.liveSpace ≤ s.liveSpace ∧ out.baseSpace = s.baseSpace ∧ s.work ≤ out.work ∧
      s.peak ≤ out.peak ∧ out.peak ≤ max s.peak (s.liveSpace-s.baseSpace) := by
  induction ids generalizing s with
  | nil =>
    cases Option.some.inj run
    exact ⟨le_refl _,rfl,le_refl _,le_refl _,Nat.le_max_left _ _⟩
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have a := destroyAtScope_resources s next accept scope id first
    have b := ih next rest
    refine ⟨by omega,b.2.1.trans a.2.1,by omega,by omega,?_⟩
    have live : next.liveSpace-next.baseSpace ≤ s.liveSpace-s.baseSpace := by omega
    exact b.2.2.2.2.trans (max_le a.2.2.2.2 (live.trans (Nat.le_max_right _ _)))



def scopeCost (s : Heap α) (scope id : Nat) : Nat :=
  match s.header id with
  | none => 0
  | some header => if header.scope = scope then oldLength s header+1 else 0

def scopeBudget (s : Heap α) (scope : Nat) : List Nat → Nat
  | [] => 0
  | id::tail => scopeCost s scope id + scopeBudget s scope tail

theorem oldLength_sub (s out : Heap α) (header : Header) (sub : AllocationSub s out) :
    oldLength out header ≤ oldLength s header := by
  cases owns : header.allocation with
  | none => simp [oldLength,owns]
  | some owner =>
    cases found : out.allocation owner with
    | none => simp [oldLength,owns,found]
    | some tracked => simp [oldLength,owns,found,sub owner tracked found]

theorem scopeCost_sub (s out : Heap α) (scope id : Nat)
    (allocations : AllocationSub s out) (headers : HeaderSub s out) :
    scopeCost out scope id ≤ scopeCost s scope id := by
  cases found : out.header id with
  | none => simp [scopeCost,found]
  | some header =>
    have previous := headers id header found
    have lengths := oldLength_sub s out header allocations
    by_cases same : header.scope = scope
    · simp only [scopeCost,found,previous,same,ite_true]
      omega
    · simp [scopeCost,found,previous,same]

theorem scopeBudget_sub (s out : Heap α) (scope : Nat) (ids : List Nat)
    (allocations : AllocationSub s out) (headers : HeaderSub s out) :
    scopeBudget out scope ids ≤ scopeBudget s scope ids := by
  induction ids with
  | nil => exact le_refl _
  | cons id tail ih =>
    have cost := scopeCost_sub s out scope id allocations headers
    simp only [scopeBudget]
    omega

theorem destroyAtScope_work (s out : Heap α) (accept : α → Bool) (scope id : Nat)
    (run : destroyAtScope s accept scope id = some out) :
    out.work ≤ s.work+scopeCost s scope id := by
  rcases destroyAtScope_success s out accept scope id run with eq | ⟨header,found,same,eq⟩
  · subst out; omega
  · subst out
    have work := (destroyed_resources s id header).1
    simp only [scopeCost,found,same,ite_true]
    omega

-- Duplicate IDs can only overestimate the cost; tombstones contribute zero.
theorem destroyList_work (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (run : destroyList s accept scope ids = some out) :
    out.work ≤ s.work+scopeBudget s scope ids := by
  induction ids generalizing s with
  | nil => cases Option.some.inj run; exact le_refl _
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have a := destroyAtScope_work s next accept scope id first
    have b := ih next rest
    have effects := destroyAtScope_effects s next accept scope id first
    have remaining := scopeBudget_sub s next scope tail effects.1 effects.2.1
    simp only [scopeBudget]
    omega

theorem destroyScope_work (s out : Heap α) (accept : α → Bool) (scope : Nat)
    (run : destroyScope s accept scope = some out) :
    out.work ≤ s.work+scopeBudget s scope (scopeOrder s) :=
  destroyList_work s out accept scope (scopeOrder s) run



theorem destroyScope_invariants (s out : Heap Int) (ty : Proofs.CppScalar.Ty) (scope : Nat)
    (run : destroyScope s ty.valid scope = some out)
    (unique : Unique s) (readable : ReadableHeaders s ty.valid) (covered : OwnsAll s)
    (valid : Proofs.CppMoveFrame.AllocationsValid s ty) (bounds : Proofs.CppMoveWrite.GrantBounds s) :
    Unique out ∧ ReadableHeaders out ty.valid ∧ OwnsAll out ∧
      Proofs.CppMoveFrame.AllocationsValid out ty ∧ Proofs.CppMoveWrite.GrantBounds out ∧
      Proofs.CppMoveSpace.HeadersLive out := by
  obtain ⟨actual,actualRun,actualUnique,actualReadable⟩ := destroyScope_ready s ty.valid scope unique readable
  have same := Option.some.inj (actualRun.symm.trans run)
  subst actual
  exact ⟨actualUnique,actualReadable,
    destroyList_ownsAll s out ty.valid scope (scopeOrder s) run covered,
    destroyList_allocationsValid s out ty.valid ty scope (scopeOrder s) run valid,
    destroyList_grantBounds s out ty.valid scope (scopeOrder s) run bounds,
    Proofs.CppMoveSpace.headersLive_of_readable out ty.valid actualReadable⟩


def finishScope (caller callee : Proofs.CppMoveContext.Context) (ty : Proofs.CppScalar.Ty) :
    Option Proofs.CppMoveContext.Context := do
  let heap ← destroyScope callee.objects.heap ty.valid callee.scope
  let next := Proofs.CppMoveContext.observe {callee with objects := {callee.objects with heap := heap}}
  Proofs.CppMoveContext.finishBorrowed caller next

theorem finishScope_ready (caller callee : Proofs.CppMoveContext.Context) (ty : Proofs.CppScalar.Ty)
    (scope : callee.scope = caller.scope+1)
    (views : callee.objects.views.take caller.objects.views.length = caller.objects.views)
    (grants : callee.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (unique : Unique callee.objects.heap) (valid : ReadableHeaders callee.objects.heap ty.valid) :
    ∃ out, finishScope caller callee ty = some out := by
  obtain ⟨heap,run,_,_⟩ := destroyScope_ready callee.objects.heap ty.valid callee.scope unique valid
  have effects := destroyList_effects callee.objects.heap heap ty.valid callee.scope (scopeOrder callee.objects.heap) run
  have closed := destroyScope_all callee.objects.heap heap ty.valid callee.scope run
  let next := Proofs.CppMoveContext.observe {callee with objects := {callee.objects with heap := heap}}
  have nextGrants : next.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants := by
    change heap.grants.take caller.objects.heap.grants.length = _
    rw [effects.2.2.1]
    exact grants
  have finished : ∃ out, Proofs.CppMoveContext.finishBorrowed caller next = some out := by
    unfold Proofs.CppMoveContext.finishBorrowed
    rw [ite_eq_left ⟨scope,views,nextGrants,fits,types,closed⟩]
    exact ⟨_,rfl⟩
  obtain ⟨out,finish⟩ := finished
  exact ⟨out,by simp [finishScope,run,next,finish]⟩

end Proofs.CppMoveDestroy
