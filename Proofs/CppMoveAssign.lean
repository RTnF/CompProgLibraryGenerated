import Proofs.CppMoveHeaders

namespace Proofs.CppMoveAssign
open Proofs.CppVector Proofs.CppMoveHeaders

-- Retirement removes an allocation identity permanently from this table.
-- Neither captured grants nor the header IDs of vector objects are rewritten.
def retire (s : Heap α) (allocation : Option Nat) : Heap α :=
  match allocation with
  | none => s
  | some owner => {s with allocations := s.allocations.set owner none}

def oldLength (s : Heap α) (header : Header) : Nat :=
  match header.allocation with
  | none => 0
  | some owner => ((s.allocation owner).map (fun t => t.buffer.items.length)).getD 0

def assigned (s : Heap α) (target source : Nat) (th sh : Header) : Heap α :=
  let freed := retire s th.allocation
  let headers := if target = source then s.headers.set target (some {th with allocation := none})
    else (s.headers.set source (some {sh with allocation := none})).set target (some {th with allocation := sh.allocation})
  {freed with
    headers := headers
    work := s.work+oldLength s th+1
    peak := max s.peak (s.liveSpace+1-s.baseSpace)}

def compatible (target source : Nat) (th sh : Header) : Bool :=
  decide (target = source ∨ th.allocation = none ∨ sh.allocation = none ∨ th.allocation ≠ sh.allocation)

def moveAssign (s : Heap α) (accept : α → Bool) (target source : Nat) : Option (Heap α) := do
  let th ← s.header target
  let sh ← s.header source
  if th.writable ∧ sh.writable ∧ readable s th accept ∧ readable s sh accept ∧
      th.limit = sh.limit ∧ compatible target source th sh then
    some (assigned s target source th sh)
  else none

-- Move operations can prune live allocations; they cannot restore old ones.
def AllocationSub (s out : Heap α) : Prop :=
  ∀ owner tracked, out.allocation owner = some tracked → s.allocation owner = some tracked

theorem retire_grants (s : Heap α) (allocation : Option Nat) : (retire s allocation).grants = s.grants := by
  cases allocation <;> rfl

theorem retire_headers (s : Heap α) (allocation : Option Nat) : (retire s allocation).headers = s.headers := by
  cases allocation <;> rfl

theorem retire_base (s : Heap α) (allocation : Option Nat) : (retire s allocation).baseSpace = s.baseSpace := by
  cases allocation <;> rfl

theorem allocation_inside (s : Heap α) (owner : Nat) (tracked : Proofs.CppVectorCopyAssign.Tracked α)
    (found : s.allocation owner = some tracked) : owner < s.allocations.length := by
  unfold Heap.allocation at found
  cases actual : s.allocations[owner]? with
  | none => simp [actual] at found
  | some value => exact (List.getElem?_eq_some_iff.mp actual).1

theorem retire_same (s : Heap α) (owner : Nat) (tracked : Proofs.CppVectorCopyAssign.Tracked α)
    (found : s.allocation owner = some tracked) : (retire s (some owner)).allocation owner = none := by
  have inside := allocation_inside s owner tracked found
  simp [retire,Heap.allocation,List.getElem?_set_self inside]

theorem retire_other (s : Heap α) (owner other : Nat) (different : owner ≠ other) :
    (retire s (some owner)).allocation other = s.allocation other := by
  simp only [retire,Heap.allocation,List.getElem?_set_ne different]


theorem retire_missing (s : Heap α) (owner : Nat) : (retire s (some owner)).allocation owner = none := by
  unfold retire Heap.allocation
  rw [List.getElem?_set]
  by_cases inside : owner < s.allocations.length <;> simp [inside]

theorem retire_sub (s : Heap α) (allocation : Option Nat) : AllocationSub s (retire s allocation) := by
  cases allocation with
  | none => intro owner tracked found; exact found
  | some erased =>
    intro owner tracked found
    by_cases same : erased = owner
    · subst owner
      rw [retire_missing] at found
      contradiction
    · rw [retire_other s erased owner same] at found
      exact found

theorem assigned_grants (s : Heap α) (target source : Nat) (th sh : Header) :
    (assigned s target source th sh).grants = s.grants := by
  change (retire s th.allocation).grants = s.grants
  exact retire_grants s th.allocation

theorem assigned_sub (s : Heap α) (target source : Nat) (th sh : Header) : AllocationSub s (assigned s target source th sh) := by
  intro owner tracked found
  exact retire_sub s th.allocation owner tracked found

theorem sub_read_none (s out : Heap α) (accept : α → Bool) (reference : Nat)
    (grants : out.grants = s.grants) (sub : AllocationSub s out)
    (old : Proofs.CppMoveHeaders.read s accept reference = none) :
    Proofs.CppMoveHeaders.read out accept reference = none := by
  unfold Proofs.CppMoveHeaders.read at old ⊢
  rw [grants]
  cases grantFound : s.grants[reference]? with
  | none => rfl
  | some grant =>
    simp only [grantFound,Bind.bind,Option.bind] at old ⊢
    cases found : out.allocation grant.reference.element.owner with
    | none => rfl
    | some tracked =>
      have previous := sub grant.reference.element.owner tracked found
      rw [previous] at old
      exact old

theorem assigned_no_resurrection (s : Heap α) (target source : Nat) (th sh : Header)
    (accept : α → Bool) (reference : Nat) (old : Proofs.CppMoveHeaders.read s accept reference = none) :
    Proofs.CppMoveHeaders.read (assigned s target source th sh) accept reference = none :=
  sub_read_none s _ accept reference (assigned_grants s target source th sh) (assigned_sub s target source th sh) old

theorem move_assign_success (s out : Heap α) (accept : α → Bool) (target source : Nat)
    (ran : moveAssign s accept target source = some out) :
    ∃ th sh, s.header target = some th ∧ s.header source = some sh ∧ out = assigned s target source th sh := by
  unfold moveAssign at ran
  cases tf : s.header target with
  | none => simp [tf] at ran
  | some th =>
    cases sf : s.header source with
    | none => simp [tf,sf] at ran
    | some sh =>
      simp only [tf,sf,Bind.bind,Option.bind] at ran
      split at ran
      · exact ⟨th,sh,rfl,rfl,(Option.some.inj ran).symm⟩
      · simp at ran

theorem move_assign_no_resurrection (s out : Heap α) (accept : α → Bool) (target source : Nat)
    (ran : moveAssign s accept target source = some out) (reference : Nat)
    (old : Proofs.CppMoveHeaders.read s accept reference = none) : Proofs.CppMoveHeaders.read out accept reference = none := by
  obtain ⟨th,sh,_,_,same⟩ := move_assign_success s out accept target source ran
  rw [same]
  exact assigned_no_resurrection s target source th sh accept reference old


theorem retire_read_target (s : Heap α) (owner : Nat) (accept : α → Bool) (reference : Nat) (grant : Grant)
    (found : s.grants[reference]? = some grant) (owns : grant.reference.element.owner = owner) :
    Proofs.CppMoveHeaders.read (retire s (some owner)) accept reference = none := by
  unfold Proofs.CppMoveHeaders.read
  rw [retire_grants,found]
  simp only [Bind.bind,Option.bind]
  rw [owns,retire_missing]

theorem retire_read_other (s : Heap α) (owner : Nat) (accept : α → Bool) (reference : Nat) (grant : Grant)
    (found : s.grants[reference]? = some grant) (different : owner ≠ grant.reference.element.owner) :
    Proofs.CppMoveHeaders.read (retire s (some owner)) accept reference = Proofs.CppMoveHeaders.read s accept reference := by
  unfold Proofs.CppMoveHeaders.read
  rw [retire_grants,found]
  simp only [Bind.bind,Option.bind]
  rw [retire_other s owner grant.reference.element.owner different]

theorem assigned_target_retired (s : Heap α) (target source owner : Nat) (th sh : Header)
    (accept : α → Bool) (reference : Nat) (grant : Grant) (targetOwner : th.allocation = some owner)
    (found : s.grants[reference]? = some grant) (owns : grant.reference.element.owner = owner) :
    Proofs.CppMoveHeaders.read (assigned s target source th sh) accept reference = none := by
  change Proofs.CppMoveHeaders.read (retire s th.allocation) accept reference = none
  rw [targetOwner]
  exact retire_read_target s owner accept reference grant found owns

theorem assigned_read_other (s : Heap α) (target source : Nat) (th sh : Header)
    (accept : α → Bool) (reference : Nat) (grant : Grant) (found : s.grants[reference]? = some grant)
    (different : ∀ owner, th.allocation = some owner → owner ≠ grant.reference.element.owner) :
    Proofs.CppMoveHeaders.read (assigned s target source th sh) accept reference = Proofs.CppMoveHeaders.read s accept reference := by
  change Proofs.CppMoveHeaders.read (retire s th.allocation) accept reference = Proofs.CppMoveHeaders.read s accept reference
  cases owned : th.allocation with
  | none => rfl
  | some owner => exact retire_read_other s owner accept reference grant found (different owner owned)

-- This trace only contains move construction/assignment. Broader mixed traces,
-- allocation creation, capture and in-place scalar writes need their adapters.
inductive Moves (accept : α → Bool) : Heap α → Heap α → Prop
  | refl (s : Heap α) : Moves accept s s
  | construct (s next out : Heap α) (source scope destination : Nat) (writable : Bool)
      (ran : moveConstruct s accept source scope writable = some (next,destination))
      (tail : Moves accept next out) : Moves accept s out
  | assign (s next out : Heap α) (target source : Nat)
      (ran : moveAssign s accept target source = some next) (tail : Moves accept next out) : Moves accept s out

theorem Moves.no_resurrection {accept : α → Bool} {s out : Heap α} (runs : Moves accept s out)
    (reference : Nat) (old : Proofs.CppMoveHeaders.read s accept reference = none) :
    Proofs.CppMoveHeaders.read out accept reference = none := by
  induction runs with
  | refl s => exact old
  | construct s next out source scope destination writable ran tail ih =>
    apply ih
    rw [move_construct_read s next accept source scope destination writable ran reference]
    exact old
  | assign s next out target source ran tail ih =>
    exact ih (move_assign_no_resurrection s next accept target source ran reference old)


theorem compatible_of_unique (s : Heap α) (target source : Nat) (th sh : Header)
    (unique : Unique s) (tf : s.header target = some th) (sf : s.header source = some sh) :
    compatible target source th sh = true := by
  simp only [compatible,decide_eq_true_eq]
  by_cases same : target = source
  · exact Or.inl same
  · cases targetOwner : th.allocation with
    | none => exact Or.inr (Or.inl rfl)
    | some a =>
      cases sourceOwner : sh.allocation with
      | none => exact Or.inr (Or.inr (Or.inl rfl))
      | some b =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        intro equal
        have ab := Option.some.inj equal
        subst b
        exact same (unique target source th sh a tf sf targetOwner sourceOwner)

theorem move_assign_runs (s : Heap α) (accept : α → Bool) (target source : Nat) (th sh : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh)
    (tw : th.writable = true) (sw : sh.writable = true)
    (tv : readable s th accept = true) (sv : readable s sh accept = true)
    (limit : th.limit = sh.limit) (unique : Unique s) :
    moveAssign s accept target source = some (assigned s target source th sh) := by
  have allowed := compatible_of_unique s target source th sh unique tf sf
  simp [moveAssign,tf,sf,tw,sw,tv,sv,limit,allowed]


theorem source_separate (s : Heap α) (target source : Nat) (th sh : Header) (owner : Nat)
    (unique : Unique s) (tf : s.header target = some th) (sf : s.header source = some sh)
    (different : target ≠ source) (sourceOwner : sh.allocation = some owner) :
    ∀ erased, th.allocation = some erased → erased ≠ owner := by
  intro erased targetOwner equal
  subst erased
  exact different (unique target source th sh owner tf sf targetOwner sourceOwner)

theorem assigned_source_read (s : Heap α) (target source : Nat) (th sh : Header)
    (accept : α → Bool) (reference : Nat) (grant : Grant)
    (unique : Unique s) (tf : s.header target = some th) (sf : s.header source = some sh)
    (different : target ≠ source) (found : s.grants[reference]? = some grant)
    (owns : sh.allocation = some grant.reference.element.owner) :
    Proofs.CppMoveHeaders.read (assigned s target source th sh) accept reference = Proofs.CppMoveHeaders.read s accept reference :=
  assigned_read_other s target source th sh accept reference grant found
    (source_separate s target source th sh grant.reference.element.owner unique tf sf different owns)


theorem assigned_target (s : Heap α) (target source : Nat) (th sh : Header)
    (found : s.header target = some th) :
    (assigned s target source th sh).header target =
      some {th with allocation := if target = source then none else sh.allocation} := by
  have inside := source_inside s target th found
  by_cases same : target = source
  · subst source
    simp [assigned,Heap.header,inside]
  · simp [assigned,Heap.header,same,inside]

theorem assigned_source (s : Heap α) (target source : Nat) (th sh : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh) :
    (assigned s target source th sh).header source = some {sh with allocation := none} := by
  by_cases same : target = source
  · have equal := Option.some.inj (tf.symm.trans ((congrArg s.header same).trans sf))
    subst sh
    rw [← same]
    simpa using assigned_target s target target th th tf
  · have inside := source_inside s source sh sf
    simp [assigned,Heap.header,same,inside]

theorem assigned_other_header (s : Heap α) (target source other : Nat) (th sh : Header)
    (targetDifferent : target ≠ other) (sourceDifferent : source ≠ other) :
    (assigned s target source th sh).header other = s.header other := by
  simp only [assigned,Heap.header]
  split <;> simp only [List.getElem?_set_ne targetDifferent,List.getElem?_set_ne sourceDifferent]

theorem assigned_header_length (s : Heap α) (target source : Nat) (th sh : Header) :
    (assigned s target source th sh).headers.length = s.headers.length := by
  simp only [assigned]
  split <;> simp


theorem assigned_owner_cases (s : Heap α) (target source i owner : Nat) (th sh hi : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh)
    (found : (assigned s target source th sh).header i = some hi) (owns : hi.allocation = some owner) :
    (i = target ∧ target ≠ source ∧ hi = {th with allocation := sh.allocation}) ∨
      (i ≠ target ∧ i ≠ source ∧ s.header i = some hi) := by
  by_cases it : i = target
  · subst i
    have same := Option.some.inj ((assigned_target s target source th sh tf).symm.trans found)
    by_cases ts : target = source
    · have empty : hi.allocation = none := by rw [← same]; simp [ts]
      rw [empty] at owns
      contradiction
    · exact Or.inl ⟨rfl,ts,by simpa [ts] using same.symm⟩
  · by_cases isource : i = source
    · subst i
      have same := Option.some.inj ((assigned_source s target source th sh tf sf).symm.trans found)
      have empty : hi.allocation = none := by rw [← same]
      rw [empty] at owns
      contradiction
    · exact Or.inr ⟨it,isource,(assigned_other_header s target source i th sh (Ne.symm it) (Ne.symm isource)).symm.trans found⟩

theorem assigned_unique (s : Heap α) (target source : Nat) (th sh : Header)
    (unique : Unique s) (tf : s.header target = some th) (sf : s.header source = some sh) :
    Unique (assigned s target source th sh) := by
  intro i j hi hj owner iFound jFound iOwns jOwns
  rcases assigned_owner_cases s target source i owner th sh hi tf sf iFound iOwns with
    ⟨iTarget,_,hiEq⟩ | ⟨_,iSource,iOld⟩
  · subst i
    subst hi
    rcases assigned_owner_cases s target source j owner th sh hj tf sf jFound jOwns with
      ⟨jTarget,_,_⟩ | ⟨_,jSource,jOld⟩
    · exact jTarget.symm
    · have same := unique source j sh hj owner sf jOld iOwns jOwns
      exact False.elim (jSource same.symm)
  · rcases assigned_owner_cases s target source j owner th sh hj tf sf jFound jOwns with
      ⟨_,_,hjEq⟩ | ⟨_,_,jOld⟩
    · rw [hjEq] at jOwns
      have same := unique i source hi sh owner iOld sf iOwns jOwns
      exact False.elim (iSource same)
    · exact unique i j hi hj owner iOld jOld iOwns jOwns

theorem move_assign_unique (s out : Heap α) (accept : α → Bool) (target source : Nat)
    (unique : Unique s) (ran : moveAssign s accept target source = some out) : Unique out := by
  obtain ⟨th,sh,tf,sf,same⟩ := move_assign_success s out accept target source ran
  rw [same]
  exact assigned_unique s target source th sh unique tf sf


theorem assigned_ownsAll (s : Heap α) (target source : Nat) (th sh : Header)
    (covered : OwnsAll s) (tf : s.header target = some th) (sf : s.header source = some sh) :
    OwnsAll (assigned s target source th sh) := by
  intro owner tracked nextFound
  have previous := assigned_sub s target source th sh owner tracked nextFound
  obtain ⟨i,hi,found,owns⟩ := covered owner tracked previous
  have notTarget : i ≠ target := by
    intro same
    subst i
    have equal := Option.some.inj (found.symm.trans tf)
    subst hi
    have gone : (assigned s target source th sh).allocation owner = none := by
      change (retire s th.allocation).allocation owner = none
      rw [owns,retire_missing]
    rw [gone] at nextFound
    contradiction
  by_cases isource : i = source
  · subst i
    have equal := Option.some.inj (found.symm.trans sf)
    subst hi
    have different : target ≠ source := Ne.symm notTarget
    refine ⟨target,{th with allocation := sh.allocation},?_,owns⟩
    simpa only [different,↓reduceIte] using assigned_target s target source th sh tf
  · exact ⟨i,hi,(assigned_other_header s target source i th sh (Ne.symm notTarget) (Ne.symm isource)).trans found,owns⟩

theorem move_assign_ownsAll (s out : Heap α) (accept : α → Bool) (target source : Nat)
    (covered : OwnsAll s) (ran : moveAssign s accept target source = some out) : OwnsAll out := by
  obtain ⟨th,sh,tf,sf,same⟩ := move_assign_success s out accept target source ran
  rw [same]
  exact assigned_ownsAll s target source th sh covered tf sf

def capacity (allocation : Option (Proofs.CppVectorCopyAssign.Tracked α)) : Nat :=
  match allocation with | none => 0 | some tracked => tracked.buffer.capacity

def oldCapacity (s : Heap α) (header : Header) : Nat :=
  match header.allocation with
  | none => 0
  | some owner => ((s.allocation owner).map (fun t => t.buffer.capacity)).getD 0

theorem capacity_sum_retire (xs : List (Option (Proofs.CppVectorCopyAssign.Tracked α))) (owner : Nat) :
    ((xs.set owner none).map capacity).sum + ((xs[owner]?).join.map (fun t => t.buffer.capacity)).getD 0 =
      (xs.map capacity).sum := by
  induction xs generalizing owner with
  | nil => simp
  | cons head tail ih =>
    cases owner with
    | zero =>
      cases head with
      | none => simp [capacity]
      | some tracked => simp [capacity,List.getElem?_cons_zero,Nat.add_comm]
    | succ owner =>
      have next := ih owner
      simpa only [List.set_cons_succ,List.map_cons,List.sum_cons,List.getElem?_cons_succ,Nat.add_assoc] using
        congrArg (fun n => capacity head+n) next


theorem header_count_replace (xs : List (Option Header)) (i : Nat) (old next : Header)
    (found : xs[i]? = some (some old)) :
    (xs.set i (some next)).countP (·.isSome) = xs.countP (·.isSome) := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have atIndex : xs[i] = some old := (List.getElem?_eq_some_iff.mp found).2
  have count : 1 ≤ xs.countP (·.isSome) := by
    have bound := List.boole_getElem_le_countP (p := fun (h : Option Header) => h.isSome) inside
    simpa only [atIndex,Option.isSome_some,↓reduceIte] using bound
  rw [List.countP_set inside]
  simp only [atIndex,Option.isSome_some,↓reduceIte]
  omega

theorem assigned_header_count (s : Heap α) (target source : Nat) (th sh : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh) :
    (assigned s target source th sh).headers.countP (·.isSome) = s.headers.countP (·.isSome) := by
  have tRaw := header_lookup s target th tf
  have sRaw := header_lookup s source sh sf
  simp only [assigned]
  split
  · exact header_count_replace s.headers target th _ tRaw
  · rename_i different
    have preserved : (s.headers.set source (some {sh with allocation := none}))[target]? = some (some th) := by
      rw [List.getElem?_set_ne (Ne.symm different)]
      exact tRaw
    rw [header_count_replace _ target th _ preserved]
    exact header_count_replace s.headers source sh _ sRaw

theorem retire_space (s : Heap α) (header : Header) :
    (retire s header.allocation).liveSpace+oldCapacity s header = s.liveSpace := by
  cases owned : header.allocation with
  | none => simp [retire,oldCapacity,owned]
  | some owner =>
    simp only [retire,oldCapacity,owned,Heap.liveSpace,Heap.allocation]
    change s.headers.countP (·.isSome) + ((s.allocations.set owner none).map capacity).sum +
      ((s.allocations[owner]?).join.map (fun t => t.buffer.capacity)).getD 0 =
        s.headers.countP (·.isSome)+(s.allocations.map capacity).sum
    simpa only [Nat.add_assoc] using congrArg (fun n => s.headers.countP (·.isSome)+n)
      (capacity_sum_retire s.allocations owner)

theorem assigned_space (s : Heap α) (target source : Nat) (th sh : Header)
    (tf : s.header target = some th) (sf : s.header source = some sh) :
    (assigned s target source th sh).liveSpace+oldCapacity s th = s.liveSpace := by
  have released := retire_space s th
  unfold Heap.liveSpace at released ⊢
  rw [assigned_header_count s target source th sh tf sf]
  rw [retire_headers] at released
  exact released

theorem assigned_resources (s : Heap α) (target source : Nat) (th sh : Header) :
    (assigned s target source th sh).work = s.work+oldLength s th+1 ∧
      (assigned s target source th sh).peak = max s.peak (s.liveSpace+1-s.baseSpace) ∧
      (assigned s target source th sh).baseSpace = s.baseSpace := by
  refine ⟨rfl,rfl,?_⟩
  change (retire s th.allocation).baseSpace = s.baseSpace
  exact retire_base s th.allocation

theorem move_assign_resources (s out : Heap α) (accept : α → Bool) (target source : Nat)
    (ran : moveAssign s accept target source = some out) :
    ∃ th, s.header target = some th ∧ out.work = s.work+oldLength s th+1 ∧
      out.liveSpace+oldCapacity s th = s.liveSpace ∧
      out.peak = max s.peak (s.liveSpace+1-s.baseSpace) ∧ out.baseSpace = s.baseSpace := by
  obtain ⟨th,sh,tf,sf,same⟩ := move_assign_success s out accept target source ran
  rw [same]
  have data := assigned_resources s target source th sh
  exact ⟨th,tf,data.1,assigned_space s target source th sh tf sf,data.2.1,data.2.2⟩

end Proofs.CppMoveAssign
