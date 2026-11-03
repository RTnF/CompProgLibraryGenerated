import Proofs.CppVectorCopy

namespace Proofs.CppVectorCopyAssign
open Proofs.CppVector

-- Lifetimes are ghost metadata. They do not represent C++ resident storage.
structure Tracked (α : Type) where
  buffer : Buffer α
  generation : Nat → Nat := fun _ => 0

structure Reference where
  element : ElementRef
  generation : Nat
  deriving DecidableEq, Repr

structure Assignment (α : Type) where
  target : Tracked α
  work : Nat
  peak : Nat

def reference (s : Tracked α) (accept : α → Bool) (index : Int) : Option Reference := do
  let element ← elementRef s.buffer accept index
  some ⟨element,s.generation index.toNat⟩

def read (s : Tracked α) (accept : α → Bool) (ref : Reference) : Option (Result α α) :=
  if ref.generation = s.generation ref.element.index then readRef s.buffer accept ref.element else none

def assigned (target source : Tracked α) : Tracked α :=
  if target.buffer.capacity < source.buffer.items.length then
    ⟨⟨target.buffer.owner,source.buffer.items,source.buffer.items.length,target.buffer.limit,target.buffer.epoch+1⟩,fun _ => 0⟩
  else
    ⟨{target.buffer with items := source.buffer.items},fun i =>
      if source.buffer.items.length ≤ i ∧ i < target.buffer.items.length then target.generation i+1
      else target.generation i⟩

-- Fixed-width scalar elements, std::allocator, successful allocation. Cost is
-- a logical upper budget including old-element retirement and new-element copy.
def copyAssign (target source : Tracked α) (accept : α → Bool) (writable : Bool) : Option (Assignment α) :=
  if target.buffer.Valid accept ∧ source.buffer.Valid accept ∧ writable = true ∧
      source.buffer.items.length ≤ target.buffer.limit then
    if target.buffer.owner = source.buffer.owner then
      some ⟨target,1,target.buffer.capacity+1⟩
    else
      some ⟨assigned target source,target.buffer.items.length+source.buffer.items.length+1,
        if target.buffer.capacity < source.buffer.items.length then
          target.buffer.capacity+source.buffer.items.length+2 else target.buffer.capacity+2⟩
  else none

theorem assigned_valid (target source : Tracked α) (accept : α → Bool)
    (targetValid : target.buffer.Valid accept) (sourceValid : source.buffer.Valid accept)
    (bound : source.buffer.items.length ≤ target.buffer.limit) :
    (assigned target source).buffer.Valid accept := by
  unfold assigned
  split
  · exact ⟨Nat.le_refl _,bound,sourceValid.2.2⟩
  · rename_i noGrowth
    exact ⟨by dsimp; omega,targetValid.2.1,sourceValid.2.2⟩

theorem copy_runs (target source : Tracked α) (accept : α → Bool)
    (targetValid : target.buffer.Valid accept) (sourceValid : source.buffer.Valid accept)
    (bound : source.buffer.items.length ≤ target.buffer.limit) (different : target.buffer.owner ≠ source.buffer.owner) :
    copyAssign target source accept true = some ⟨assigned target source,
      target.buffer.items.length+source.buffer.items.length+1,
      if target.buffer.capacity < source.buffer.items.length then
        target.buffer.capacity+source.buffer.items.length+2 else target.buffer.capacity+2⟩ := by
  simp [copyAssign,targetValid,sourceValid,bound,different]

theorem self_runs (target : Tracked α) (accept : α → Bool) (valid : target.buffer.Valid accept) :
    copyAssign target target accept true = some ⟨target,1,target.buffer.capacity+1⟩ := by
  have bound := Nat.le_trans valid.1 valid.2.1
  simp [copyAssign,valid,bound]

theorem readonly (target source : Tracked α) (accept : α → Bool) :
    copyAssign target source accept false = none := by simp [copyAssign]

theorem assigned_owner (target source : Tracked α) :
    (assigned target source).buffer.owner = target.buffer.owner := by unfold assigned; split <;> rfl

theorem assigned_items (target source : Tracked α) :
    (assigned target source).buffer.items = source.buffer.items := by unfold assigned; split <;> rfl

theorem assigned_capacity (target source : Tracked α) :
    (assigned target source).buffer.capacity = max target.buffer.capacity source.buffer.items.length := by
  unfold assigned
  split
  · rename_i grow; exact (Nat.max_eq_right (Nat.le_of_lt grow)).symm
  · rename_i keep
    change target.buffer.capacity = max target.buffer.capacity source.buffer.items.length
    exact (Nat.max_eq_left (by omega)).symm

theorem prefix_generation (target source : Tracked α) (index : Nat)
    (keep : source.buffer.items.length ≤ target.buffer.capacity) (inside : index < source.buffer.items.length) :
    (assigned target source).generation index = target.generation index := by
  have noGrow : ¬ target.buffer.capacity < source.buffer.items.length := by omega
  have notErased : ¬ (source.buffer.items.length ≤ index ∧ index < target.buffer.items.length) := by omega
  simp [assigned,noGrow,notErased]

theorem prefix_read (target source : Tracked α) (accept : α → Bool) (index : Nat) (value : α)
    (targetValid : target.buffer.Valid accept) (sourceValid : source.buffer.Valid accept)
    (keep : source.buffer.items.length ≤ target.buffer.capacity) (found : source.buffer.items[index]? = some value) :
    read (assigned target source) accept ⟨⟨target.buffer.owner,target.buffer.epoch,index⟩,target.generation index⟩ =
      some ⟨(assigned target source).buffer,value,1,target.buffer.capacity+2⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have noGrow : ¬ target.buffer.capacity < source.buffer.items.length := by omega
  have bound := Nat.le_trans keep targetValid.2.1
  have valid := assigned_valid target source accept targetValid sourceValid bound
  have generation := prefix_generation target source index keep inside
  unfold read
  rw [generation]
  simp only [↓reduceIte]
  simpa [assigned,noGrow] using readRef_runs (assigned target source).buffer accept index value valid
    (by simpa [assigned_items] using found)

-- A reference retired by a previous reallocation or element destruction.
def Retired (s : Tracked α) (ref : Reference) : Prop :=
  ref.element.owner = s.buffer.owner ∧
    (ref.element.epoch < s.buffer.epoch ∨
      ref.element.epoch = s.buffer.epoch ∧ ref.generation < s.generation ref.element.index)

theorem retired_unreadable (s : Tracked α) (accept : α → Bool) (ref : Reference) (retired : Retired s ref) :
    read s accept ref = none := by
  rcases retired.2 with epoch | generation
  · have unequal : ref.element.epoch ≠ s.buffer.epoch := by omega
    unfold read
    split
    · simp [readRef,unequal]
    · rfl
  · have unequal : ref.generation ≠ s.generation ref.element.index := by omega
    simp [read,unequal]

theorem retired_assigned (target source : Tracked α) (ref : Reference) (retired : Retired target ref) :
    Retired (assigned target source) ref := by
  refine ⟨by rw [assigned_owner]; exact retired.1,?_⟩
  unfold assigned
  split
  · left
    dsimp
    rcases retired.2 with epoch | generation <;> omega
  · dsimp
    rcases retired.2 with epoch | generation
    · exact Or.inl epoch
    · refine Or.inr ⟨generation.1,?_⟩
      split <;> omega

theorem erased_retired (target source : Tracked α) (index : Nat)
    (keep : source.buffer.items.length ≤ target.buffer.capacity)
    (removed : source.buffer.items.length ≤ index) (old : index < target.buffer.items.length) :
    Retired (assigned target source) ⟨⟨target.buffer.owner,target.buffer.epoch,index⟩,target.generation index⟩ := by
  have noGrow : ¬ target.buffer.capacity < source.buffer.items.length := by omega
  simp [Retired,assigned,noGrow,removed,old]

theorem reallocated_retired (target source : Tracked α) (ref : Reference)
    (grow : target.buffer.capacity < source.buffer.items.length) (owner : ref.element.owner = target.buffer.owner)
    (epoch : ref.element.epoch = target.buffer.epoch) : Retired (assigned target source) ref := by
  simp [Retired,assigned,grow,owner,epoch]

theorem copy_preserves_retired (target source : Tracked α) (accept : α → Bool) (writable : Bool)
    (result : Assignment α) (ran : copyAssign target source accept writable = some result)
    (ref : Reference) (retired : Retired target ref) : Retired result.target ref := by
  unfold copyAssign at ran
  split at ran
  · split at ran
    · cases Option.some.inj ran
      exact retired
    · cases Option.some.inj ran
      exact retired_assigned target source ref retired
  · simp at ran

inductive Assignments (accept : α → Bool) : Tracked α → Tracked α → Prop where
  | done (s : Tracked α) : Assignments accept s s
  | step (start source : Tracked α) (result : Assignment α) (finish : Tracked α)
      (ran : copyAssign start source accept true = some result)
      (tail : Assignments accept result.target finish) : Assignments accept start finish

theorem Assignments.retired {accept : α → Bool} {start finish : Tracked α}
    (runs : Assignments accept start finish) (ref : Reference) (retired : Retired start ref) :
    Retired finish ref := by
  induction runs with
  | done s => exact retired
  | step start source result finish ran tail ih => exact ih (copy_preserves_retired start source _ _ result ran ref retired)

theorem Assignments.no_resurrection {accept : α → Bool} {start finish : Tracked α}
    (runs : Assignments accept start finish) (ref : Reference) (retired : Retired start ref) :
    read finish accept ref = none := retired_unreadable finish accept ref (runs.retired ref retired)


theorem copy_properties (target source : Tracked α) (accept : α → Bool) (writable : Bool)
    (result : Assignment α) (ran : copyAssign target source accept writable = some result) :
    result.target.buffer.Valid accept ∧ result.target.buffer.owner = target.buffer.owner ∧
      result.work ≤ target.buffer.items.length+source.buffer.items.length+1 ∧
      target.buffer.capacity+1 ≤ result.peak ∧ result.target.buffer.capacity+1 ≤ result.peak := by
  unfold copyAssign at ran
  split at ran
  · rename_i good
    split at ran
    · cases Option.some.inj ran
      exact ⟨good.1,rfl,by dsimp; omega,Nat.le_refl _,Nat.le_refl _⟩
    · cases Option.some.inj ran
      refine ⟨assigned_valid target source accept good.1 good.2.1 good.2.2.2,
        assigned_owner target source,Nat.le_refl _,?_,?_⟩
      · dsimp
        split <;> omega
      · dsimp
        rw [assigned_capacity]
        split <;> omega
  · simp at ran

-- Only the target's physical slot and ghost lifetimes change. All other
-- buffers, including a distinct source, keep their contents and references.
structure LifetimeStore (α : Type) where
  physical : Proofs.CppVectorStore.Store α
  generation : Nat → Nat → Nat := fun _ _ => 0

def withAssignment (s : LifetimeStore α) (owner : Nat) (old : Buffer α) (result : Assignment α) : LifetimeStore α :=
  ⟨{s.physical with objects := s.physical.objects.set owner (some result.target.buffer), work := s.physical.work+result.work, peak := max s.physical.peak (s.physical.liveSpace+(result.peak-(old.capacity+1))-s.physical.baseSpace)},
    fun other => if other = owner then result.target.generation else s.generation other⟩

def storeAssign (s : LifetimeStore α) (targetOwner sourceOwner : Nat) (accept : α → Bool)
    (writable : Bool) : Option (LifetimeStore α) := do
  let target ← s.physical.lookup targetOwner
  let source ← s.physical.lookup sourceOwner
  let result ← copyAssign ⟨target,s.generation targetOwner⟩ ⟨source,s.generation sourceOwner⟩ accept writable
  let (physical,_) ← s.physical.commit targetOwner accept ⟨result.target.buffer,(),result.work,result.peak⟩
  some ⟨physical,fun other => if other = targetOwner then result.target.generation else s.generation other⟩

def storeRead (s : LifetimeStore α) (accept : α → Bool) (ref : Reference) : Option (Result α α) := do
  let buffer ← s.physical.lookup ref.element.owner
  read ⟨buffer,s.generation ref.element.owner⟩ accept ref

theorem store_runs (s : LifetimeStore α) (targetOwner sourceOwner : Nat) (accept : α → Bool)
    (valid : s.physical.Valid accept) (target source : Buffer α)
    (targetFound : s.physical.lookup targetOwner = some target)
    (sourceFound : s.physical.lookup sourceOwner = some source)
    (bound : source.items.length ≤ target.limit) :
    ∃ result, copyAssign ⟨target,s.generation targetOwner⟩ ⟨source,s.generation sourceOwner⟩ accept true = some result ∧
      storeAssign s targetOwner sourceOwner accept true = some (withAssignment s targetOwner target result) := by
  have targetValid := (valid _ _ targetFound).2
  have sourceValid := (valid _ _ sourceFound).2
  have success : ∃ result, copyAssign ⟨target,s.generation targetOwner⟩ ⟨source,s.generation sourceOwner⟩ accept true = some result := by
    unfold copyAssign
    dsimp only
    simp only [targetValid,sourceValid,bound,true_and,↓reduceIte]
    split <;> exact ⟨_,rfl⟩
  obtain ⟨result,ran⟩ := success
  have props := copy_properties _ _ _ _ result ran
  have owned := (valid _ _ targetFound).1
  have same := Eq.trans props.2.1 owned
  have committed := Proofs.CppVectorStore.commit_runs s.physical targetOwner accept target
    ⟨result.target.buffer,(),result.work,result.peak⟩ targetFound owned same props.1 props.2.2.2.1 props.2.2.2.2
  refine ⟨result,ran,?_⟩
  simp only [storeAssign,targetFound,sourceFound,ran,committed,Bind.bind,Option.bind,withAssignment]

theorem store_valid (s : LifetimeStore α) (targetOwner sourceOwner : Nat) (accept : α → Bool)
    (valid : s.physical.Valid accept) (target source : Buffer α)
    (targetFound : s.physical.lookup targetOwner = some target)
    (_sourceFound : s.physical.lookup sourceOwner = some source)
    (result : Assignment α)
    (ran : copyAssign ⟨target,s.generation targetOwner⟩ ⟨source,s.generation sourceOwner⟩ accept true = some result) :
    (withAssignment s targetOwner target result).physical.Valid accept := by
  have props := copy_properties _ _ _ _ result ran
  have owned := Eq.trans props.2.1 (valid _ _ targetFound).1
  exact Proofs.CppVectorStore.commit_valid s.physical targetOwner accept
    ⟨result.target.buffer,(),result.work,result.peak⟩ valid
    (Proofs.CppVectorStore.lookup_bound s.physical _ _ targetFound) owned props.1

theorem store_target (s : LifetimeStore α) (owner : Nat) (old : Buffer α) (result : Assignment α)
    (found : s.physical.lookup owner = some old) :
    (withAssignment s owner old result).physical.lookup owner = some result.target.buffer := by
  exact Proofs.CppVectorStore.lookup_set_same s.physical owner _
    (Proofs.CppVectorStore.lookup_bound s.physical owner old found)

theorem store_other (s : LifetimeStore α) (owner other : Nat) (old : Buffer α) (result : Assignment α)
    (different : owner ≠ other) :
    (withAssignment s owner old result).physical.lookup other = s.physical.lookup other ∧
      (withAssignment s owner old result).generation other = s.generation other := by
  refine ⟨Proofs.CppVectorStore.lookup_set_other s.physical owner other _ different,?_⟩
  simp [withAssignment,Ne.symm different]

theorem store_other_reference (s : LifetimeStore α) (owner : Nat) (old : Buffer α)
    (result : Assignment α) (accept : α → Bool) (ref : Reference) (different : owner ≠ ref.element.owner) :
    storeRead (withAssignment s owner old result) accept ref = storeRead s accept ref := by
  obtain ⟨buffer,generation⟩ := store_other s owner ref.element.owner old result different
  simp only [storeRead,buffer,generation]


theorem reference_runs (s : Tracked α) (accept : α → Bool) (index : Nat)
    (valid : s.buffer.Valid accept) (inside : index < s.buffer.items.length) :
    reference s accept (index : Int) = some ⟨⟨s.buffer.owner,s.buffer.epoch,index⟩,s.generation index⟩ := by
  simp [reference,elementRef_runs s.buffer accept (index : Int) valid (by omega) (by simpa using inside)]

theorem store_work (s : LifetimeStore α) (owner : Nat) (old : Buffer α) (result : Assignment α) :
    (withAssignment s owner old result).physical.work = s.physical.work+result.work := rfl

theorem store_space (s : LifetimeStore α) (owner : Nat) (old : Buffer α) (result : Assignment α)
    (found : s.physical.lookup owner = some old) :
    (withAssignment s owner old result).physical.liveSpace+old.capacity+1 =
      s.physical.liveSpace+result.target.buffer.capacity+1 := by
  have raw : s.physical.objects[owner]? = some (some old) := by
    unfold Proofs.CppVectorStore.Store.lookup at found
    cases lookup : s.physical.objects[owner]? with
    | none => simp [lookup] at found
    | some value => cases value with
      | none => simp [lookup] at found
      | some buffer =>
        have same : buffer = old := by simpa [lookup] using found
        subst buffer
        rfl
  exact Proofs.CppVectorStore.update_space s.physical owner old result.target.buffer raw

theorem store_peak (s : LifetimeStore α) (owner : Nat) (old : Buffer α) (result : Assignment α) :
    (withAssignment s owner old result).physical.peak =
      max s.physical.peak (s.physical.liveSpace+(result.peak-(old.capacity+1))-s.physical.baseSpace) := rfl

theorem store_retired_unreadable (s : LifetimeStore α) (targetOwner sourceOwner : Nat) (accept : α → Bool)
    (valid : s.physical.Valid accept) (target source : Buffer α)
    (targetFound : s.physical.lookup targetOwner = some target) (result : Assignment α)
    (ran : copyAssign ⟨target,s.generation targetOwner⟩ ⟨source,s.generation sourceOwner⟩ accept true = some result)
    (ref : Reference) (retired : Retired ⟨target,s.generation targetOwner⟩ ref) :
    storeRead (withAssignment s targetOwner target result) accept ref = none := by
  have refOwner : ref.element.owner = targetOwner := Eq.trans retired.1 (valid _ _ targetFound).1
  have targetLookup := store_target s targetOwner target result targetFound
  have postRetired := copy_preserves_retired _ _ _ _ result ran ref retired
  simp only [storeRead,refOwner,targetLookup,Bind.bind,Option.bind]
  change read ⟨result.target.buffer,(withAssignment s targetOwner target result).generation targetOwner⟩ accept ref = none
  simpa only [withAssignment,↓reduceIte] using retired_unreadable result.target accept ref postRetired

end Proofs.CppVectorCopyAssign
