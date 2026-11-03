import Proofs.CppVectorCopyAssign
import Proofs.CppFrameCopy

namespace Proofs.CppFrameCopyAssign
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings
open Proofs.DynamicResultValid

structure TrackedFrame where
  frame : Frame
  generation : Nat → Nat → Nat := fun _ _ => 0

structure TrackedReference where
  original : Reference
  generation : Nat
  deriving DecidableEq, Repr

def elementRef (s : TrackedFrame) (slot : Nat) (ty : Ty) (index : Int) : Option TrackedReference := do
  let original ← s.frame.elementRef slot ty index
  some ⟨original,s.generation original.address.owner original.address.index⟩

def read (s : TrackedFrame) (ref : TrackedReference) : Option Int :=
  if ref.generation = s.generation ref.original.address.owner ref.original.address.index then
    s.frame.read ref.original else none

def write (s : TrackedFrame) (ref : TrackedReference) (value : Int) : Option TrackedFrame := do
  if ref.generation = s.generation ref.original.address.owner ref.original.address.index then
    let frame ← s.frame.write ref.original value
    some ⟨frame,s.generation⟩
  else none

def after (s : TrackedFrame) (owner : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) : TrackedFrame :=
  ⟨s.frame.updated owner old ⟨result.target.buffer,(),result.work,result.peak⟩,
    fun other => if other = owner then result.target.generation else s.generation other⟩

def copyAssign (s : TrackedFrame) (targetSlot sourceSlot : Nat) (ty : Ty) : Option TrackedFrame := do
  let (targetBinding,target) ← s.frame.resolve targetSlot (.integer ty)
  let (sourceBinding,source) ← s.frame.resolve sourceSlot (.integer ty)
  let result ← Proofs.CppVectorCopyAssign.copyAssign ⟨target,s.generation targetBinding.owner⟩
    ⟨source,s.generation sourceBinding.owner⟩ (accepts (.integer ty)) targetBinding.writable
  let frame ← s.frame.commit targetBinding.owner (.integer ty) ⟨result.target.buffer,(),result.work,result.peak⟩
  some ⟨frame,fun other => if other = targetBinding.owner then result.target.generation else s.generation other⟩

theorem object_valid (f : Frame) (owner : Nat) (ty : Ty) (buffer : Buffer Value) (tag : Tag)
    (object : f.object owner (.integer ty) = some (buffer,tag)) :
    f.state.wellFormed = true ∧ f.state.storage.lookup owner = some buffer ∧
      f.state.forest.lookup owner = some tag ∧ tag.element = .integer ty ∧
      buffer.owner = owner ∧ buffer.Valid (accepts (.integer ty)) := by
  obtain ⟨valid,found,tagFound,typed⟩ := Proofs.CppFrameCopy.object_parts f owner ty buffer tag object
  obtain ⟨actual,actualFound,owns,payload⟩ := wellFormed_buffer f.state owner buffer valid found
  have same := Option.some.inj (actualFound.symm.trans tagFound)
  subst actual
  rw [payloadOK,typed] at payload
  exact ⟨valid,found,tagFound,typed,owns,payload.1⟩

theorem assign_runs (s : TrackedFrame) (targetSlot sourceSlot : Nat) (ty : Ty)
    (tb sb : Binding) (target source : Buffer Value)
    (targetResolved : s.frame.resolve targetSlot (.integer ty) = some (tb,target))
    (sourceResolved : s.frame.resolve sourceSlot (.integer ty) = some (sb,source))
    (permission : tb.writable = true) (bounded : source.items.length ≤ target.limit) :
    ∃ result, Proofs.CppVectorCopyAssign.copyAssign ⟨target,s.generation tb.owner⟩ ⟨source,s.generation sb.owner⟩
        (accepts (.integer ty)) true = some result ∧
      copyAssign s targetSlot sourceSlot ty = some (after s tb.owner target result) ∧
      (after s tb.owner target result).frame.state.wellFormed = true := by
  obtain ⟨tag,targetObject⟩ := Proofs.CppFrameCopy.resolve_object s.frame targetSlot ty tb target targetResolved
  obtain ⟨sourceTag,sourceObject⟩ := Proofs.CppFrameCopy.resolve_object s.frame sourceSlot ty sb source sourceResolved
  obtain ⟨valid,found,tagFound,typed,owns,targetValid⟩ := object_valid s.frame tb.owner ty target tag targetObject
  have sourceValid := (object_valid s.frame sb.owner ty source sourceTag sourceObject).2.2.2.2.2
  have success : ∃ result, Proofs.CppVectorCopyAssign.copyAssign ⟨target,s.generation tb.owner⟩ ⟨source,s.generation sb.owner⟩
      (accepts (.integer ty)) true = some result := by
    unfold Proofs.CppVectorCopyAssign.copyAssign
    dsimp only
    simp only [targetValid,sourceValid,bounded,true_and,↓reduceIte]
    split <;> exact ⟨_,rfl⟩
  obtain ⟨result,ran⟩ := success
  have props := Proofs.CppVectorCopyAssign.copy_properties _ _ _ _ result ran
  have newOwns : result.target.buffer.owner = tb.owner := Eq.trans props.2.1 owns
  have payload : payloadOK tag result.target.buffer := by simp only [payloadOK,typed]; exact ⟨props.1,True.intro⟩
  have committed := commit_runs s.frame tb.owner (.integer ty) target tag
    ⟨result.target.buffer,(),result.work,result.peak⟩ valid targetObject tagFound found newOwns payload
    props.2.2.2.1 props.2.2.2.2
  refine ⟨result,ran,?_,?_⟩
  · simp only [copyAssign,targetResolved,sourceResolved,permission,ran,committed,Bind.bind,Option.bind,after]
  · exact updated_wellFormed s.frame tb.owner target tag ⟨result.target.buffer,(),result.work,result.peak⟩
      valid tagFound (Proofs.CppVectorStore.lookup_bound s.frame.state.storage _ _ found) newOwns payload

theorem after_metadata (s : TrackedFrame) (owner : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) :
    (after s owner old result).frame.bindings = s.frame.bindings ∧
      (after s owner old result).frame.rootWritable = s.frame.rootWritable ∧
      (after s owner old result).frame.state.forest = s.frame.state.forest := ⟨rfl,rfl,rfl⟩

theorem after_grant (s : TrackedFrame) (owner : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) (ref : Reference) :
    (after s owner old result).frame.grant ref = s.frame.grant ref := rfl

theorem after_object (s : TrackedFrame) (owner : Nat) (old : Buffer Value) (tag : Tag) (ty : Ty)
    (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (found : s.frame.state.storage.lookup owner = some old) (tagFound : s.frame.state.forest.lookup owner = some tag)
    (typed : tag.element = .integer ty) (valid : (after s owner old result).frame.state.wellFormed = true) :
    (after s owner old result).frame.object owner (.integer ty) = some (result.target.buffer,tag) := by
  apply object_runs _ _ _ _ _ valid _ tagFound typed
  exact Proofs.CppVectorStore.lookup_set_same s.frame.state.storage owner _
    (Proofs.CppVectorStore.lookup_bound s.frame.state.storage owner old found)

theorem after_object_other (s : TrackedFrame) (owner other : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) (expected : Element)
    (different : owner ≠ other) (valid : s.frame.state.wellFormed = true)
    (postValid : (after s owner old result).frame.state.wellFormed = true) :
    (after s owner old result).frame.object other expected = s.frame.object other expected := by
  have kept : (after s owner old result).frame.state.storage.lookup other = s.frame.state.storage.lookup other := by
    simp only [after,Frame.updated,Proofs.CppVectorStore.Store.lookup,List.getElem?_set_ne different]
  simp only [Frame.object,valid,postValid,↓reduceIte]
  rw [kept]
  rfl

theorem after_read_other (s : TrackedFrame) (owner : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) (ref : TrackedReference)
    (different : owner ≠ ref.original.address.owner) (valid : s.frame.state.wellFormed = true)
    (postValid : (after s owner old result).frame.state.wellFormed = true) :
    read (after s owner old result) ref = read s ref := by
  have object := after_object_other s owner ref.original.address.owner old result (.integer ref.original.element) different valid postValid
  have generation : (after s owner old result).generation ref.original.address.owner = s.generation ref.original.address.owner := by
    simp only [after,Ne.symm different,↓reduceIte]
  simp only [read,generation]
  split
  · simp only [Frame.read,after_grant,object]
  · rfl

theorem read_retired (s : TrackedFrame) (ref : TrackedReference) (buffer : Buffer Value) (tag : Tag)
    (object : s.frame.object ref.original.address.owner (.integer ref.original.element) = some (buffer,tag))
    (retired : Proofs.CppVectorCopyAssign.Retired ⟨buffer,s.generation ref.original.address.owner⟩
      ⟨ref.original.address,ref.generation⟩) : read s ref = none := by
  rcases retired.2 with epoch | generation
  · have unequal : ref.original.address.epoch ≠ buffer.epoch := by dsimp at epoch; omega
    unfold read
    split
    · unfold Frame.read
      cases grant : s.frame.grant ref.original <;> simp [object,readRef,unequal]
    · rfl
  · have unequal : ref.generation ≠ s.generation ref.original.address.owner ref.original.address.index := by
      dsimp at generation
      omega
    simp [read,unequal]


theorem read_buffer (s : TrackedFrame) (ref : TrackedReference) (buffer : Buffer Value) (tag : Tag)
    (writable : Bool) (grant : s.frame.grant ref.original = some writable)
    (object : s.frame.object ref.original.address.owner (.integer ref.original.element) = some (buffer,tag)) :
    read s ref = (do
      let result ← Proofs.CppVectorCopyAssign.read ⟨buffer,s.generation ref.original.address.owner⟩
        (accepts (.integer ref.original.element)) ⟨ref.original.address,ref.generation⟩
      match result.value with | .integer value => some value | .child _ => none) := by
  unfold read Proofs.CppVectorCopyAssign.read
  dsimp only
  split
  · simp only [Frame.read,grant,object,Bind.bind,Option.bind]
    rfl
  · rfl

theorem after_target_retired (s : TrackedFrame) (owner sourceOwner : Nat) (old source : Buffer Value)
    (tag : Tag) (ty : Ty) (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (found : s.frame.state.storage.lookup owner = some old) (tagFound : s.frame.state.forest.lookup owner = some tag)
    (typed : tag.element = .integer ty) (postValid : (after s owner old result).frame.state.wellFormed = true)
    (ran : Proofs.CppVectorCopyAssign.copyAssign ⟨old,s.generation owner⟩ ⟨source,s.generation sourceOwner⟩
      (accepts (.integer ty)) true = some result)
    (ref : TrackedReference) (refOwner : ref.original.address.owner = owner) (refType : ref.original.element = ty)
    (retired : Proofs.CppVectorCopyAssign.Retired ⟨old,s.generation owner⟩ ⟨ref.original.address,ref.generation⟩) :
    read (after s owner old result) ref = none := by
  have postRetired := Proofs.CppVectorCopyAssign.copy_preserves_retired _ _ _ _ result ran _ retired
  have object := after_object s owner old tag ty result found tagFound typed postValid
  apply read_retired (after s owner old result) ref result.target.buffer tag
  · simpa only [refOwner,refType] using object
  · simpa only [after,refOwner,↓reduceIte] using postRetired


theorem assign_result (s : TrackedFrame) (targetSlot sourceSlot : Nat) (ty : Ty)
    (tb sb : Binding) (target source : Buffer Value)
    (targetResolved : s.frame.resolve targetSlot (.integer ty) = some (tb,target))
    (sourceResolved : s.frame.resolve sourceSlot (.integer ty) = some (sb,source))
    (permission : tb.writable = true) (bounded : source.items.length ≤ target.limit)
    (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (ran : Proofs.CppVectorCopyAssign.copyAssign ⟨target,s.generation tb.owner⟩ ⟨source,s.generation sb.owner⟩
      (accepts (.integer ty)) true = some result) :
    copyAssign s targetSlot sourceSlot ty = some (after s tb.owner target result) ∧
      (after s tb.owner target result).frame.state.wellFormed = true := by
  obtain ⟨actual,actualRun,run,valid⟩ := assign_runs s targetSlot sourceSlot ty tb sb target source
    targetResolved sourceResolved permission bounded
  have same := Option.some.inj (actualRun.symm.trans ran)
  subst actual
  exact ⟨run,valid⟩

theorem prefix_read (s : TrackedFrame) (owner sourceOwner slot index : Nat) (ty : Ty) (writable : Bool)
    (target source : Buffer Value) (tag : Tag) (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (targetValid : target.Valid (accepts (.integer ty))) (sourceValid : source.Valid (accepts (.integer ty)))
    (found : s.frame.state.storage.lookup owner = some target) (tagFound : s.frame.state.forest.lookup owner = some tag)
    (typed : tag.element = .integer ty) (postValid : (after s owner target result).frame.state.wellFormed = true)
    (targetEq : result.target = Proofs.CppVectorCopyAssign.assigned ⟨target,s.generation owner⟩ ⟨source,s.generation sourceOwner⟩)
    (owns : target.owner = owner) (keep : source.items.length ≤ target.capacity) (value : Int)
    (atIndex : source.items[index]? = some (.integer value))
    (grant : s.frame.grant ⟨slot,ty,writable,⟨owner,target.epoch,index⟩⟩ = some writable) :
    read (after s owner target result) ⟨⟨slot,ty,writable,⟨owner,target.epoch,index⟩⟩,s.generation owner index⟩ = some value := by
  have object := after_object s owner target tag ty result found tagFound typed postValid
  have nextGrant := after_grant s owner target result ⟨slot,ty,writable,⟨owner,target.epoch,index⟩⟩
  rw [grant] at nextGrant
  rw [read_buffer _ _ result.target.buffer tag writable nextGrant object]
  have primitive := Proofs.CppVectorCopyAssign.prefix_read ⟨target,s.generation owner⟩ ⟨source,s.generation sourceOwner⟩
    (accepts (.integer ty)) index (.integer value) targetValid sourceValid keep atIndex
  have changed : Proofs.CppVectorCopyAssign.read ⟨result.target.buffer,(after s owner target result).generation owner⟩
      (accepts (.integer ty)) ⟨⟨owner,target.epoch,index⟩,s.generation owner index⟩ =
      some ⟨result.target.buffer,.integer value,1,target.capacity+2⟩ := by
    simpa only [after,↓reduceIte,targetEq,owns] using primitive
  simp only [changed,Bind.bind,Option.bind]

theorem sum_one_change (xs : List Nat) (nodup : xs.Nodup) (owner : Nat) (member : owner ∈ xs)
    (f g : Nat → Nat) (other : ∀ i ∈ xs, i ≠ owner → f i = g i) :
    (xs.map f).sum+g owner = (xs.map g).sum+f owner := by
  induction xs with
  | nil => simp at member
  | cons i xs ih =>
    obtain ⟨absent,tailDup⟩ := List.nodup_cons.mp nodup
    by_cases same : i=owner
    · subst i
      have tails : xs.map f = xs.map g := by
        apply List.map_congr_left
        intro j inside
        have different : j ≠ owner := by intro eq; subst j; exact absent inside
        exact other j (by simp [inside]) different
      simp only [List.map_cons,List.sum_cons,tails]
      omega
    · have inTail : owner ∈ xs := by simpa [Ne.symm same] using member
      have tail := ih tailDup inTail (fun j inside neq => other j (by simp [inside]) neq)
      have head := other i (by simp) same
      simp only [List.map_cons,List.sum_cons,head]
      omega

theorem after_space (s : TrackedFrame) (owner : Nat) (old : Buffer Value) (tag : Tag)
    (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (found : s.frame.state.storage.lookup owner = some old) (tagFound : s.frame.state.forest.lookup owner = some tag) :
    (after s owner old result).frame.state.liveSpace+old.capacity =
      s.frame.state.liveSpace+result.target.buffer.capacity := by
  have bound := Proofs.CppVectorStore.lookup_bound s.frame.state.storage owner old found
  have newFound : (after s owner old result).frame.state.storage.lookup owner = some result.target.buffer :=
    Proofs.CppVectorStore.lookup_set_same s.frame.state.storage owner _ bound
  have other : ∀ i ∈ List.range s.frame.state.storage.objects.length, i ≠ owner →
      (after s owner old result).frame.state.nodeSpace i = s.frame.state.nodeSpace i := by
    intro i _ different
    have kept : (after s owner old result).frame.state.storage.lookup i = s.frame.state.storage.lookup i := by
      simp only [after,Frame.updated,Proofs.CppVectorStore.Store.lookup,List.getElem?_set_ne (Ne.symm different)]
    simp only [State.nodeSpace,kept]
    rfl
  have total := sum_one_change (List.range s.frame.state.storage.objects.length) List.nodup_range owner
    (List.mem_range.mpr bound) ((after s owner old result).frame.state.nodeSpace) s.frame.state.nodeSpace other
  have oldValue : s.frame.state.nodeSpace owner = old.capacity+(if tag.parent = none then 1 else 0) := by
    simp [State.nodeSpace,found,tagFound]
  have newValue : (after s owner old result).frame.state.nodeSpace owner = result.target.buffer.capacity+(if tag.parent = none then 1 else 0) := by
    simp only [State.nodeSpace,newFound]
    change (match s.frame.state.forest.lookup owner, some result.target.buffer with
      | some tag, some buffer => buffer.capacity+if tag.parent = none then 1 else 0
      | _, _ => 0) = _
    simp [tagFound]
  rw [oldValue,newValue] at total
  have sameLength : (after s owner old result).frame.state.storage.objects.length = s.frame.state.storage.objects.length := List.length_set
  unfold State.liveSpace
  rw [sameLength]
  omega

theorem after_work_peak (s : TrackedFrame) (owner : Nat) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value) :
    (after s owner old result).frame.state.storage.work = s.frame.state.storage.work+result.work ∧
      (after s owner old result).frame.state.storage.peak =
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(result.peak-(old.capacity+1))-s.frame.state.storage.baseSpace) :=
  ⟨rfl,rfl⟩


theorem assign_success (s finish : TrackedFrame) (targetSlot sourceSlot : Nat) (ty : Ty)
    (ran : copyAssign s targetSlot sourceSlot ty = some finish) :
    ∃ tb sb target source result,
      s.frame.resolve targetSlot (.integer ty) = some (tb,target) ∧
      s.frame.resolve sourceSlot (.integer ty) = some (sb,source) ∧ tb.writable = true ∧
      source.items.length ≤ target.limit ∧
      Proofs.CppVectorCopyAssign.copyAssign ⟨target,s.generation tb.owner⟩ ⟨source,s.generation sb.owner⟩
        (accepts (.integer ty)) true = some result ∧ finish = after s tb.owner target result ∧
      finish.frame.state.wellFormed = true := by
  have fullRun := ran
  unfold copyAssign at ran
  obtain ⟨⟨tb,target⟩,targetResolved,rest⟩ := bind_some _ _ _ ran
  obtain ⟨⟨sb,source⟩,sourceResolved,rest⟩ := bind_some _ _ _ rest
  obtain ⟨result,primitive,rest⟩ := bind_some _ _ _ rest
  have condition : tb.writable = true ∧ source.items.length ≤ target.limit := by
    unfold Proofs.CppVectorCopyAssign.copyAssign at primitive
    split at primitive
    · rename_i good
      exact ⟨good.2.2.1,good.2.2.2⟩
    · simp at primitive
  rw [condition.1] at primitive
  obtain ⟨canonical,valid⟩ := assign_result s targetSlot sourceSlot ty tb sb target source targetResolved sourceResolved
    condition.1 condition.2 result primitive
  have same := Option.some.inj (fullRun.symm.trans canonical)
  refine ⟨tb,sb,target,source,result,targetResolved,sourceResolved,condition.1,condition.2,primitive,same,?_⟩
  rw [same]
  exact valid

def Retired (s : TrackedFrame) (ref : TrackedReference) : Prop :=
  ∃ buffer tag, s.frame.object ref.original.address.owner (.integer ref.original.element) = some (buffer,tag) ∧
    Proofs.CppVectorCopyAssign.Retired ⟨buffer,s.generation ref.original.address.owner⟩ ⟨ref.original.address,ref.generation⟩

theorem retired_read (s : TrackedFrame) (ref : TrackedReference) (retired : Retired s ref) : read s ref = none := by
  obtain ⟨buffer,tag,object,old⟩ := retired
  exact read_retired s ref buffer tag object old

theorem assign_retired (s finish : TrackedFrame) (targetSlot sourceSlot : Nat) (ty : Ty)
    (ran : copyAssign s targetSlot sourceSlot ty = some finish) (ref : TrackedReference)
    (retired : Retired s ref) : Retired finish ref := by
  obtain ⟨tb,sb,target,source,result,tr,sr,permission,bounded,primitive,eq,postValid⟩ :=
    assign_success s finish targetSlot sourceSlot ty ran
  rw [eq] at postValid ⊢
  obtain ⟨buffer,tag,object,oldRetired⟩ := retired
  obtain ⟨valid,refFound,refTag,refTyped,_,_⟩ := object_valid s.frame _ _ buffer tag object
  by_cases sameOwner : tb.owner = ref.original.address.owner
  · obtain ⟨targetTag,targetObject⟩ := Proofs.CppFrameCopy.resolve_object s.frame targetSlot ty tb target tr
    obtain ⟨_,targetFound,targetTagFound,targetTyped,_,_⟩ := object_valid s.frame _ _ target targetTag targetObject
    rw [sameOwner] at targetFound targetTagFound
    have sameBuffer := Option.some.inj (targetFound.symm.trans refFound)
    have sameTag := Option.some.inj (targetTagFound.symm.trans refTag)
    subst buffer
    subst targetTag
    have sameType : ref.original.element = ty := by
      exact Element.integer.inj (refTyped.symm.trans targetTyped)
    have nextObject := after_object s tb.owner target tag ty result
      (by rw [sameOwner]; exact targetFound) (by rw [sameOwner]; exact targetTagFound) targetTyped postValid
    have nextRetired := Proofs.CppVectorCopyAssign.copy_preserves_retired _ _ _ _ result primitive
      ⟨ref.original.address,ref.generation⟩ (by simpa only [sameOwner] using oldRetired)
    refine ⟨result.target.buffer,tag,?_,?_⟩
    · simpa only [sameOwner,sameType] using nextObject
    · simpa only [after,← sameOwner,↓reduceIte] using nextRetired
  · refine ⟨buffer,tag,?_,?_⟩
    · rw [after_object_other s tb.owner ref.original.address.owner target result (.integer ref.original.element) sameOwner valid postValid]
      exact object
    · simpa only [after,Ne.symm sameOwner,↓reduceIte] using oldRetired

inductive Assignments : TrackedFrame → TrackedFrame → Prop where
  | done (s : TrackedFrame) : Assignments s s
  | step (s next finish : TrackedFrame) (target source : Nat) (ty : Ty)
      (ran : copyAssign s target source ty = some next) (tail : Assignments next finish) : Assignments s finish

theorem Assignments.retired {s finish : TrackedFrame} (runs : Assignments s finish)
    (ref : TrackedReference) (old : Retired s ref) : Retired finish ref := by
  induction runs with
  | done s => exact old
  | step s next finish target source ty ran tail ih => exact ih (assign_retired s next target source ty ran ref old)

theorem Assignments.no_resurrection {s finish : TrackedFrame} (runs : Assignments s finish)
    (ref : TrackedReference) (old : Retired s ref) : read finish ref = none :=
  retired_read finish ref (runs.retired ref old)


theorem write_runs (s : TrackedFrame) (ref : TrackedReference) (value : Int) (finish : Frame)
    (generation : ref.generation = s.generation ref.original.address.owner ref.original.address.index)
    (ran : s.frame.write ref.original value = some finish) :
    write s ref value = some ⟨finish,s.generation⟩ := by simp [write,generation,ran]

theorem write_retired (s : TrackedFrame) (ref : TrackedReference) (value : Int) (retired : Retired s ref) :
    write s ref value = none := by
  obtain ⟨buffer,tag,object,retired⟩ := retired
  rcases retired.2 with epoch | generation
  · have unequal : ref.original.address.epoch ≠ buffer.epoch := by dsimp at epoch; omega
    unfold write
    split
    · unfold Frame.write
      cases grant : s.frame.grant ref.original <;> simp [object,writeRef,unequal]
    · rfl
  · have unequal : ref.generation ≠ s.generation ref.original.address.owner ref.original.address.index := by
      dsimp at generation
      omega
    simp [write,unequal]

end Proofs.CppFrameCopyAssign
