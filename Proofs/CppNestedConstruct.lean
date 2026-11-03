import Proofs.CppNestedVectorBindings

namespace Proofs.CppNestedConstruct
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore

-- `std::vector<std::vector<T>> v(count)`: one root header whose buffer holds
-- `count` logical child IDs, followed by `count` empty child vectors. Parent
-- IDs are always smaller than child IDs, and no existing ID is reused.
def rowIds (root count : Nat) : List Nat := (List.range count).map fun j => root+1+j

def rootTag (ty : Ty) (scope root count : Nat) : Tag :=
  ⟨.vector (.integer ty),none,some scope,rowIds root count⟩

def rowTag (ty : Ty) (root : Nat) : Tag := ⟨.integer ty,some root,none,[]⟩

def _root_.Proofs.CppVectorOwnership.Forest.constructRows (f : Forest) (ty : Ty) (scope count : Nat) : Forest :=
  ⟨f.objects ++ some (rootTag ty scope f.objects.length count) ::
    (List.range count).map fun _ => some (rowTag ty f.objects.length)⟩

theorem rowIds_length (root count : Nat) : (rowIds root count).length = count := by
  simp [rowIds]

theorem rowIds_nodup (root count : Nat) : (rowIds root count).Nodup := by
  unfold rowIds
  exact List.Pairwise.map _ (fun a b different same => different (by omega)) List.nodup_range

theorem mem_rowIds (root count child : Nat) :
    child ∈ rowIds root count ↔ ∃ j, j < count ∧ child = root+1+j := by
  simp only [rowIds,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j,bound,rfl⟩; exact ⟨j,bound,rfl⟩
  · rintro ⟨j,bound,rfl⟩; exact ⟨j,bound,rfl⟩

theorem constructRows_length (f : Forest) (ty : Ty) (scope count : Nat) :
    (f.constructRows ty scope count).objects.length = f.objects.length+1+count := by
  simp [Forest.constructRows]; omega

theorem constructRows_old (f : Forest) (ty : Ty) (scope count owner : Nat)
    (bound : owner < f.objects.length) :
    (f.constructRows ty scope count).lookup owner = f.lookup owner := by
  simp [Forest.constructRows,Forest.lookup,List.getElem?_append_left bound]

theorem constructRows_root (f : Forest) (ty : Ty) (scope count : Nat) :
    (f.constructRows ty scope count).lookup f.objects.length =
      some (rootTag ty scope f.objects.length count) := by
  simp [Forest.constructRows,Forest.lookup]

theorem constructRows_row (f : Forest) (ty : Ty) (scope count j : Nat) (bound : j < count) :
    (f.constructRows ty scope count).lookup (f.objects.length+1+j) =
      some (rowTag ty f.objects.length) := by
  have shift : f.objects.length+1+j-f.objects.length = j+1 := by omega
  simp only [Forest.constructRows,Forest.lookup]
  rw [List.getElem?_append_right (by omega),shift,List.getElem?_cons_succ,List.getElem?_map,
    List.getElem?_range bound]
  rfl

theorem tagOK_extend (f g : Forest) (mono : ∀ i t, f.lookup i = some t → g.lookup i = some t)
    (owner : Nat) (tag : Tag) (ok : f.tagOK owner tag) : g.tagOK owner tag := by
  obtain ⟨supported,nodup,parent,children⟩ := ok
  refine ⟨supported,nodup,?_,?_⟩
  · unfold Forest.parentOK at parent ⊢
    cases hp : tag.parent with
    | none => simpa [hp] using parent
    | some p =>
      simp only [hp] at parent ⊢
      obtain ⟨earlier,context,rest⟩ := parent
      refine ⟨earlier,context,?_⟩
      cases found : f.lookup p with
      | none => simp [found] at rest
      | some origin => rw [mono p origin found]; simpa [found] using rest
  · cases he : tag.element with
    | integer ty => simpa [he] using children
    | vector element =>
      simp only [he] at children ⊢
      intro child member
      obtain ⟨earlier,rest⟩ := children child member
      refine ⟨earlier,?_⟩
      cases found : f.lookup child with
      | none => simp [found] at rest
      | some node => rw [mono child node found]; simpa [found] using rest

theorem constructRows_mono (f : Forest) (ty : Ty) (scope count : Nat) (i : Nat) (t : Tag)
    (found : f.lookup i = some t) :
    (f.constructRows ty scope count).lookup i = some t := by
  have bound : i < f.objects.length := by
    by_cases inside : i < f.objects.length
    · exact inside
    · rw [lookup_past_end f i (by omega)] at found; contradiction
  rw [constructRows_old f ty scope count i bound]; exact found

theorem rootTag_ok (f : Forest) (ty : Ty) (scope count : Nat) (supported : CppVectorBindings.supported ty) :
    (f.constructRows ty scope count).tagOK f.objects.length (rootTag ty scope f.objects.length count) := by
  refine ⟨by simp [rootTag,Element.supported,supported],rowIds_nodup _ _,by simp [Forest.parentOK,rootTag],?_⟩
  simp only [rootTag]
  intro child member
  obtain ⟨j,bound,rfl⟩ := (mem_rowIds _ _ _).mp member
  refine ⟨by omega,?_⟩
  rw [constructRows_row f ty scope count j bound]
  simp [rowTag]

theorem rowTag_ok (f : Forest) (ty : Ty) (scope count j : Nat) (supported : CppVectorBindings.supported ty)
    (bound : j < count) :
    (f.constructRows ty scope count).tagOK (f.objects.length+1+j) (rowTag ty f.objects.length) := by
  refine ⟨by simp [Element.supported,rowTag,supported],by simp [rowTag],?_,by simp [rowTag]⟩
  simp only [Forest.parentOK,rowTag]
  refine ⟨by omega,trivial,?_⟩
  rw [constructRows_root f ty scope count]
  simp only [rootTag]
  exact ⟨(mem_rowIds _ _ _).mpr ⟨j,bound,rfl⟩,trivial⟩

theorem constructRows_wellFormed (f : Forest) (ty : Ty) (scope count : Nat)
    (valid : f.wellFormed = true) (supported : CppVectorBindings.supported ty) :
    (f.constructRows ty scope count).wellFormed = true := by
  unfold Forest.wellFormed
  rw [constructRows_length]
  apply List.all_eq_true.mpr
  intro i member
  have inRange := List.mem_range.mp member
  unfold Forest.check
  by_cases old : i < f.objects.length
  · rw [constructRows_old f ty scope count i old]
    cases found : f.lookup i with
    | none => rfl
    | some tag =>
      simp only [decide_eq_true_eq]
      exact tagOK_extend f _ (constructRows_mono f ty scope count) i tag (wellFormed_tag f i tag valid found)
  · by_cases isRoot : i = f.objects.length
    · subst i
      rw [constructRows_root f ty scope count]
      simpa using rootTag_ok f ty scope count supported
    · obtain ⟨j,rfl⟩ : ∃ j, i = f.objects.length+1+j := ⟨i-f.objects.length-1,by omega⟩
      have bound : j < count := by omega
      rw [constructRows_row f ty scope count j bound]
      simpa using rowTag_ok f ty scope count j supported bound

-- sizeof(std::vector<T>) is 24 bytes in the fixed LP64 libstdc++ ABI.
def rowLimit : Nat := (2^63-1)/24

def rootBuffer (root count : Nat) : Buffer Value :=
  ⟨root,(rowIds root count).map Value.child,count,rowLimit,0⟩

def rowBuffer (ty : Ty) (owner : Nat) : Buffer Value :=
  ⟨owner,[],0,CppVectorBindings.sizeLimit ty,0⟩

-- Work is one step per constructed element plus the root. The peak adds the
-- new root header and its `count` child headers to the nested live space.
def _root_.Proofs.CppNestedVectorStore.State.constructRows (s : State) (ty : Ty) (scope count : Nat) : Option State :=
  if s.wellFormed = true ∧ CppVectorBindings.supported ty ∧ count ≤ rowLimit then
    let root := s.storage.objects.length
    some ⟨s.forest.constructRows ty scope count,
      {s.storage with
        objects := s.storage.objects ++ some (rootBuffer root count) ::
          (List.range count).map fun j => some (rowBuffer ty (root+1+j)),
        work := s.storage.work+count+1,
        peak := max s.storage.peak (s.liveSpace+(count+2)-s.storage.baseSpace)}⟩
  else none

theorem constructRows_storage_old (s : State) (ty : Ty) (scope count owner : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) (bound : owner < s.storage.objects.length) :
    next.storage.lookup owner = s.storage.lookup owner := by
  unfold State.constructRows at ran
  split at ran
  · cases ran
    simp [Store.lookup,List.getElem?_append_left bound]
  · simp at ran

theorem constructRows_inv (s : State) (ty : Ty) (scope count : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) :
    s.wellFormed = true ∧ CppVectorBindings.supported ty ∧ count ≤ rowLimit ∧
      next = ⟨s.forest.constructRows ty scope count,
        {s.storage with
          objects := s.storage.objects ++ some (rootBuffer s.storage.objects.length count) ::
            (List.range count).map fun j => some (rowBuffer ty (s.storage.objects.length+1+j)),
          work := s.storage.work+count+1,
          peak := max s.storage.peak (s.liveSpace+(count+2)-s.storage.baseSpace)}⟩ := by
  unfold State.constructRows at ran
  split at ran
  · rename_i good
    cases ran
    exact ⟨good.1,good.2.1,good.2.2,rfl⟩
  · simp at ran

theorem constructRows_state_wellFormed (s : State) (ty : Ty) (scope count : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) : next.wellFormed = true := by
  obtain ⟨valid,supported,limit,rfl⟩ := constructRows_inv s ty scope count next ran
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have forestLength := constructRows_length s.forest ty scope count
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨?_,constructRows_wellFormed s.forest ty scope count forest supported⟩,?_⟩
  · simp only [List.length_append,List.length_cons,List.length_map,List.length_range]
    omega
  · apply List.all_eq_true.mpr
    intro i member
    have inRange := List.mem_range.mp member
    simp only [List.length_append,List.length_cons,List.length_map,List.length_range] at inRange
    by_cases old : i < s.storage.objects.length
    · have good := List.all_eq_true.mp checks i (List.mem_range.mpr old)
      have forestOld : i < s.forest.objects.length := by omega
      simpa [State.check,constructRows_old s.forest ty scope count i forestOld,Store.lookup,
        List.getElem?_append_left old] using good
    · by_cases isRoot : i = s.storage.objects.length
      · subst i
        have rootLookup := constructRows_root s.forest ty scope count
        rw [lengths] at rootLookup
        simp only [State.check,rootLookup,lengths,Store.lookup,List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self,List.getElem?_cons_zero,Option.join_some]
        have tag := rootTag_ok s.forest ty scope count supported
        simp only [decide_eq_true_eq,rootBuffer,payloadOK,rootTag]
        refine ⟨trivial,⟨by simp [rowIds_length],limit,?_⟩,trivial⟩
        simp [List.all_map,Function.comp_def,accepts]
      · obtain ⟨j,rfl⟩ : ∃ j, i = s.storage.objects.length+1+j := ⟨i-s.storage.objects.length-1,by omega⟩
        have bound : j < count := by omega
        have rowLookup := constructRows_row s.forest ty scope count j bound
        rw [lengths] at rowLookup
        have shift : s.storage.objects.length+1+j-s.storage.objects.length = j+1 := by omega
        simp only [State.check,rowLookup,Store.lookup,List.getElem?_append_right (by omega : s.storage.objects.length ≤ s.storage.objects.length+1+j),
          shift,List.getElem?_cons_succ,List.getElem?_map,List.getElem?_range bound,Option.map_some,Option.join_some]
        simp only [decide_eq_true_eq,rowBuffer,payloadOK,rowTag]
        refine ⟨trivial,⟨by simp,by simp,by simp⟩,trivial⟩

theorem constructRows_storage_root (s : State) (ty : Ty) (scope count : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) :
    next.storage.lookup s.storage.objects.length = some (rootBuffer s.storage.objects.length count) := by
  obtain ⟨_,_,_,rfl⟩ := constructRows_inv s ty scope count next ran
  simp [Store.lookup]

theorem constructRows_storage_row (s : State) (ty : Ty) (scope count k : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) (inside : k < count) :
    next.storage.lookup (s.storage.objects.length+1+k) =
      some (rowBuffer ty (s.storage.objects.length+1+k)) := by
  obtain ⟨_,_,_,rfl⟩ := constructRows_inv s ty scope count next ran
  have shift : s.storage.objects.length+1+k-s.storage.objects.length = k+1 := by omega
  simp only [Store.lookup]
  rw [List.getElem?_append_right (by omega),shift,List.getElem?_cons_succ,List.getElem?_map,
    List.getElem?_range inside]
  rfl

theorem constructRows_forest (s : State) (ty : Ty) (scope count : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) :
    next.forest = s.forest.constructRows ty scope count := by
  obtain ⟨_,_,_,rfl⟩ := constructRows_inv s ty scope count next ran
  rfl

theorem constructRows_objects_length (s : State) (ty : Ty) (scope count : Nat) (next : State)
    (ran : s.constructRows ty scope count = some next) :
    next.storage.objects.length = s.storage.objects.length+1+count := by
  obtain ⟨_,_,_,rfl⟩ := constructRows_inv s ty scope count next ran
  simp; omega

-- `std::vector<T> name;`: one empty root owned by the current scope.
def flatTag (ty : Ty) (scope : Nat) : Tag := ⟨.integer ty,none,some scope,[]⟩

def _root_.Proofs.CppVectorOwnership.Forest.declareRoot (f : Forest) (ty : Ty) (scope : Nat) : Forest :=
  ⟨f.objects ++ [some (flatTag ty scope)]⟩

def flatBuffer (ty : Ty) (owner : Nat) : Buffer Value := ⟨owner,[],0,CppVectorBindings.sizeLimit ty,0⟩

def _root_.Proofs.CppNestedVectorStore.State.declareVector (s : State) (ty : Ty) (scope : Nat) : Option State :=
  if s.wellFormed = true ∧ CppVectorBindings.supported ty then
    some ⟨s.forest.declareRoot ty scope,
      {s.storage with
        objects := s.storage.objects ++ [some (flatBuffer ty s.storage.objects.length)],
        work := s.storage.work+1,
        peak := max s.storage.peak (s.liveSpace+1-s.storage.baseSpace)}⟩
  else none

theorem declareVector_inv (s : State) (ty : Ty) (scope : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) :
    s.wellFormed = true ∧ CppVectorBindings.supported ty ∧
      next = ⟨s.forest.declareRoot ty scope,
        {s.storage with
          objects := s.storage.objects ++ [some (flatBuffer ty s.storage.objects.length)],
          work := s.storage.work+1,
          peak := max s.storage.peak (s.liveSpace+1-s.storage.baseSpace)}⟩ := by
  unfold State.declareVector at ran
  split at ran
  · rename_i good
    cases ran
    exact ⟨good.1,good.2,rfl⟩
  · simp at ran

theorem declareRoot_length (f : Forest) (ty : Ty) (scope : Nat) :
    (f.declareRoot ty scope).objects.length = f.objects.length+1 := by
  simp [Forest.declareRoot]

theorem declareRoot_old (f : Forest) (ty : Ty) (scope owner : Nat) (bound : owner < f.objects.length) :
    (f.declareRoot ty scope).lookup owner = f.lookup owner := by
  simp [Forest.declareRoot,Forest.lookup,List.getElem?_append_left bound]

theorem declareRoot_new (f : Forest) (ty : Ty) (scope : Nat) :
    (f.declareRoot ty scope).lookup f.objects.length = some (flatTag ty scope) := by
  simp [Forest.declareRoot,Forest.lookup]

theorem declareRoot_wellFormed (f : Forest) (ty : Ty) (scope : Nat) (valid : f.wellFormed = true)
    (supported : CppVectorBindings.supported ty) : (f.declareRoot ty scope).wellFormed = true := by
  unfold Forest.wellFormed
  rw [declareRoot_length]
  apply List.all_eq_true.mpr
  intro i member
  have inRange := List.mem_range.mp member
  unfold Forest.check
  by_cases old : i < f.objects.length
  · rw [declareRoot_old f ty scope i old]
    cases found : f.lookup i with
    | none => rfl
    | some tag =>
      simp only [decide_eq_true_eq]
      refine tagOK_extend f _ (fun j t h => ?_) i tag (wellFormed_tag f i tag valid found)
      have bound : j < f.objects.length := by
        by_cases inside : j < f.objects.length
        · exact inside
        · rw [lookup_past_end f j (by omega)] at h; contradiction
      rw [declareRoot_old f ty scope j bound]; exact h
  · have isNew : i = f.objects.length := by omega
    subst i
    rw [declareRoot_new f ty scope]
    simp only [decide_eq_true_eq]
    exact ⟨by simp [flatTag,Element.supported,supported],by simp [flatTag],by simp [Forest.parentOK,flatTag],
      by simp [flatTag]⟩

theorem declareVector_wellFormed (s : State) (ty : Ty) (scope : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) : next.wellFormed = true := by
  obtain ⟨valid,supported,rfl⟩ := declareVector_inv s ty scope next ran
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have forestLength := declareRoot_length s.forest ty scope
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨?_,declareRoot_wellFormed s.forest ty scope forest supported⟩,?_⟩
  · simp only [List.length_append,List.length_singleton]
    omega
  · apply List.all_eq_true.mpr
    intro i member
    have inRange := List.mem_range.mp member
    simp only [List.length_append,List.length_singleton] at inRange
    by_cases old : i < s.storage.objects.length
    · have good := List.all_eq_true.mp checks i (List.mem_range.mpr old)
      have forestOld : i < s.forest.objects.length := by omega
      simpa [State.check,declareRoot_old s.forest ty scope i forestOld,Store.lookup,
        List.getElem?_append_left old] using good
    · have isNew : i = s.storage.objects.length := by omega
      subst i
      have rootLookup := declareRoot_new s.forest ty scope
      rw [lengths] at rootLookup
      simp only [State.check,rootLookup,lengths,Store.lookup,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.join_some]
      simp only [decide_eq_true_eq,flatBuffer,payloadOK,flatTag]
      exact ⟨trivial,⟨by simp,by simp,by simp⟩,trivial⟩

theorem declareVector_storage_old (s : State) (ty : Ty) (scope owner : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) (bound : owner < s.storage.objects.length) :
    next.storage.lookup owner = s.storage.lookup owner := by
  obtain ⟨_,_,rfl⟩ := declareVector_inv s ty scope next ran
  simp [Store.lookup,List.getElem?_append_left bound]

theorem declareVector_storage_new (s : State) (ty : Ty) (scope : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) :
    next.storage.lookup s.storage.objects.length = some (flatBuffer ty s.storage.objects.length) := by
  obtain ⟨_,_,rfl⟩ := declareVector_inv s ty scope next ran
  simp [Store.lookup]

theorem declareVector_forest (s : State) (ty : Ty) (scope : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) : next.forest = s.forest.declareRoot ty scope := by
  obtain ⟨_,_,rfl⟩ := declareVector_inv s ty scope next ran
  rfl

theorem declareVector_objects_length (s : State) (ty : Ty) (scope : Nat) (next : State)
    (ran : s.declareVector ty scope = some next) :
    next.storage.objects.length = s.storage.objects.length+1 := by
  obtain ⟨_,_,rfl⟩ := declareVector_inv s ty scope next ran
  simp


-- `std::vector<T> name(count, value);`: one root owned by the current scope holding `count` copies.
def _root_.Proofs.CppNestedVectorStore.State.fillVector (s : State) (ty : Ty) (scope count : Nat) (value : Int) :
    Option State :=
  if s.wellFormed = true ∧ CppVectorBindings.supported ty ∧ count ≤ CppVectorBindings.sizeLimit ty ∧
      ty.valid value = true then
    some ⟨s.forest.declareRoot ty scope,
      {s.storage with
        objects := s.storage.objects ++ [some ⟨s.storage.objects.length,List.replicate count (Value.integer value),count,
          CppVectorBindings.sizeLimit ty,0⟩],
        work := s.storage.work+(count+1),
        peak := max s.storage.peak (s.liveSpace+(count+2)-s.storage.baseSpace)}⟩
  else none

theorem fillVector_inv (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) :
    s.wellFormed = true ∧ CppVectorBindings.supported ty ∧ count ≤ CppVectorBindings.sizeLimit ty ∧
      ty.valid value = true ∧
      next = ⟨s.forest.declareRoot ty scope,
        {s.storage with
          objects := s.storage.objects ++ [some ⟨s.storage.objects.length,List.replicate count (Value.integer value),count,
            CppVectorBindings.sizeLimit ty,0⟩],
          work := s.storage.work+(count+1),
          peak := max s.storage.peak (s.liveSpace+(count+2)-s.storage.baseSpace)}⟩ := by
  unfold State.fillVector at ran
  split at ran
  · rename_i good
    cases ran
    exact ⟨good.1,good.2.1,good.2.2.1,good.2.2.2,rfl⟩
  · simp at ran

theorem fillVector_storage_old (s : State) (ty : Ty) (scope count : Nat) (value : Int) (owner : Nat) (next : State)
    (ran : s.fillVector ty scope count value = some next) (bound : owner < s.storage.objects.length) :
    next.storage.lookup owner = s.storage.lookup owner := by
  obtain ⟨_,_,_,_,rfl⟩ := fillVector_inv s ty scope count value next ran
  simp [Store.lookup,List.getElem?_append_left bound]

theorem fillVector_storage_new (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) :
    next.storage.lookup s.storage.objects.length = some ⟨s.storage.objects.length,
      List.replicate count (Value.integer value),count,CppVectorBindings.sizeLimit ty,0⟩ := by
  obtain ⟨_,_,_,_,rfl⟩ := fillVector_inv s ty scope count value next ran
  simp [Store.lookup]

theorem fillVector_forest (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) : next.forest = s.forest.declareRoot ty scope := by
  obtain ⟨_,_,_,_,rfl⟩ := fillVector_inv s ty scope count value next ran
  rfl

theorem fillVector_objects_length (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) :
    next.storage.objects.length = s.storage.objects.length+1 := by
  obtain ⟨_,_,_,_,rfl⟩ := fillVector_inv s ty scope count value next ran
  simp

theorem fillVector_work (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) :
    next.storage.work = s.storage.work+count+1 := by
  obtain ⟨_,_,_,_,rfl⟩ := fillVector_inv s ty scope count value next ran
  simp; omega

theorem fillVector_wellFormed (s : State) (ty : Ty) (scope count : Nat) (value : Int) (next : State)
    (ran : s.fillVector ty scope count value = some next) : next.wellFormed = true := by
  obtain ⟨valid,supported,bounded,accepted,rfl⟩ := fillVector_inv s ty scope count value next ran
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have forestLength := declareRoot_length s.forest ty scope
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨?_,declareRoot_wellFormed s.forest ty scope forest supported⟩,?_⟩
  · simp only [List.length_append,List.length_singleton]
    omega
  · apply List.all_eq_true.mpr
    intro i member
    have inRange := List.mem_range.mp member
    simp only [List.length_append,List.length_singleton] at inRange
    by_cases old : i < s.storage.objects.length
    · have good := List.all_eq_true.mp checks i (List.mem_range.mpr old)
      have forestOld : i < s.forest.objects.length := by omega
      simpa [State.check,declareRoot_old s.forest ty scope i forestOld,Store.lookup,
        List.getElem?_append_left old] using good
    · have isNew : i = s.storage.objects.length := by omega
      subst i
      have rootLookup := declareRoot_new s.forest ty scope
      rw [lengths] at rootLookup
      simp only [State.check,rootLookup,lengths,Store.lookup,
        List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero,Option.join_some]
      simp only [decide_eq_true_eq,payloadOK,flatTag]
      have valid : (⟨s.storage.objects.length,List.replicate count (Value.integer value),count,
          CppVectorBindings.sizeLimit ty,0⟩ : Buffer Value).Valid (accepts (Element.integer ty)) := by
        refine ⟨by simp,bounded,?_⟩
        simp [accepts,accepted]
      apply decide_eq_true
      exact ⟨trivial,valid,trivial⟩

end Proofs.CppNestedConstruct
