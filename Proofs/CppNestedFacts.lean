import Proofs.CppNestedProgram

namespace Proofs.CppNestedFacts
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings

-- Closed-form reductions of nested Frame operations. Each lemma states the
-- facts under which an operation succeeds and names its result; none of them
-- is specific to one program.

theorem maximum_runs (f : Frame) (owner root : Nat) (writable : Bool)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (rooted : f.state.forest.rootOwner owner = some root)
    (flag : f.rootWritable[root]? = some writable) : f.maximum owner = some writable := by
  simp [Frame.maximum,lengths,rooted,flag]

theorem resolve_root (f : Frame) (slot : Nat) (expected : Element) (binding : Binding) (scope : Nat)
    (buffer : Buffer Value) (tag : Tag) (maximum : Bool)
    (found : f.bindings[slot]? = some binding) (header : binding.header = .root scope)
    (type : binding.element = expected)
    (object : f.object binding.owner expected = some (buffer,tag))
    (parentless : tag.parent = none) (context : tag.scope = some scope)
    (max : f.maximum binding.owner = some maximum)
    (permission : binding.writable = true → maximum = true) :
    f.resolve slot expected = some (binding,buffer) := by
  subst type
  simp [Frame.resolve,Frame.headerOwner,found,header,object,parentless,context,max]
  exact permission

theorem resolve_child (f : Frame) (slot : Nat) (expected : Element) (binding : Binding)
    (address : ElementRef) (parent : Buffer Value) (parentTag : Tag) (result : Result Value Value)
    (owner : Nat) (buffer : Buffer Value) (tag : Tag) (maximum : Bool)
    (found : f.bindings[slot]? = some binding) (header : binding.header = .child address)
    (type : binding.element = expected) (same : binding.owner = owner)
    (parentObject : f.object address.owner (.vector expected) = some (parent,parentTag))
    (read : readRef parent (accepts (.vector expected)) address = some result)
    (child : result.value = .child owner)
    (object : f.object owner expected = some (buffer,tag))
    (max : f.maximum owner = some maximum)
    (permission : binding.writable = true → maximum = true) :
    f.resolve slot expected = some (binding,buffer) := by
  subst type same
  simp [Frame.resolve,Frame.headerOwner,found,header,parentObject,read,child,object,max]
  exact permission

theorem child_runs (f : Frame) (slot : Nat) (expected : Element) (index : Int) (binding : Binding)
    (parent : Buffer Value) (address : ElementRef) (result : Result Value Value) (owner : Nat)
    (buffer : Buffer Value) (tag : Tag)
    (resolved : f.resolve slot (.vector expected) = some (binding,parent))
    (captured : CppVector.elementRef parent (accepts (.vector expected)) index = some address)
    (read : readRef parent (accepts (.vector expected)) address = some result)
    (value : result.value = .child owner)
    (object : f.object owner expected = some (buffer,tag))
    (parentOf : tag.parent = some binding.owner) :
    f.child slot expected index = some (f.addBinding ⟨owner,expected,binding.writable,.child address⟩) := by
  simp [Frame.child,Frame.bindChild,resolved,captured,read,value,object,parentOf]

theorem object_buffer (f : Frame) (owner : Nat) (expected : Element) (buffer : Buffer Value) (tag : Tag)
    (object : f.object owner expected = some (buffer,tag)) :
    f.state.wellFormed = true ∧ f.state.storage.lookup owner = some buffer ∧
      f.state.forest.lookup owner = some tag ∧ tag.element = expected := by
  unfold Frame.object at object
  split at object
  · rename_i valid
    cases found : f.state.storage.lookup owner with
    | none => simp [found] at object
    | some stored =>
      cases tagFound : f.state.forest.lookup owner with
      | none => simp [found,tagFound] at object
      | some stored_tag =>
        simp only [found,tagFound,Bind.bind,Option.bind] at object
        split at object
        · rename_i same
          cases object
          exact ⟨valid,rfl,rfl,same⟩
        · simp at object
  · simp at object

-- A forest node always has a live buffer with the same owner and a payload
-- that agrees with its tag.
theorem wellFormed_pair (s : State) (owner : Nat) (tag : Tag) (valid : s.wellFormed = true)
    (found : s.forest.lookup owner = some tag) :
    ∃ buffer, s.storage.lookup owner = some buffer ∧ buffer.owner = owner ∧ payloadOK tag buffer := by
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have bound : owner < s.storage.objects.length := by
    by_cases inside : owner < s.forest.objects.length
    · omega
    · rw [CppVectorOwnership.lookup_past_end s.forest owner (by omega)] at found; contradiction
  have good := List.all_eq_true.mp checks owner (List.mem_range.mpr bound)
  cases stored : s.storage.lookup owner with
  | none => simp [State.check,found,stored] at good
  | some buffer =>
    refine ⟨buffer,rfl,?_⟩
    simpa [State.check,found,stored] using good

theorem rows_facts (s : State) (root : Nat) (tag : Tag) (buffer : Buffer Value) (ty : Ty)
    (valid : s.wellFormed = true) (tagFound : s.forest.lookup root = some tag)
    (found : s.storage.lookup root = some buffer) (element : tag.element = .vector (.integer ty)) :
    buffer.owner = root ∧ buffer.Valid (accepts tag.element) ∧
      buffer.items = tag.children.map Value.child ∧
      ∀ child ∈ tag.children, ∃ childBuffer,
        s.forest.lookup child = some ⟨.integer ty,some root,none,[]⟩ ∧ root < child ∧
        s.storage.lookup child = some childBuffer := by
  obtain ⟨stored,foundAgain,owner,payload⟩ := wellFormed_pair s root tag valid tagFound
  have same : stored = buffer := by
    rw [found] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst same
  have items : stored.items = tag.children.map Value.child := by
    have h := payload.2
    simpa [element] using h
  refine ⟨owner,payload.1,items,?_⟩
  intro child member
  have good := (CppVectorOwnership.wellFormed_tag s.forest root tag (wellFormed_parts s valid).2.1 tagFound).2.2.2
  simp only [element] at good
  obtain ⟨earlier,rest⟩ := good child member
  cases childFound : s.forest.lookup child with
  | none => simp [childFound] at rest
  | some childTag =>
    simp only [childFound] at rest
    obtain ⟨parent,context,type⟩ := rest
    have childOK := CppVectorOwnership.wellFormed_tag s.forest child childTag (wellFormed_parts s valid).2.1 childFound
    have noChildren : childTag.children = [] := by
      have h := childOK.2.2.2
      simp only [type] at h
      exact h
    obtain ⟨childBuffer,storedFound,_,_⟩ := wellFormed_pair s child childTag valid childFound
    have tagEq : childTag = ⟨.integer ty,some root,none,[]⟩ := by
      cases childTag
      simp_all
    exact ⟨childBuffer,by rw [tagEq],earlier,storedFound⟩

end Proofs.CppNestedFacts
