import Proofs.CppNestedConstruct

namespace Proofs.CppForestAppend
open Proofs.CppScalar Proofs.CppVectorOwnership

-- Old objects retain their type, parent and scope. Their child lists may
-- grow, but every previously owned child remains owned by the same object.
def Extends (f g : Forest) : Prop :=
  ∀ i t, f.lookup i = some t → ∃ u, g.lookup i = some u ∧
    u.element = t.element ∧ u.parent = t.parent ∧ u.scope = t.scope ∧
    ∀ c ∈ t.children, c ∈ u.children

theorem lookup_lt (f : Forest) (i : Nat) (t : Tag) (found : f.lookup i = some t) :
    i < f.objects.length := by
  by_cases bound : i < f.objects.length
  · exact bound
  · rw [lookup_past_end f i (by omega)] at found
    contradiction

theorem tagOK_mono (f g : Forest) (ext : Extends f g) (i : Nat) (t : Tag)
    (good : f.tagOK i t) : g.tagOK i t := by
  obtain ⟨supported, nodup, parent, children⟩ := good
  refine ⟨supported, nodup, ?_, ?_⟩
  · unfold Forest.parentOK at parent ⊢
    cases hp : t.parent with
    | none => simpa [hp] using parent
    | some p =>
      simp only [hp] at parent ⊢
      obtain ⟨earlier, scope, rest⟩ := parent
      refine ⟨earlier, scope, ?_⟩
      cases found : f.lookup p with
      | none => simp [found] at rest
      | some origin =>
        simp only [found] at rest
        obtain ⟨next, hn, he, _, _, hc⟩ := ext p origin found
        rw [hn]
        exact ⟨hc i rest.1, he.trans rest.2⟩
  · cases he : t.element with
    | integer ty => simpa [he] using children
    | vector element =>
      simp only [he] at children ⊢
      intro child member
      obtain ⟨earlier, rest⟩ := children child member
      refine ⟨earlier, ?_⟩
      cases found : f.lookup child with
      | none => simp [found] at rest
      | some node =>
        simp only [found] at rest
        obtain ⟨next, hn, ht, hp, hs, _⟩ := ext child node found
        rw [hn]
        exact ⟨hp.trans rest.1, hs.trans rest.2.1, ht.trans rest.2.2⟩

def childTag (parent : Nat) (element : Element) : Tag :=
  ⟨element, some parent, none, []⟩

def _root_.Proofs.CppVectorOwnership.Forest.appendChild (f : Forest) (parent : Nat) (tag : Tag) (element : Element) : Forest :=
  ⟨f.objects.set parent (some {tag with children := tag.children ++ [f.objects.length]}) ++
    [some (childTag parent element)]⟩

theorem append_length (f : Forest) (parent : Nat) (tag : Tag) (element : Element) :
    (f.appendChild parent tag element).objects.length = f.objects.length + 1 := by
  simp [Forest.appendChild]

theorem append_parent (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (bound : parent < f.objects.length) :
    (f.appendChild parent tag element).lookup parent =
      some {tag with children := tag.children ++ [f.objects.length]} := by
  simp only [Forest.appendChild, Forest.lookup]
  rw [List.getElem?_append_left (by simpa using bound), List.getElem?_set_self bound]
  rfl

theorem append_old (f : Forest) (parent : Nat) (tag : Tag) (element : Element) (i : Nat)
    (bound : i < f.objects.length) (other : parent ≠ i) :
    (f.appendChild parent tag element).lookup i = f.lookup i := by
  simp only [Forest.appendChild, Forest.lookup]
  rw [List.getElem?_append_left (by simpa using bound), List.getElem?_set_ne other]

theorem append_fresh (f : Forest) (parent : Nat) (tag : Tag) (element : Element) :
    (f.appendChild parent tag element).lookup f.objects.length = some (childTag parent element) := by
  simp [Forest.appendChild, Forest.lookup]

theorem append_extends (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (found : f.lookup parent = some tag) : Extends f (f.appendChild parent tag element) := by
  intro i t ht
  have bound := lookup_lt f i t ht
  by_cases same : parent = i
  · subst i
    have equal : tag = t := Option.some.inj (found.symm.trans ht)
    subst t
    refine ⟨_, append_parent f parent tag element bound, rfl, rfl, rfl, ?_⟩
    intro c hc
    exact List.mem_append_left _ hc
  · exact ⟨t, (append_old f parent tag element i bound same).trans ht, rfl, rfl, rfl,
      fun _ hc => hc⟩

theorem children_bound (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag)
    (type : tag.element = .vector element) (child : Nat) (member : child ∈ tag.children) :
    child < f.objects.length := by
  have good := (wellFormed_tag f parent tag valid found).2.2.2
  rw [type] at good
  have childOK := (good child member).2
  cases hc : f.lookup child with
  | none => simp [hc] at childOK
  | some node => exact lookup_lt f child node hc

theorem append_parent_ok (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag)
    (type : tag.element = .vector element) :
    (f.appendChild parent tag element).tagOK parent
      {tag with children := tag.children ++ [f.objects.length]} := by
  have good := wellFormed_tag f parent tag valid found
  have mono := tagOK_mono f _ (append_extends f parent tag element found) parent tag good
  refine ⟨good.1, ?_, mono.2.2.1, ?_⟩
  · have fresh : f.objects.length ∉ tag.children := by
      intro member
      have := children_bound f parent tag element valid found type f.objects.length member
      omega
    simp [List.nodup_append, good.2.1]
    intro a ha equal
    subst a
    exact fresh ha
  · simp only [type]
    intro child member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | fresh
    · have children := mono.2.2.2
      rw [type] at children
      exact children child old
    · subst child
      refine ⟨lookup_lt f parent tag found, ?_⟩
      rw [append_fresh]
      simp [childTag]

theorem append_child_ok (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag)
    (type : tag.element = .vector element) :
    (f.appendChild parent tag element).tagOK f.objects.length (childTag parent element) := by
  have good := wellFormed_tag f parent tag valid found
  have supported : element.supported = true := by simpa [type, Element.supported] using good.1
  refine ⟨supported, by simp [childTag], ?_, ?_⟩
  · simp only [Forest.parentOK, childTag]
    refine ⟨lookup_lt f parent tag found, trivial, ?_⟩
    rw [append_parent f parent tag element (lookup_lt f parent tag found)]
    simp [type]
  · cases element <;> simp [childTag]

theorem append_wellFormed (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag)
    (type : tag.element = .vector element) :
    (f.appendChild parent tag element).wellFormed = true := by
  unfold Forest.wellFormed
  apply List.all_eq_true.mpr
  intro i member
  have inside : i < f.objects.length + 1 := by
    have := List.mem_range.mp member
    rwa [append_length] at this
  unfold Forest.check
  by_cases fresh : i = f.objects.length
  · subst i
    rw [append_fresh]
    simpa using append_child_ok f parent tag element valid found type
  · have bound : i < f.objects.length := by omega
    by_cases same : parent = i
    · subst i
      rw [append_parent f parent tag element bound]
      simpa using append_parent_ok f parent tag element valid found type
    · rw [append_old f parent tag element i bound same]
      cases hi : f.lookup i with
      | none => rfl
      | some node =>
        simpa using tagOK_mono f _ (append_extends f parent tag element found) i node
          (wellFormed_tag f i node valid hi)

theorem rootOwner_extends (f g : Forest) (ext : Extends f g) (valid : f.wellFormed = true)
    (owner : Nat) (tag : Tag) (found : f.lookup owner = some tag) :
    g.rootOwner owner = f.rootOwner owner := by
  induction owner using Nat.strongRecOn generalizing tag with
  | ind i ih =>
    obtain ⟨next, hg, _, hp, _, _⟩ := ext i tag found
    cases parent : tag.parent with
    | none => rw [root_runs g i next hg (hp.trans parent), root_runs f i tag found parent]
    | some p =>
      have good := (wellFormed_tag f i tag valid found).2.2.1
      simp only [Forest.parentOK, parent] at good
      obtain ⟨earlier, _, rest⟩ := good
      cases ancestor : f.lookup p with
      | none => simp [ancestor] at rest
      | some origin =>
        rw [child_runs g i p next hg (hp.trans parent) earlier,
          child_runs f i p tag found parent earlier]
        exact ih p earlier origin ancestor

theorem context_extends (f g : Forest) (ext : Extends f g) (valid : f.wellFormed = true)
    (owner : Nat) (tag : Tag) (found : f.lookup owner = some tag) :
    g.context owner = f.context owner := by
  have rootEq := rootOwner_extends f g ext valid owner tag found
  cases root : f.rootOwner owner with
  | none => simp [Forest.context, rootEq, root]
  | some r =>
    obtain ⟨rt, hf, _⟩ := rootOwner_is_root f owner r root
    obtain ⟨gt, hg, _, _, hs, _⟩ := ext r rt hf
    simp [Forest.context, rootEq, root, hf, hg, hs]

end Proofs.CppForestAppend
