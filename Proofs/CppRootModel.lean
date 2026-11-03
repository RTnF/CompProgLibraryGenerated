import Proofs.CppRowsFrame

namespace Proofs.CppRootModel
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct Proofs.CppNestedFacts
open Proofs.CppRowsGraph Proofs.CppRowsContents

inductive View where
  | flat (ty : Ty) (scope : Nat) (values : List Int)
  | rows (ty : Ty) (scope : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
  deriving DecidableEq, Repr

def View.element : View → Element
  | .flat ty _ _ => .integer ty
  | .rows ty _ _ _ _ => .vector (.integer ty)

def View.scope : View → Nat
  | .flat _ scope _ | .rows _ scope _ _ _ => scope

structure Flat (s : State) (root : Nat) (ty : Ty) (scope : Nat) (values : List Int) : Prop where
  valid : s.wellFormed = true
  tag : s.forest.lookup root = some ⟨.integer ty,none,some scope,[]⟩
  buffer : ∃ b, s.storage.lookup root = some b ∧ b.items = values.map Value.integer

def Models (s : State) (root : Nat) : View → Prop
  | .flat ty sc vs => Flat s root ty sc vs
  | .rows ty sc ids epoch vs => Data s root ty sc ids epoch vs

theorem Models.valid {s : State} {root : Nat} {v : View} (model : Models s root v) :
    s.wellFormed = true := by
  cases v with
  | flat ty sc vs => exact Flat.valid model
  | rows ty sc ids epoch vs => exact model.rows.valid

theorem Models.root_tag {s : State} {root : Nat} {v : View} (model : Models s root v) :
    ∃ t, s.forest.lookup root = some t ∧ t.element = v.element ∧ t.parent = none ∧ t.scope = some v.scope := by
  cases v with
  | flat ty sc vs => exact ⟨_,model.tag,rfl,rfl,rfl⟩
  | rows ty sc ids epoch vs => exact ⟨_,model.rows.rootTag,rfl,rfl,rfl⟩

theorem Models.bound {s : State} {root : Nat} {v : View} (model : Models s root v) :
    root < s.storage.objects.length := by
  cases v with
  | flat ty sc vs =>
    obtain ⟨b,found,_⟩ := model.buffer
    exact lookup_bound s.storage root b found
  | rows ty sc ids epoch vs =>
    obtain ⟨b,found,_,_⟩ := model.rows.buffer
    exact lookup_bound s.storage root b found

theorem root_ne_child (s : State) (root owner : Nat) (rt ct : Tag)
    (rootTag : s.forest.lookup root = some rt) (rootParent : rt.parent = none)
    (childTag : s.forest.lookup owner = some ct) (parent : Nat) (childParent : ct.parent = some parent) :
    root ≠ owner := by
  intro same
  subst owner
  have tags : rt = ct := Option.some.inj (rootTag.symm.trans childTag)
  rw [tags,childParent] at rootParent
  contradiction

theorem children_distinct (s : State) (owner other parent root : Nat) (ct ot : Tag)
    (child : s.forest.lookup owner = some ct) (cp : ct.parent = some parent)
    (otherChild : s.forest.lookup other = some ot) (op : ot.parent = some root)
    (different : parent ≠ root) : owner ≠ other := by
  intro same
  subst other
  have tags : ct = ot := Option.some.inj (child.symm.trans otherChild)
  have parents := congrArg Tag.parent tags
  rw [cp,op] at parents
  exact different (Option.some.inj parents)

-- Adding a new child modifies only its own root's logical view. All existing
-- roots retain their contents, even if the tracked root's parent reallocates.
theorem append_other (s : State) (parent root : Nat) (pt : Tag) (ty : Ty)
    (old : Buffer Value) (r : Result Value Unit) (v : View)
    (model : Models s root v) (different : parent ≠ root)
    (parentFound : s.forest.lookup parent = some pt) (parentless : pt.parent = none)
    (valid : (CppAppendRow.added s parent pt ty old r).wellFormed = true) :
    Models (CppAppendRow.added s parent pt ty old r) root v := by
  have lengths := (wellFormed_parts s model.valid).1
  have rootBound := model.bound
  have rootTag := CppForestAppend.append_old s.forest parent pt (.integer ty) root (by omega) different
  have rootBuffer := CppAppendRow.storage_old s parent pt ty old r root rootBound different
  cases v with
  | flat t sc vs =>
    refine ⟨valid,rootTag.trans model.tag,?_⟩
    obtain ⟨b,hb,hi⟩ := model.buffer
    exact ⟨b,rootBuffer.trans hb,hi⟩
  | rows t sc ids epoch vs =>
    refine ⟨⟨valid,rootTag.trans model.rows.rootTag,?_⟩,model.length,?_⟩
    · obtain ⟨b,hb,he,hi⟩ := model.rows.buffer
      exact ⟨b,rootBuffer.trans hb,he,hi⟩
    · intro k owner lookup
      obtain ⟨b,hb,hi⟩ := model.contents k owner lookup
      obtain ⟨buffer,obj,_,_⟩ := row_object (⟨s,[],[]⟩ : Frame) root t sc ids epoch k owner model.rows lookup
      have objectFacts := object_buffer (⟨s,[],[]⟩ : Frame) owner (.integer t) buffer _ obj
      have distinct := root_ne_child s parent owner pt _ parentFound parentless objectFacts.2.2.1 root rfl
      exact ⟨b,(CppAppendRow.storage_old s parent pt ty old r owner (lookup_bound s.storage owner b hb) distinct).trans hb,hi⟩

-- A child buffer cannot be another root or a child of a different root. These
-- separation facts follow from tags; no consecutive-ID assumption is used.
theorem updated_other (f : Frame) (owner parent root : Nat) (ct : Tag)
    (old : Buffer Value) (r : Result Value Unit) (v : View)
    (model : Models f.state root v) (different : parent ≠ root)
    (childTag : f.state.forest.lookup owner = some ct) (cp : ct.parent = some parent)
    (valid : (f.updated owner old r).state.wellFormed = true) :
    Models (f.updated owner old r).state root v := by
  obtain ⟨rt,rf,_,rp,_⟩ := model.root_tag
  have distinct := (root_ne_child f.state root owner rt ct rf rp childTag parent cp).symm
  have rootBuffer := CppNestedOps.updated_lookup_other f owner root old r distinct
  cases v with
  | flat ty sc vs =>
    refine ⟨valid,model.tag,?_⟩
    obtain ⟨b,hb,hi⟩ := model.buffer
    exact ⟨b,rootBuffer.trans hb,hi⟩
  | rows ty sc ids epoch vs =>
    refine ⟨⟨valid,model.rows.rootTag,?_⟩,model.length,?_⟩
    · obtain ⟨b,hb,he,hi⟩ := model.rows.buffer
      exact ⟨b,rootBuffer.trans hb,he,hi⟩
    · intro k child lookup
      obtain ⟨b,hb,hi⟩ := model.contents k child lookup
      obtain ⟨buffer,obj,_,_⟩ := row_object f root ty sc ids epoch k child model.rows lookup
      have facts := object_buffer f child (.integer ty) buffer _ obj
      have disjoint := children_distinct f.state owner child parent root ct _ childTag cp facts.2.2.1 rfl different
      exact ⟨b,(CppNestedOps.updated_lookup_other f owner child old r disjoint).trans hb,hi⟩

theorem append_frame_effect (f next : Frame) (slot root : Nat) (ty : Ty)
    (binding : Binding) (buffer : Buffer Value) (view : View)
    (model : Models f.state root view)
    (resolved : f.resolve slot (.vector (.integer ty)) = some (binding,buffer))
    (owner : binding.owner = root) (ran : f.appendRow slot ty = some next) :
    next.bindings = f.bindings ∧ next.rootWritable = f.rootWritable ++ [false] ∧
      ∀ other v, root ≠ other → Models f.state other v → Models next.state other v := by
  unfold Frame.appendRow at ran
  simp only [resolved,Bind.bind,Option.bind] at ran
  split at ran
  · cases step : f.state.appendRow binding.owner ty with
    | none => simp [step] at ran
    | some state =>
      simp only [step,Option.some.injEq] at ran
      subst next
      refine ⟨rfl,rfl,?_⟩
      intro other v different otherModel
      rw [owner] at step
      have valid := CppAppendRow.appendRow_valid f.state state root ty step
      obtain ⟨old,pt,r,_,_,ptFound,_,_,stateEq⟩ := CppAppendRow.appendRow_inv f.state state root ty step
      obtain ⟨rt,rtFound,_,rootless,_⟩ := model.root_tag
      have equal : pt = rt := Option.some.inj (ptFound.symm.trans rtFound)
      rw [stateEq] at valid ⊢
      exact append_other f.state root other pt ty old r v otherModel different ptFound
        (by rw [equal]; exact rootless) valid
  · contradiction

-- Keying logical contents by owner makes aliases share a single view.
abbrev Heap := Nat → Option View

def put (h : Heap) (root : Nat) (v : View) : Heap :=
  fun owner => if owner = root then some v else h owner

def HeapModels (s : State) (h : Heap) : Prop := ∀ root v, h root = some v → Models s root v

theorem heap_put (s : State) (h : Heap) (root : Nat) (v : View)
    (changed : Models s root v) (others : ∀ other, other ≠ root → ∀ old, h other = some old → Models s other old) :
    HeapModels s (put h root v) := by
  intro other old lookup
  by_cases same : other = root
  · subst other
    simp [put] at lookup
    subst old
    exact changed
  · exact others other same old (by simpa [put,same] using lookup)

end Proofs.CppRootModel
