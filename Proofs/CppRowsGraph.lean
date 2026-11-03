import Proofs.CppNestedRows
import Proofs.CppAppendRow

namespace Proofs.CppRowsGraph
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppNestedFacts

def tag (ty : Ty) (sc : Nat) (ids : List Nat) : Tag :=
  ⟨.vector (.integer ty),none,some sc,ids⟩

-- The row IDs and the current parent epoch are explicit. Neither contiguous
-- allocation nor the absence of earlier reallocations is required.
structure Rows (s : State) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) : Prop where
  valid : s.wellFormed = true
  rootTag : s.forest.lookup root = some (tag ty sc ids)
  buffer : ∃ b, s.storage.lookup root = some b ∧ b.epoch = epoch ∧ b.items = ids.map Value.child

theorem of_legacy (s : State) (root : Nat) (ty : Ty) (count sc : Nat)
    (g : CppNestedRows.RootGraph s root ty count sc) :
    Rows s root ty sc (rowIds root count) 0 := ⟨g.valid,g.tag,g.buffer⟩

theorem root_object (f : Frame) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat)
    (g : Rows f.state root ty sc ids epoch) :
    ∃ b, f.object root (.vector (.integer ty)) = some (b,tag ty sc ids) ∧
      f.state.storage.lookup root = some b ∧ b.epoch = epoch ∧ b.items = ids.map Value.child := by
  obtain ⟨b, found, he, hi⟩ := g.buffer
  exact ⟨b,object_runs f root _ b _ g.valid found g.rootTag rfl,found,he,hi⟩

theorem row_object (f : Frame) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch k owner : Nat)
    (g : Rows f.state root ty sc ids epoch) (lookup : ids[k]? = some owner) :
    ∃ b, f.object owner (.integer ty) = some (b,⟨.integer ty,some root,none,[]⟩) ∧
      f.state.storage.lookup owner = some b ∧ root < owner := by
  obtain ⟨rb, _, found, _, _⟩ := root_object f root ty sc ids epoch g
  have facts := rows_facts f.state root (tag ty sc ids) rb ty g.valid g.rootTag found rfl
  obtain ⟨b, ht, earlier, hb⟩ := facts.2.2.2 owner (List.mem_of_getElem? lookup)
  exact ⟨b,object_runs f owner _ b _ g.valid hb ht rfl,hb,earlier⟩

def binding (root : Nat) (ty : Ty) (epoch k owner : Nat) (writable : Bool) : Binding :=
  ⟨owner,.integer ty,writable,.child ⟨root,epoch,k⟩⟩

theorem maximum_root (f : Frame) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat)
    (g : Rows f.state root ty sc ids epoch) (maximum : Bool)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[root]? = some maximum) : f.maximum root = some maximum := by
  exact maximum_runs f root root maximum lengths
    (CppVectorOwnership.root_runs f.state.forest root _ g.rootTag rfl) flag

theorem maximum_row (f : Frame) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch k owner : Nat)
    (g : Rows f.state root ty sc ids epoch) (lookup : ids[k]? = some owner) (maximum : Bool)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[root]? = some maximum) : f.maximum owner = some maximum := by
  obtain ⟨b, object, _, earlier⟩ := row_object f root ty sc ids epoch k owner g lookup
  obtain ⟨_, _, ht, _⟩ := object_buffer f owner _ b _ object
  have rooted : f.state.forest.rootOwner owner = some root := by
    rw [CppVectorOwnership.child_runs f.state.forest owner root _ ht rfl earlier]
    exact CppVectorOwnership.root_runs f.state.forest root _ g.rootTag rfl
  exact maximum_runs f owner root maximum lengths rooted flag

theorem row_read (f : Frame) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch k owner : Nat)
    (g : Rows f.state root ty sc ids epoch) (lookup : ids[k]? = some owner) :
    ∃ b, f.object root (.vector (.integer ty)) = some (b,tag ty sc ids) ∧
      readRef b (accepts (.vector (.integer ty))) ⟨root,epoch,k⟩ =
        some ⟨b,.child owner,1,b.capacity+2⟩ ∧
      CppVector.elementRef b (accepts (.vector (.integer ty))) k = some ⟨root,epoch,k⟩ := by
  obtain ⟨b, object, found, he, hi⟩ := root_object f root ty sc ids epoch g
  have facts := rows_facts f.state root (tag ty sc ids) b ty g.valid g.rootTag found rfl
  have valid : b.Valid (accepts (.vector (.integer ty))) := facts.2.1
  have item : b.items[k]? = some (.child owner) := by simp [hi,List.getElem?_map,lookup]
  have read := readRef_runs b (accepts (.vector (.integer ty))) k (.child owner) valid item
  have bound : (k : Int).toNat < b.items.length := by
    have := (List.getElem?_eq_some_iff.mp lookup).1
    simpa [hi] using this
  have captured := elementRef_runs b (accepts (.vector (.integer ty))) k valid (by omega) bound
  refine ⟨b,object,?_,?_⟩
  · simpa [facts.1,he] using read
  · simpa [facts.1,he] using captured

theorem child_row (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat)
    (epoch k owner : Nat) (g : Rows f.state root ty sc ids epoch) (lookup : ids[k]? = some owner)
    (writable maximum : Bool)
    (hb : f.bindings[slot]? = some ⟨root,.vector (.integer ty),writable,.root sc⟩)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[root]? = some maximum) (permission : writable = true → maximum = true) :
    f.child slot (.integer ty) k = some (f.addBinding (binding root ty epoch k owner writable)) := by
  obtain ⟨rb, ro, read, captured⟩ := row_read f root ty sc ids epoch k owner g lookup
  have resolved := resolve_root f slot (.vector (.integer ty)) ⟨root,.vector (.integer ty),writable,.root sc⟩ sc rb (tag ty sc ids) maximum hb
    rfl rfl ro rfl rfl (maximum_root f root ty sc ids epoch g maximum lengths flag) permission
  obtain ⟨b, bo, _, _⟩ := row_object f root ty sc ids epoch k owner g lookup
  exact child_runs f slot (.integer ty) k _ rb ⟨root,epoch,k⟩ _ owner b _ resolved captured read rfl bo rfl

theorem resolve_row (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat)
    (epoch k owner : Nat) (g : Rows f.state root ty sc ids epoch) (lookup : ids[k]? = some owner)
    (writable maximum : Bool)
    (hb : f.bindings[slot]? = some (binding root ty epoch k owner writable))
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[root]? = some maximum) (permission : writable = true → maximum = true) :
    ∃ b, f.resolve slot (.integer ty) = some (binding root ty epoch k owner writable,b) ∧
      f.state.storage.lookup owner = some b := by
  obtain ⟨rb, ro, read, _⟩ := row_read f root ty sc ids epoch k owner g lookup
  obtain ⟨b, bo, found, _⟩ := row_object f root ty sc ids epoch k owner g lookup
  exact ⟨b, resolve_child f slot (.integer ty) (binding root ty epoch k owner writable) ⟨root,epoch,k⟩
    rb (tag ty sc ids) _ owner b _ maximum hb rfl rfl rfl ro read rfl bo
    (maximum_row f root ty sc ids epoch k owner g lookup maximum lengths flag) permission, found⟩

theorem appendRow_rows (s : State) (root : Nat) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat)
    (g : Rows s root ty sc ids epoch) (old : Buffer Value) (found : s.storage.lookup root = some old)
    (room : old.items.length < old.limit) :
    ∃ r, s.appendRow root ty = some (CppAppendRow.added s root (tag ty sc ids) ty old r) ∧
      Rows (CppAppendRow.added s root (tag ty sc ids) ty old r) root ty sc
        (ids ++ [s.storage.objects.length]) r.buffer.epoch := by
  obtain ⟨r, run, valid, items, _, _⟩ :=
    CppAppendRow.appendRow_runs s root (tag ty sc ids) ty old g.valid found g.rootTag rfl room
  have lengths := (wellFormed_parts s g.valid).1
  have inside := CppVectorStore.lookup_bound s.storage root old found
  have ht := CppForestAppend.append_parent s.forest root (tag ty sc ids) (.integer ty) (by omega)
  rw [lengths] at ht
  obtain ⟨b, hb, _, hi⟩ := g.buffer
  have same : b = old := Option.some.inj (hb.symm.trans found)
  subst b
  refine ⟨r,run,valid,ht,?_⟩
  refine ⟨r.buffer,CppAppendRow.storage_parent s root (tag ty sc ids) ty old r inside,rfl,?_⟩
  simpa [hi,List.map_append] using items

-- Changes to a different buffer preserve the parent identity and epoch.
-- Validity is supplied by the particular mutating operation's success theorem.
theorem updated_rows (f : Frame) (root owner : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (old : Buffer Value) (result : Result Value Unit)
    (g : Rows f.state root ty sc ids epoch) (different : owner ≠ root)
    (valid : (f.updated owner old result).state.wellFormed = true) :
    Rows (f.updated owner old result).state root ty sc ids epoch := by
  refine ⟨valid,g.rootTag,?_⟩
  obtain ⟨b,found,he,hi⟩ := g.buffer
  exact ⟨b,(CppNestedOps.updated_lookup_other f owner root old result different).trans found,he,hi⟩

end Proofs.CppRowsGraph
