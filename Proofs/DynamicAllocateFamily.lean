import Proofs.DynamicAllocateModels

namespace Proofs.DynamicAllocateFamily
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedConstruct Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicAllocateModels

def grown (f : Frame) (next : State) (wr : Bool) (children : Nat) : Frame :=
  {f with state := next,rootWritable := f.rootWritable ++ [wr] ++ List.replicate children false}

theorem Family.remeasured {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) : Family params h f (resources f) :=
  ⟨family.valid,family.models,family.lengths,family.bindings,family.flags,family.permissions,family.views,measured_resources f⟩

theorem Family.fresh {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) : h f.state.storage.objects.length = none := by
  cases found : h f.state.storage.objects.length with
  | none => rfl
  | some view => have bound := (family.models _ view found).bound; omega

theorem Family.allocated {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : State) (wr : Bool) (children : Nat) (view : View)
    (freshModel : Models next f.state.storage.objects.length view)
    (preserved : ∀ owner v, Models f.state owner v → Models next owner v)
    (count : next.forest.objects.length = f.state.forest.objects.length+1+children) :
    Family params (put h f.state.storage.objects.length view) (grown f next wr children) (resources (grown f next wr children)) := by
  refine ⟨freshModel.valid,heap_put next h _ view freshModel (fun owner _ v found => preserved owner v (family.models owner v found)),?_,family.bindings,?_,family.permissions,?_,measured_resources _⟩
  · change (f.rootWritable ++ [wr] ++ List.replicate children false).length = next.forest.objects.length
    simp [family.lengths,count,Nat.add_assoc]; omega
  · intro p member
    have found := family.flags p member
    change ((f.rootWritable ++ [wr]) ++ List.replicate children false)[p.owner]? = _
    rw [List.append_assoc]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found
  · intro p member
    obtain ⟨v,found,element,scope⟩ := family.views p member
    have bound := (family.models p.owner v found).bound
    have different : p.owner ≠ f.state.storage.objects.length := by omega
    exact ⟨v,by simp [put,different,found],element,scope⟩

theorem rows {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : State) (ty : Ty) (scope count : Nat) (wr : Bool)
    (run : f.state.constructRows ty scope count = some next) :
    Family params (put h f.state.storage.objects.length (.rows ty scope (rowIds f.state.storage.objects.length count) 0 (List.replicate count [])))
      (grown f next wr count) (resources (grown f next wr count)) := by
  apply Family.allocated family next wr count _ (rows_new f.state next ty scope count run) (rows_old f.state next ty scope count run)
  rw [(wellFormed_parts next (constructRows_state_wellFormed f.state ty scope count next run)).1,
    constructRows_objects_length f.state ty scope count next run,(wellFormed_parts f.state family.valid).1]

theorem empty {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : State) (ty : Ty) (scope : Nat) (wr : Bool)
    (run : f.state.declareVector ty scope = some next) :
    Family params (put h f.state.storage.objects.length (.flat ty scope [])) (grown f next wr 0) (resources (grown f next wr 0)) := by
  apply Family.allocated family next wr 0 _ (empty_new f.state next ty scope run) (empty_old f.state next ty scope run)
  rw [(wellFormed_parts next (declareVector_wellFormed f.state ty scope next run)).1,
    declareVector_objects_length f.state ty scope next run,(wellFormed_parts f.state family.valid).1]

theorem filled {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : State) (ty : Ty) (scope count : Nat) (value : Int) (wr : Bool)
    (run : f.state.fillVector ty scope count value = some next) :
    Family params (put h f.state.storage.objects.length (.flat ty scope (List.replicate count value)))
      (grown f next wr 0) (resources (grown f next wr 0)) := by
  apply Family.allocated family next wr 0 _ (filled_new f.state next ty scope count value run) (filled_old f.state next ty scope count value run)
  rw [(wellFormed_parts next (fillVector_wellFormed f.state ty scope count value next run)).1,
    fillVector_objects_length f.state ty scope count value next run,(wellFormed_parts f.state family.valid).1]

-- Bind the newly allocated root without assuming bindRoot success.
theorem register {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (owner : Nat) (view : View) (found : h owner = some view)
    (wr : Bool) (flag : f.rootWritable[owner]? = some wr) :
    ∃ next, f.bindRoot owner view.element view.scope wr = some (next,f.bindings.length) ∧
      Family (params ++ [⟨f.bindings.length,owner,view.element,view.scope,wr,wr⟩]) h next m := by
  let s : NState := ⟨⟨[],[],0,0,0⟩,f,[],view.scope,0⟩
  have run := DynamicBindExists.root_bind (s := s) family owner view.scope view.element wr wr view found rfl rfl flag (fun h => h)
  obtain ⟨maximum,actual,_,_,post⟩ := DynamicFamilyInit.bind_root (s := s) family owner view.scope view.element wr view found rfl rfl _ f.bindings.length run
  have same : maximum = wr := Option.some.inj (actual.symm.trans flag)
  subst maximum
  exact ⟨_,run,post⟩

theorem new_flag {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : State) (wr : Bool) (children : Nat) :
    (grown f next wr children).rootWritable[f.state.storage.objects.length]? = some wr := by
  have lengths := family.lengths.trans (wellFormed_parts f.state family.valid).1
  rw [← lengths]
  simp [grown]

end Proofs.DynamicAllocateFamily
