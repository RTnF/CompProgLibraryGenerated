import Proofs.DynamicScopeAuto

namespace Proofs.DynamicFamilyInit
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedFacts
open Proofs.CppRootModel Proofs.CppRowsFrame Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes

def Compatible (h : Heap) : Resolved → Prop
  | .vector owner scope ty _ => ∃ v, h owner = some v ∧ v.element = .integer ty ∧ v.scope = scope
  | .nestedRoot owner scope ty _ => ∃ v, h owner = some v ∧ v.element = .vector (.integer ty) ∧ v.scope = scope
  | _ => True

def grant (flags : List Bool) (slot : Nat) : Resolved → Option Parameter
  | .vector owner scope ty wr => some ⟨slot,owner,.integer ty,scope,wr,flags[owner]?.getD false⟩
  | .nestedRoot owner scope ty wr => some ⟨slot,owner,.vector (.integer ty),scope,wr,flags[owner]?.getD false⟩
  | _ => none

def vectorCount : Resolved → Nat
  | .vector _ _ _ _ | .nestedRoot _ _ _ _ | .vectorChild _ _ _ _ => 1
  | _ => 0

def describe (flags : List Bool) (slot : Nat) : List Resolved → List Parameter
  | [] => []
  | r::rs => (grant flags slot r).toList ++ describe flags (slot+vectorCount r) rs

theorem empty (h : Heap) (f : Frame) (valid : f.state.wellFormed = true)
    (models : HeapModels f.state h) (lengths : f.rootWritable.length = f.state.forest.objects.length) :
    Family [] h f (resources f) :=
  ⟨valid,models,lengths,by simp,by simp,by simp,by simp,measured_resources f⟩

-- Binding a root changes the reference table only. The maximum grant belongs
-- to the owner and is retained when a new parameter has a const view.
theorem bind_root {params : List Parameter} {h : Heap} {s : NState} {m : Resources}
    (family : Family params h s.frame m) (owner scope : Nat) (element : Element) (wr : Bool)
    (view : View) (lookup : h owner = some view) (typed : view.element = element) (scopedView : view.scope = scope)
    (next : Frame) (index : Nat) (run : s.frame.bindRoot owner element scope wr = some (next,index)) :
    ∃ maximum, s.frame.rootWritable[owner]? = some maximum ∧
      index = s.frame.bindings.length ∧ next = (s.frame.addBinding ⟨owner,element,wr,.root scope⟩).1 ∧
      Family (params ++ [⟨index,owner,element,scope,wr,maximum⟩]) h next m := by
  unfold Frame.bindRoot at run
  cases obj : s.frame.object owner element with
  | none => simp [obj] at run
  | some pair =>
    obtain ⟨buffer,tag⟩ := pair
    cases max : s.frame.maximum owner with
    | none => simp [obj,max] at run
    | some maximum =>
      simp only [obj,max,Bind.bind,Option.bind] at run
      split at run
      · rename_i good
        obtain ⟨_,_,found,_⟩ := object_buffer s.frame owner element buffer tag obj
        have rooted := CppVectorOwnership.root_runs s.frame.state.forest owner tag found good.1
        have flag : s.frame.rootWritable[owner]? = some maximum := by
          simpa [Frame.maximum,family.lengths,rooted] using max
        have equal := Option.some.inj run
        have indexEq : index = s.frame.bindings.length := (congrArg Prod.snd equal).symm
        have frameEq : next = (s.frame.addBinding ⟨owner,element,wr,.root scope⟩).1 := (congrArg Prod.fst equal).symm
        subst index
        subst next
        refine ⟨maximum,flag,rfl,rfl,?_⟩
        refine ⟨family.valid,family.models,family.lengths,?_,?_,?_,?_,⟨family.measured.live,family.measured.work,family.measured.peak,family.measured.count,family.measured.base⟩⟩
        · intro p member
          rcases List.mem_append.mp member with old | fresh
          · change (s.frame.bindings ++ _)[p.slot]? = _
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings p old)).1]
            exact family.bindings p old
          · simp only [List.mem_singleton] at fresh
            subst p
            simp [Frame.addBinding,Parameter.binding]
        · intro p member
          rcases List.mem_append.mp member with old | fresh
          · exact family.flags p old
          · simp only [List.mem_singleton] at fresh
            subst p; exact flag
        · intro p member
          rcases List.mem_append.mp member with old | fresh
          · exact family.permissions p old
          · simp only [List.mem_singleton] at fresh
            subst p; exact good.2.2
        · intro p member
          rcases List.mem_append.mp member with old | fresh
          · exact family.views p old
          · simp only [List.mem_singleton] at fresh
            subst p; exact ⟨view,lookup,typed,scopedView⟩
      · contradiction

theorem bind_one {params : List Parameter} {h : Heap} {s t : NState} {m : Resources}
    (family : Family params h s.frame m) (r : Resolved) (compatible : Compatible h r)
    (run : bindOne s r = some t) :
    Family (params ++ (grant s.frame.rootWritable s.frame.bindings.length r).toList) h t.frame m ∧
      t.frame.state = s.frame.state ∧ t.frame.rootWritable = s.frame.rootWritable ∧
      t.frame.bindings.length = s.frame.bindings.length+vectorCount r ∧ t.scope = s.scope := by
  cases r with
  | scalar ty wr value =>
    cases bound : Proofs.CppState.bindArgument s.scalars ⟨ty,false,wr⟩ (.value value) with
    | none => simp [bindOne,bound] at run
    | some scalars =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t
      exact ⟨by simpa [grant] using family,rfl,rfl,by simp [vectorCount],rfl⟩
  | scalarAddress ty address wr =>
    cases bound : Proofs.CppState.bindArgument s.scalars ⟨ty,true,wr⟩ (.reference address) with
    | none => simp [bindOne,bound] at run
    | some scalars =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t
      exact ⟨by simpa [grant] using family,rfl,rfl,by simp [vectorCount],rfl⟩
  | vectorChild owner address ty wr =>
    cases checked : (s.frame.addBinding ⟨owner,.integer ty,wr,.child address⟩).1.resolve
        (s.frame.addBinding ⟨owner,.integer ty,wr,.child address⟩).2 (.integer ty) with
    | none => simp [bindOne,checked] at run
    | some pair =>
      simp only [bindOne,checked,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t
      refine ⟨?_,rfl,rfl,by simp [Frame.addBinding,vectorCount],rfl⟩
      simp only [grant,Option.toList,List.append_nil]
      refine ⟨family.valid,family.models,family.lengths,?_,family.flags,family.permissions,family.views,
        ⟨family.measured.live,family.measured.work,family.measured.peak,family.measured.count,family.measured.base⟩⟩
      intro p member
      change (s.frame.bindings ++ _)[p.slot]? = _
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings p member)).1]
      exact family.bindings p member
  | vector owner scope ty wr | nestedRoot owner scope ty wr =>
    obtain ⟨view,lookup,typed,scopedView⟩ := compatible
    cases bound : s.frame.bindRoot owner view.element scope wr with
    | none => rw [typed] at bound; simp [bindOne,bound] at run
    | some pair =>
      rw [typed] at bound
      obtain ⟨frame,index⟩ := pair
      obtain ⟨maximum,flag,indexEq,frameEq,after⟩ := bind_root family owner scope _ wr view lookup typed scopedView frame index bound
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t
      refine ⟨?_,?_,?_,?_,rfl⟩
      · simpa [grant,flag,indexEq] using after
      · rw [frameEq]; rfl
      · rw [frameEq]; rfl
      · simp [frameEq,Frame.addBinding,vectorCount]

theorem bind_all {params : List Parameter} {h : Heap} {s t : NState} {m : Resources}
    (family : Family params h s.frame m) (rs : List Resolved) (compatible : ∀ r ∈ rs, Compatible h r)
    (run : bindAll s rs = some t) :
    Family (params ++ describe s.frame.rootWritable s.frame.bindings.length rs) h t.frame m ∧
      t.frame.state = s.frame.state ∧ t.frame.rootWritable = s.frame.rootWritable ∧ t.scope = s.scope := by
  induction rs generalizing params s with
  | nil =>
    simp only [bindAll,Option.some.injEq] at run
    subst t
    exact ⟨by simpa [describe] using family,rfl,rfl,rfl⟩
  | cons r rs ih =>
    have head := compatible r (by simp)
    have tail : ∀ q ∈ rs, Compatible h q := by
      intro q member
      exact compatible q (List.mem_cons_of_mem r member)
    cases first : bindOne s r with
    | none => simp [bindAll,first] at run
    | some next =>
      have rest : bindAll next rs = some t := by simpa [bindAll,first] using run
      obtain ⟨after,state,flags,count,scope⟩ := bind_one family r head first
      obtain ⟨final,lastState,lastFlags,lastScope⟩ := ih after tail rest
      refine ⟨?_,lastState.trans state,lastFlags.trans flags,lastScope.trans scope⟩
      simpa [describe,flags,count,List.append_assoc] using final

end Proofs.DynamicFamilyInit
