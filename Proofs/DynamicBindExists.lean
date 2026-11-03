import Proofs.DynamicBoundArguments

namespace Proofs.DynamicBindExists
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedCall
open Proofs.CppNestedFacts Proofs.CppRootModel Proofs.CppRowsFrame Proofs.MultiVecDynamic Proofs.DynamicFamilyInit
open Proofs.DynamicBoundArguments

theorem root_bind {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (owner scope : Nat) (expected : Element) (wr maximum : Bool)
    (view : View) (lookup : h owner = some view) (typed : view.element = expected) (scopedView : view.scope = scope)
    (flag : s.frame.rootWritable[owner]? = some maximum) (permission : wr = true → maximum = true) :
    s.frame.bindRoot owner expected scope wr = some (s.frame.addBinding ⟨owner,expected,wr,.root scope⟩) := by
  obtain ⟨buffer,tag,obj,found,parent,sc⟩ := DynamicResolveRoots.root_object s.frame owner view (family.models owner view lookup)
  have object : s.frame.object owner expected = some (buffer,tag) := by rw [← typed]; exact obj
  have maximum := maximum_runs s.frame owner owner maximum family.lengths
    (CppVectorOwnership.root_runs s.frame.state.forest owner tag found parent) flag
  have context : tag.scope = some scope := by rw [scopedView] at sc; exact sc
  simp only [Frame.bindRoot,object,maximum,Bind.bind,Option.bind]
  rw [if_pos ⟨parent,context,permission⟩]

theorem one_exists {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (r : Resolved) (bound : Boundable h s r) : ∃ t, bindOne s r = some t := by
  cases r with
  | scalar ty wr value =>
    change ty.valid value = true at bound
    let sc : Proofs.CppState.State := {s.scalars with memory := s.scalars.memory ++ [⟨ty,value⟩],bindings := s.scalars.bindings ++ [⟨s.scalars.memory.length,wr⟩]}
    refine ⟨({s with scalars := sc.observe 0,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : NState).observe,?_⟩
    simp [bindOne,Proofs.CppState.bindArgument,bound,sc]
  | scalarAddress ty address wr =>
    obtain ⟨cell,found,typed,valid⟩ := bound
    let sc : Proofs.CppState.State := {s.scalars with bindings := s.scalars.bindings ++ [⟨address,wr⟩]}
    refine ⟨({s with scalars := sc.observe 0,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : NState).observe,?_⟩
    simp [bindOne,Proofs.CppState.bindArgument,found,typed,valid,sc]
  | vector owner scope ty wr =>
    obtain ⟨view,maximum,lookup,typed,scopedView,flag,permission⟩ := bound
    have run := root_bind family owner scope (.integer ty) wr maximum view lookup typed scopedView flag permission
    refine ⟨({s with frame := (s.frame.addBinding ⟨owner,.integer ty,wr,.root scope⟩).1,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).observe,?_⟩
    simp [bindOne,run,Frame.addBinding]
  | vectorChild owner address ty wr =>
    obtain ⟨buffer,tag,maximum,header,object,max,permission⟩ := bound
    let binding : Binding := ⟨owner,.integer ty,wr,.child address⟩
    let added := s.frame.addBinding binding
    have header' : added.1.headerOwner binding = some owner := header
    have object' : added.1.object owner (.integer ty) = some (buffer,tag) := object
    have max' : added.1.maximum owner = some maximum := max
    have found : added.1.bindings[added.2]? = some binding := by simp [added,Frame.addBinding]
    have checked : added.1.resolve added.2 (.integer ty) = some (binding,buffer) := by
      simp only [Frame.resolve,found,header',object',max',Bind.bind,Option.bind]
      exact if_pos ⟨rfl,rfl,permission⟩
    refine ⟨({s with frame := added.1,slots := s.slots ++ [.vector added.2]} : NState).observe,?_⟩
    change (added.1.resolve added.2 (.integer ty)).bind _ = _
    rw [checked]
    rfl
  | nestedRoot owner scope ty wr =>
    obtain ⟨view,maximum,lookup,typed,scopedView,flag,permission⟩ := bound
    have run := root_bind family owner scope (.vector (.integer ty)) wr maximum view lookup typed scopedView flag permission
    refine ⟨({s with frame := (s.frame.addBinding ⟨owner,.vector (.integer ty),wr,.root scope⟩).1,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).observe,?_⟩
    simp [bindOne,run,Frame.addBinding]

theorem scalar_memory (s t : Proofs.CppState.State) (p : Proofs.CppState.Parameter) (a : Proofs.CppState.Argument)
    (run : Proofs.CppState.bindArgument s p a = some t) : ∃ extra, t.memory = s.memory ++ extra := by
  cases a with
  | value v =>
    simp only [Proofs.CppState.bindArgument] at run
    split at run
    · contradiction
    · have same := Option.some.inj run
      subst t
      exact ⟨[⟨p.type,v⟩],rfl⟩
  | reference address =>
    cases found : s.memory[address]? with
    | none => simp [Proofs.CppState.bindArgument,found] at run
    | some cell =>
      simp only [Proofs.CppState.bindArgument,found,Bind.bind,Option.bind] at run
      split at run
      · contradiction
      · have same := Option.some.inj run
        subst t
        exact ⟨[],by simp [Proofs.CppState.State.observe]⟩

theorem one_memory (s t : NState) (r : Resolved) (run : bindOne s r = some t) :
    ∃ extra, t.scalars.memory = s.scalars.memory ++ extra := by
  cases r with
  | scalar ty wr value =>
    cases bound : Proofs.CppState.bindArgument s.scalars ⟨ty,false,wr⟩ (.value value) with
    | none => simp [bindOne,bound] at run
    | some sc =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t; exact scalar_memory _ _ _ _ bound
  | scalarAddress ty address wr =>
    cases bound : Proofs.CppState.bindArgument s.scalars ⟨ty,true,wr⟩ (.reference address) with
    | none => simp [bindOne,bound] at run
    | some sc =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t; exact scalar_memory _ _ _ _ bound
  | vector owner scope ty wr =>
    cases bound : s.frame.bindRoot owner (.integer ty) scope wr with
    | none => simp [bindOne,bound] at run
    | some pair =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t; exact ⟨[],by simp [NState.observe]⟩
  | vectorChild owner address ty wr =>
    unfold bindOne at run
    obtain ⟨pair,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have same := Option.some.inj rest
    subst t
    exact ⟨[],by simp [NState.observe]⟩
  | nestedRoot owner scope ty wr =>
    cases bound : s.frame.bindRoot owner (.vector (.integer ty)) scope wr with
    | none => simp [bindOne,bound] at run
    | some pair =>
      simp only [bindOne,bound,Bind.bind,Option.bind,Option.some.injEq] at run
      subst t; exact ⟨[],by simp [NState.observe]⟩

theorem all_exists {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (rs : List Resolved) (bound : ∀ r ∈ rs, Boundable h s r) :
    ∃ t, bindAll s rs = some t ∧ Family (params ++ describe s.frame.rootWritable s.frame.bindings.length rs) h t.frame m ∧
      t.frame.rootWritable = s.frame.rootWritable ∧ t.scope = s.scope ∧
      ∃ extra, t.scalars.memory = s.scalars.memory ++ extra := by
  induction rs generalizing params s with
  | nil => exact ⟨s,rfl,by simpa [describe] using family,rfl,rfl,[],by simp⟩
  | cons r rs ih =>
    have head := bound r (by simp)
    obtain ⟨next,run⟩ := one_exists family r head
    obtain ⟨nextFamily,state,flags,count,scope⟩ := DynamicFamilyInit.bind_one family r (compatible head) run
    have memory := one_memory s next r run
    have tail : ∀ q ∈ rs, Boundable h next q := by
      intro q member
      exact transport (bound q (List.mem_cons_of_mem r member)) flags memory state
    obtain ⟨last,tailRun,lastFamily,lastFlags,lastScope,extra2,memory2⟩ := ih nextFamily tail
    obtain ⟨extra1,memory1⟩ := memory
    refine ⟨last,by simp [bindAll,run,tailRun],?_,lastFlags.trans flags,lastScope.trans scope,extra1 ++ extra2,?_⟩
    · simpa [describe,flags,count,List.append_assoc] using lastFamily
    · rw [memory2,memory1,List.append_assoc]

end Proofs.DynamicBindExists
