import Proofs.DynamicResultValid

namespace Proofs.DynamicBoundArguments
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedCall
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes

def Boundable (h : Heap) (s : NState) : Resolved → Prop
  | .scalar ty _ value => ty.valid value = true
  | .scalarAddress ty address _ => ∃ cell, s.scalars.memory[address]? = some cell ∧ cell.type = ty ∧ ty.valid cell.value = true
  | .vector owner scope ty wr => ∃ view maximum, h owner = some view ∧ view.element = .integer ty ∧ view.scope = scope ∧
      s.frame.rootWritable[owner]? = some maximum ∧ (wr = true → maximum = true)
  | .vectorChild owner address ty wr => ∃ buffer tag maximum,
      s.frame.headerOwner ⟨owner,.integer ty,wr,.child address⟩ = some owner ∧
      s.frame.object owner (.integer ty) = some (buffer,tag) ∧
      s.frame.maximum owner = some maximum ∧ (wr = true → maximum = true)
  | .nestedRoot owner scope ty wr => ∃ view maximum, h owner = some view ∧ view.element = .vector (.integer ty) ∧ view.scope = scope ∧
      s.frame.rootWritable[owner]? = some maximum ∧ (wr = true → maximum = true)

theorem compatible {h : Heap} {s : NState} {r : Resolved} (bound : Boundable h s r) : DynamicFamilyInit.Compatible h r := by
  cases r with
  | scalar _ _ _ | scalarAddress _ _ _ | vectorChild _ _ _ _ => exact True.intro
  | vector _ _ _ _ | nestedRoot _ _ _ _ =>
    obtain ⟨view,_,lookup,element,scope,_⟩ := bound
    exact ⟨view,lookup,element,scope⟩

theorem transport {h : Heap} {s t : NState} {r : Resolved} (bound : Boundable h s r)
    (flags : t.frame.rootWritable = s.frame.rootWritable)
    (memoryPrefix : ∃ extra, t.scalars.memory = s.scalars.memory ++ extra)
    (state : t.frame.state = s.frame.state) : Boundable h t r := by
  cases r with
  | scalar _ _ _ => exact bound
  | scalarAddress ty address wr =>
    obtain ⟨cell,found,typed,valid⟩ := bound
    obtain ⟨extra,memory⟩ := memoryPrefix
    refine ⟨cell,?_,typed,valid⟩
    rw [memory,List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found
  | vectorChild owner address ty wr =>
    obtain ⟨buffer,tag,maximum,header,object,max,permission⟩ := bound
    refine ⟨buffer,tag,maximum,?_,?_,?_,permission⟩
    · simpa only [Frame.headerOwner,Frame.object,state] using header
    · simpa only [Frame.object,state] using object
    · simpa only [Frame.maximum,state,flags] using max
  | vector _ _ _ _ | nestedRoot _ _ _ _ =>
    obtain ⟨view,maximum,lookup,element,scope,flag,permission⟩ := bound
    exact ⟨view,maximum,lookup,element,scope,by rw [flags]; exact flag,permission⟩

theorem cell_facts (l : Locals) (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (run : DynamicStmt.scalarCell l slot ty = some (binding,cell)) :
    l.memory[binding.address]? = some cell ∧ cell.type = ty ∧ ty.valid cell.value = true := by
  unfold DynamicStmt.scalarCell at run
  cases loc : l.slots[slot]? with
  | none => simp [loc] at run
  | some location =>
    cases location with
    | vector _ => simp [loc] at run
    | scalar index =>
      cases bfound : l.bindings[index]? with
      | none => simp [loc,bfound] at run
      | some b =>
        cases cfound : l.memory[b.address]? with
        | none => simp [loc,bfound,cfound] at run
        | some c =>
          simp only [loc,bfound,cfound,Bind.bind,Option.bind] at run
          split at run
          · rename_i good
            have same := Option.some.inj run
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
            exact ⟨cfound,good⟩
          · contradiction

theorem one (params : List Parameter) (st : DynamicStmt.State) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params st.locals st.contents s)
    (parameter : Proofs.CppVectorBindings.Parameter) (argument : NArgument) (r : Resolved)
    (pure : DynamicArguments.resolve params st parameter argument = some r) : Boundable h s r := by
  cases parameter with
  | scalar ty reference wr =>
    cases reference with
    | false =>
      cases argument with
      | value e =>
        by_cases typed : e.resultType = ty
        · cases value : denote params st.locals st.contents e with
          | none => simp [DynamicArguments.resolve,typed,value] at pure
          | some v =>
            simp only [DynamicArguments.resolve,typed,ite_true,value,Option.map_some,Option.some.injEq] at pure
            subst r
            have valid := DynamicResultValid.expression params st.locals st.contents e v value
            rw [typed] at valid; exact valid
        · simp [DynamicArguments.resolve,typed] at pure
      | _ => simp [DynamicArguments.resolve] at pure
    | true =>
      cases argument with
      | scalarReference slot =>
        cases cell : DynamicStmt.scalarCell st.locals slot ty with
        | none => simp [DynamicArguments.resolve,cell] at pure
        | some pair =>
          obtain ⟨binding,value⟩ := pair
          simp only [DynamicArguments.resolve,cell,Bind.bind,Option.bind] at pure
          split at pure
          · have same := Option.some.inj pure
            subst r
            obtain ⟨found,typed,valid⟩ := cell_facts st.locals slot ty binding value cell
            refine ⟨value,?_,typed,valid⟩
            have memory := congrArg Locals.memory real.locals
            change s.scalars.memory = st.locals.memory at memory
            rw [memory]; exact found
          · contradiction
      | _ => simp [DynamicArguments.resolve] at pure
  | vector ty wr =>
    cases argument with
    | vectorReference slot =>
      cases chosen : DynamicArguments.root params st slot (.integer ty) wr with
      | none => simp [DynamicArguments.resolve,chosen] at pure
      | some p =>
        simp only [DynamicArguments.resolve,chosen,Option.map_some,Option.some.injEq] at pure
        subst r
        obtain ⟨_,selected,typed,permission⟩ := DynamicArguments.root_found params st slot (.integer ty) wr p chosen
        have member := List.mem_of_find?_eq_some selected
        obtain ⟨view,lookup,element,scope⟩ := family.views p member
        exact ⟨view,p.maximum,lookup,element.trans typed,scope,family.flags p member,fun h => family.permissions p member (permission h)⟩
    | _ => simp [DynamicArguments.resolve] at pure
  | nested ty wr =>
    cases argument with
    | vectorReference slot =>
      cases chosen : DynamicArguments.root params st slot (.vector (.integer ty)) wr with
      | none => simp [DynamicArguments.resolve,chosen] at pure
      | some p =>
        simp only [DynamicArguments.resolve,chosen,Option.map_some,Option.some.injEq] at pure
        subst r
        obtain ⟨_,selected,typed,permission⟩ := DynamicArguments.root_found params st slot (.vector (.integer ty)) wr p chosen
        have member := List.mem_of_find?_eq_some selected
        obtain ⟨view,lookup,element,scope⟩ := family.views p member
        exact ⟨view,p.maximum,lookup,element.trans typed,scope,family.flags p member,fun h => family.permissions p member (permission h)⟩
    | _ => simp [DynamicArguments.resolve] at pure

theorem all (params : List Parameter) (st : DynamicStmt.State) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params st.locals st.contents s)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List NArgument) (rs : List Resolved)
    (pure : DynamicArguments.resolveAll params st parameters arguments = some rs) : ∀ r ∈ rs, Boundable h s r := by
  induction parameters generalizing arguments rs with
  | nil => cases arguments <;> simp_all [DynamicArguments.resolveAll]
  | cons p ps ih =>
    cases arguments with
    | nil => simp [DynamicArguments.resolveAll] at pure
    | cons a args =>
      cases first : DynamicArguments.resolve params st p a with
      | none => simp [DynamicArguments.resolveAll,first] at pure
      | some r =>
        cases rest : DynamicArguments.resolveAll params st ps args with
        | none => simp [DynamicArguments.resolveAll,first,rest] at pure
        | some tail =>
          simp only [DynamicArguments.resolveAll,first,rest,Bind.bind,Option.bind,Option.some.injEq] at pure
          subst rs
          intro q member
          rcases List.mem_cons.mp member with same | member
          · subst q; exact one params st h m s family real p a r first
          · exact ih args tail rest q member

end Proofs.DynamicBoundArguments
