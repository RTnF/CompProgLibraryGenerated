import Proofs.DynamicIndexAtoms

namespace Proofs.DynamicExprDecode
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppVectorOwnership
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr

-- Recover the parameter lookup that the pure selector actually used.
theorem root (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (view : Contents)
    (run : select params l h (.local slot) = some view) :
    ∃ p, l.slots[slot]? = some (.vector p.slot) ∧
      params.find? (fun q => q.slot == p.slot) = some p ∧ h p.owner = some view ∧
      view.element = p.element ∧ view.scope = p.scope := by
  unfold select at run
  cases loc : l.slots[slot]? with
  | none => simp [loc] at run
  | some location =>
    cases location with
    | scalar rb => simp [loc] at run
    | vector rb =>
      cases chosen : params.find? (fun p => p.slot == rb) with
      | none => simp [loc,chosen] at run
      | some p =>
        cases found : h p.owner with
        | none => simp [loc,chosen,found] at run
        | some selected =>
          simp only [loc,chosen,found,Bind.bind,Option.bind] at run
          split at run
          · rename_i good
            have equal := Option.some.inj run
            subst selected
            have slotEq : p.slot = rb := by simpa using List.find?_some chosen
            subst rb
            exact ⟨p,rfl,chosen,found,good⟩
          · contradiction

-- A row selector always returns a flat row. Only a local root can select rows.
theorem row (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (parent : Container) (element : Element) (idx : NExpr) (view : Contents)
    (run : select params l h (.row parent element idx) = some view) :
    ∃ (ty : Ty) (sc : Nat) (values : List (List Int)) (k : Nat) (vs : List Int), select params l h parent = some (.rows ty sc values) ∧
      element = .integer ty ∧ denote params l h idx = some (k : Int) ∧
      values[k]? = some vs ∧ view = .flat ty sc vs := by
  rw [select.eq_def] at run
  cases first : select params l h parent with
  | none => simp [first] at run
  | some selected =>
    cases selected with
    | flat ty sc values => simp [first] at run
    | rows ty sc values =>
      cases index : denote params l h idx with
      | none => simp [first,index] at run
      | some i =>
        simp only [first,index,Bind.bind,Option.bind] at run
        split at run
        · rename_i good
          cases item : values[i.toNat]? with
          | none => simp [item] at run
          | some vs =>
            simp only [item,Option.bind_some,Option.some.injEq] at run
            have natural : (i.toNat : Int) = i := by omega
            exact ⟨ty,sc,values,i.toNat,vs,rfl,good.1,by simp only [natural],item,run.symm⟩
        · contradiction

theorem rows_local (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (container : Container) (ty : Ty) (sc : Nat) (values : List (List Int))
    (run : select params l h container = some (.rows ty sc values)) :
    ∃ slot, container = .local slot := by
  cases container with
  | «local» slot => exact ⟨slot,rfl⟩
  | row parent element idx =>
    obtain ⟨_,_,_,_,_,_,_,_,_,bad⟩ := row params l h parent element idx _ run
    contradiction

theorem size (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (element : Element) (container : Container) (v : Int)
    (run : denote params l h (.size element container) = some v) :
    ∃ view, select params l h container = some view ∧ view.element = element ∧
      view.length < 2^64 ∧ v = (view.length : Int) := by
  rw [denote.eq_def] at run
  simp only [NExpr.scalarOnly,Bool.false_eq_true,ite_false] at run
  cases found : select params l h container with
  | none => simp [found] at run
  | some view =>
    simp only [found,Bind.bind,Option.bind] at run
    split at run
    · rename_i good
      have checked := good.2
      simp [Ty.valid] at checked
      exact ⟨view,rfl,good.1,by omega,(Option.some.inj run).symm⟩
    · contradiction

theorem read (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (ty : Ty) (container : Container) (idx : NExpr) (v : Int)
    (run : denote params l h (.read ty container idx) = some v) :
    ∃ (sc : Nat) (values : List Int) (k : Nat), select params l h container = some (.flat ty sc values) ∧
      denote params l h idx = some (k : Int) ∧ values[k]? = some v ∧ ty.valid v = true := by
  rw [denote.eq_def] at run
  simp only [NExpr.scalarOnly,Bool.false_eq_true,ite_false] at run
  cases selected : select params l h container with
  | none => simp [selected] at run
  | some view =>
    cases view with
    | rows t sc values => simp [selected] at run
    | flat t sc values =>
      cases index : denote params l h idx with
      | none => simp [selected,index] at run
      | some i =>
        simp only [selected,index,Bind.bind,Option.bind] at run
        split at run
        · rename_i good
          obtain ⟨rfl,positive⟩ := good
          cases item : values[i.toNat]? with
          | none => simp [item] at run
          | some x =>
            simp only [item,Option.bind_some] at run
            split at run
            · rename_i valid
              have equal := Option.some.inj run
              subst x
              have natural : (i.toNat : Int) = i := by omega
              exact ⟨sc,values,i.toNat,rfl,by simp only [natural],item,valid⟩
            · contradiction
        · contradiction

end Proofs.DynamicExprDecode
