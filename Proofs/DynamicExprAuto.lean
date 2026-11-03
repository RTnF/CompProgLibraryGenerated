import Proofs.DynamicExprDecode

namespace Proofs.DynamicExprAuto
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppVectorOwnership
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprDerive Proofs.DynamicExprCertified

-- The pure success supplies the actual root lookup, element type and size bound.
theorem size_ready (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (element : Element) (container : Container)
    (indices : ∀ idx : NExpr, idx.nodes < container.nodes → Ready params l h idx) :
    Ready params l h (.size element container) := by
  apply Ready.atom
  intro v run
  obtain ⟨view,selected,typed,small,value⟩ := DynamicExprDecode.size params l h element container v run
  subst v
  cases container with
  | «local» slot =>
    obtain ⟨p,loc,chosen,lookup,_,_⟩ := DynamicExprDecode.root params l h slot view selected
    cases view with
    | flat ty sc values =>
      simp only [Contents.element] at typed
      subst element
      exact DynamicExprAtoms.flat_size params l h slot p loc chosen ty sc values lookup small
    | rows ty sc values =>
      simp only [Contents.element] at typed
      subst element
      exact DynamicExprAtoms.root_size params l h slot p loc chosen ty sc values lookup small
  | row parent expected idx =>
    obtain ⟨ty,sc,values,k,vs,parentFound,expectedType,index,rowFound,same⟩ :=
      DynamicExprDecode.row params l h parent expected idx view selected
    subst view
    simp only [Contents.element] at typed
    subst element
    subst expected
    obtain ⟨slot,sameParent⟩ := DynamicExprDecode.rows_local params l h parent ty sc values parentFound
    subst parent
    obtain ⟨p,loc,chosen,lookup,_,_⟩ := DynamicExprDecode.root params l h slot (.rows ty sc values) parentFound
    exact DynamicIndexAtoms.row_size params l h slot p loc chosen ty sc k values vs idx lookup
      (indices idx (by simp [Container.nodes]; omega)) index rowFound small

theorem read_ready (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (ty : Ty) (container : Container) (idx : NExpr) (idxReady : Ready params l h idx)
    (indices : ∀ index : NExpr, index.nodes < container.nodes → Ready params l h index) :
    Ready params l h (.read ty container idx) := by
  apply Ready.atom
  intro v run
  obtain ⟨sc,vs,j,selected,index,item,_⟩ := DynamicExprDecode.read params l h ty container idx v run
  cases container with
  | «local» slot =>
    obtain ⟨p,loc,chosen,lookup,_,_⟩ := DynamicExprDecode.root params l h slot (.flat ty sc vs) selected
    exact DynamicIndexAtoms.flat_read params l h slot p loc chosen ty sc j vs idx v lookup idxReady index item
  | row parent expected rowIdx =>
    obtain ⟨t,sc2,values,k,vs2,parentFound,expectedType,rowIndex,rowFound,same⟩ :=
      DynamicExprDecode.row params l h parent expected rowIdx (.flat ty sc vs) selected
    simp only [Contents.flat.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    subst expected
    obtain ⟨slot,sameParent⟩ := DynamicExprDecode.rows_local params l h parent ty sc values parentFound
    subst parent
    obtain ⟨p,loc,chosen,lookup,_,_⟩ := DynamicExprDecode.root params l h slot (.rows ty sc values) parentFound
    exact DynamicIndexAtoms.row_read params l h slot p loc chosen ty sc k j values vs rowIdx idx v lookup
      (indices rowIdx (by simp [Container.nodes]; omega)) rowIndex rowFound idxReady index item

-- No leaf lookup or intermediate scalar value has to be supplied by the user.
-- Failed subexpressions are harmless when short-circuiting never evaluates them.
theorem ready (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) : Ready params l h e := by
  have all : ∀ n (e : NExpr), e.nodes ≤ n → Ready params l h e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro e small
      have sub : ∀ a : NExpr, a.nodes < e.nodes → Ready params l h a := by
        intro a less
        exact ih a.nodes (by omega) a (by omega)
      cases e with
      | literal ty value => exact Ready.scalar _ rfl
      | «variable» ty slot => exact Ready.scalar _ rfl
      | cast ty a => exact Ready.cast ty a (sub a (by simp [NExpr.nodes]))
      | targetCast ty a => exact Ready.targetCast ty a (sub a (by simp [NExpr.nodes]))
      | unary ty op a => exact Ready.unary ty op a (sub a (by simp [NExpr.nodes]))
      | binary ty op a b =>
        exact Ready.binary ty op a b (sub a (by simp [NExpr.nodes]; omega)) (sub b (by simp [NExpr.nodes]; omega))
      | divrem ty rem a b =>
        exact Ready.divrem ty rem a b (sub a (by simp [NExpr.nodes]; omega)) (sub b (by simp [NExpr.nodes]; omega))
      | logical conj a b =>
        exact Ready.logical conj a b (sub a (by simp [NExpr.nodes]; omega)) (sub b (by simp [NExpr.nodes]; omega))
      | size element container =>
        apply size_ready params l h element container
        intro idx less
        exact sub idx (by simp only [NExpr.nodes]; omega)
      | read ty container idx =>
        apply read_ready params l h ty container idx (sub idx (by simp [NExpr.nodes]; omega))
        intro rowIdx less
        exact sub rowIdx (by simp only [NExpr.nodes]; omega)
  exact all e.nodes e (by omega)

theorem evaluation (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) (v : Int)
    (success : denote params l h e = some v) : Evaluation params l h e v :=
  derive (ready params l h e) v success

theorem sound (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) (v : Int)
    (success : denote params l h e = some v) : Atomic params l h e v :=
  DynamicExprCertified.sound (evaluation params l h e v success)

end Proofs.DynamicExprAuto
