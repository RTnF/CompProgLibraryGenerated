import Proofs.DynamicContents
import Proofs.CppNestedEval

namespace Proofs.DynamicExpr
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppMixedInvoke
open Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicContents

structure Locals where
  memory : List Proofs.CppState.Cell
  bindings : List Proofs.CppState.Binding
  slots : List Location
  deriving DecidableEq, Repr

def snapshot (s : NState) : Locals := ⟨s.scalars.memory,s.scalars.bindings,s.slots⟩

def environment (l : Locals) (slot : Nat) (ty : Ty) : Option Int := do
  let .scalar index ← l.slots[slot]? | none
  let binding ← l.bindings[index]?
  let cell ← l.memory[binding.address]?
  if cell.type = ty ∧ ty.valid cell.value then some cell.value else none

theorem snapshot_env (s : NState) : environment (snapshot s) = envOf s := by
  funext slot ty
  simp only [environment,snapshot,envOf,NState.scalarCell,NState.scalarSlot]
  cases hl : s.slots[slot]? with
  | none => simp [hl]
  | some location =>
    cases location with
    | scalar index =>
      cases binding : s.scalars.bindings[index]? with
      | none => simp [binding]
      | some b =>
        cases cell : s.scalars.memory[b.address]? with
        | none => simp [binding,cell]
        | some c =>
          by_cases ok : c.type = ty ∧ ty.valid c.value = true <;> simp [binding,cell,ok]
    | vector index => simp

def _root_.Proofs.DynamicContents.Contents.element : Contents → Proofs.CppVectorOwnership.Element
  | .flat ty _ _ => .integer ty
  | .rows ty _ _ => .vector (.integer ty)

def _root_.Proofs.DynamicContents.Contents.scope : Contents → Nat
  | .flat _ sc _ | .rows _ sc _ => sc

def _root_.Proofs.DynamicContents.Contents.length : Contents → Nat
  | .flat _ _ vs => vs.length
  | .rows _ _ vs => vs.length

mutual
def select (params : List Parameter) (l : Locals) (h : ContentsHeap) : Container → Option Contents
  | .local slot => do
      let .vector rb ← l.slots[slot]? | none
      let p ← params.find? (fun p => p.slot == rb)
      let view ← h p.owner
      if view.element = p.element ∧ view.scope = p.scope then some view else none
  | .row parent expected index => do
      let .rows ty sc values ← select params l h parent | none
      let i ← denote params l h index
      if expected = .integer ty ∧ 0 ≤ i then
        let row ← values[i.toNat]?
        some (.flat ty sc row)
      else none

def denote (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) : Option Int :=
  if e.scalarOnly = true then e.denote (environment l) else
  match e with
  | .cast ty operand => (denote params l h operand).bind ty.convert
  | .targetCast ty operand => (denote params l h operand).bind ty.targetConvert
  | .unary ty op operand => (denote params l h operand).bind fun v => ty.convert (unaryValue op v)
  | .binary ty op left right => (denote params l h left).bind fun a =>
      (denote params l h right).bind fun b => ty.convert (binaryValue op a b)
  | .divrem ty remainder left right => (denote params l h left).bind fun a =>
      (denote params l h right).bind fun b => checkedDivRem ty remainder a b
  | .logical conjunction left right => (denote params l h left).bind fun a =>
      if conjunction then
        (if a = 0 then some 0 else (denote params l h right).map fun b => if b = 0 then 0 else 1)
      else
        (if a = 0 then (denote params l h right).map fun b => if b = 0 then 0 else 1 else some 1)
  | .size element container => do
      let view ← select params l h container
      let value : Int := view.length
      if view.element = element ∧ (⟨64,false,false⟩ : Ty).valid value then some value else none
  | .read ty container index => do
      let .flat t _ values ← select params l h container | none
      let i ← denote params l h index
      if t = ty ∧ 0 ≤ i then
        let value ← values[i.toNat]?
        if ty.valid value then some value else none
      else none
  | _ => none
end

theorem denote_scalar (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr)
    (scalar : e.scalarOnly = true) : denote params l h e = e.denote (environment l) := by
  rw [denote.eq_def,if_pos scalar]

theorem size_root (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (slot : Nat) (p : Parameter) (view : Contents)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (lookup : h p.owner = some view) (element : view.element = p.element)
    (scope : view.scope = p.scope) :
    denote params l h (.size view.element (.local slot)) =
      if (⟨64,false,false⟩ : Ty).valid (view.length : Int) then some (view.length : Int) else none := by
  rw [denote.eq_def]
  simp [NExpr.scalarOnly,select,location,selected,lookup,element,scope]

theorem size_row (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (slot : Nat) (p : Parameter) (ty : Ty) (sc k : Nat) (values : List (List Int)) (vs : List Int) (idx : NExpr)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (lookup : h p.owner = some (.rows ty sc values))
    (element : p.element = .vector (.integer ty)) (scope : p.scope = sc)
    (idxValue : denote params l h idx = some (k : Int)) (row : values[k]? = some vs)
    (sized : (⟨64,false,false⟩ : Ty).valid (vs.length : Int) = true) :
    denote params l h (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) = some (vs.length : Int) := by
  rw [denote.eq_def]
  simp [NExpr.scalarOnly,select,location,selected,lookup,element,scope,
    Contents.element,Contents.scope,Contents.length,idxValue,row,sized]

theorem read_row (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (slot : Nat) (p : Parameter) (ty : Ty) (sc k j : Nat) (values : List (List Int)) (vs : List Int)
    (idx pos : NExpr) (x : Int)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (lookup : h p.owner = some (.rows ty sc values))
    (element : p.element = .vector (.integer ty)) (scope : p.scope = sc)
    (idxValue : denote params l h idx = some (k : Int)) (row : values[k]? = some vs)
    (posValue : denote params l h pos = some (j : Int)) (item : vs[j]? = some x) (valid : ty.valid x = true) :
    denote params l h (.read ty (.row (.local slot) (.integer ty) idx) pos) = some x := by
  rw [denote.eq_def]
  simp [NExpr.scalarOnly,select,location,selected,lookup,element,scope,
    Contents.element,Contents.scope,idxValue,row,posValue,item,valid]

theorem read_root (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (slot : Nat) (p : Parameter) (ty : Ty) (sc j : Nat) (vs : List Int) (idx : NExpr) (x : Int)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (lookup : h p.owner = some (.flat ty sc vs))
    (element : p.element = .integer ty) (scope : p.scope = sc)
    (idxValue : denote params l h idx = some (j : Int)) (item : vs[j]? = some x) (valid : ty.valid x = true) :
    denote params l h (.read ty (.local slot) idx) = some x := by
  rw [denote.eq_def]
  simp [NExpr.scalarOnly,select,location,selected,lookup,element,scope,Contents.element,Contents.scope,idxValue,item,valid]

end Proofs.DynamicExpr
