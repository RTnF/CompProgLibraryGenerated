import Proofs.DynamicExprCertified

namespace Proofs.DynamicExprAtoms
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicExprCertified

-- These constructors require logical lookups and bounds, rather than a
-- caller-supplied proof about execution states.
theorem root_size (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (p : Parameter)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc values)) (small : values.length < 2^64) :
    Atomic params l h (.size (.vector (.integer ty)) (.local slot)) (values.length : Int) := by
  intro s realizes
  obtain ⟨pure,t,ev,_⟩ := DynamicSizeSound.root_size params l h s realizes slot p location selected ty sc values lookup small
  exact ⟨pure,t,[],ev.mono (by simp [NExpr.nodes,Container.nodes]) (by simp [NExpr.nodes,Container.nodes])⟩

theorem flat_size (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (p : Parameter)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc : Nat) (values : List Int)
    (lookup : h p.owner = some (.flat ty sc values)) (small : values.length < 2^64) :
    Atomic params l h (.size (.integer ty) (.local slot)) (values.length : Int) := by
  intro s realizes
  obtain ⟨pure,t,ev,_⟩ := DynamicFlatSound.size_flat params l h s realizes slot p location selected ty sc values lookup small
  exact ⟨pure,t,[],ev.mono (by simp [NExpr.nodes,Container.nodes]) (by simp [NExpr.nodes,Container.nodes])⟩

theorem flat_read (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (p : Parameter)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc j : Nat) (values : List Int) (idx : NExpr) (x : Int)
    (lookup : h p.owner = some (.flat ty sc values))
    (scalar : idx.scalarOnly = true) (idxValue : idx.denote (environment l) = some (j : Int))
    (item : values[j]? = some x) : Atomic params l h (.read ty (.local slot) idx) x := by
  intro s realizes
  obtain ⟨pure,t,ev,_⟩ := DynamicFlatSound.read_flat params l h s realizes slot p location selected ty sc j values idx x lookup scalar idxValue item
  exact ⟨pure,t,[],ev.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩

theorem row_size (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (p : Parameter)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k : Nat) (values : List (List Int)) (vs : List Int) (idx : NExpr)
    (lookup : h p.owner = some (.rows ty sc values))
    (scalar : idx.scalarOnly = true) (idxValue : idx.denote (environment l) = some (k : Int))
    (row : values[k]? = some vs) (small : vs.length < 2^64) :
    Atomic params l h (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) (vs.length : Int) := by
  intro s realizes
  have value : idx.denote (envOf s) = some (k : Int) := by rw [← snapshot_env,realizes.locals]; exact idxValue
  obtain ⟨pure,t,extra,ev,_⟩ := DynamicReadSound.row_size params l h s realizes slot p location selected ty sc k values vs idx lookup scalar value row small
  exact ⟨pure,t,extra,ev.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩

theorem row_read (params : List Parameter) (l : Locals) (h : ContentsHeap) (slot : Nat) (p : Parameter)
    (location : l.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k j : Nat) (values : List (List Int)) (vs : List Int) (idx pos : NExpr) (x : Int)
    (lookup : h p.owner = some (.rows ty sc values))
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (environment l) = some (k : Int))
    (row : values[k]? = some vs) (posScalar : pos.scalarOnly = true)
    (posValue : pos.denote (environment l) = some (j : Int)) (item : vs[j]? = some x) :
    Atomic params l h (.read ty (.row (.local slot) (.integer ty) idx) pos) x := by
  intro s realizes
  have iv : idx.denote (envOf s) = some (k : Int) := by rw [← snapshot_env,realizes.locals]; exact idxValue
  have pv : pos.denote (envOf s) = some (j : Int) := by rw [← snapshot_env,realizes.locals]; exact posValue
  obtain ⟨pure,t,extra,ev,_⟩ := DynamicReadSound.row_read params l h s realizes slot p location selected ty sc k j values vs idx pos x lookup idxScalar iv row posScalar pv item
  exact ⟨pure,t,extra,ev.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩

end Proofs.DynamicExprAtoms
