import Proofs.DynamicExprDerive

namespace Proofs.DynamicIndexEval
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct Proofs.CppNestedRows Proofs.CppNestedStmt
open Proofs.CppRowsGraph

-- The index may append its own temporary bindings. The selected row binding
-- follows them, so its index is the old length plus the temporary count.
theorem eval_row (s : NState) (slot rb : Nat) (idx : NExpr) (k R sc epoch owner : Nat)
    (ids : List Nat) (ty : Ty) (wr maximum : Bool) (wi pi : Nat)
    (index : ∀ u, Ext s u → ∃ t extra, Ev u idx t (k : Int) extra wi pi)
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : Rows s.frame.state R ty sc ids epoch)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some maximum) (perm : wr = true → maximum = true)
    (lookup : ids[k]? = some owner) :
    ∃ t extra, (Container.row (.local slot) (.integer ty) idx).eval s = some (t,s.frame.bindings.length+extra.length) ∧
      GoodF s t (wi+2) (max (idx.nodes+2) (max pi 1)) ∧
      t.frame.bindings = s.frame.bindings ++ (extra ++ [CppRowsGraph.binding R ty epoch k owner wr]) := by
  let start := (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).charge 1 1
  have first := (GoodF.charge s 0 ((Container.local slot).nodes+idx.nodes+1)).trans (GoodF.charge _ 1 1)
  obtain ⟨t1,extra,ev⟩ := index start (Ext.of_goodF (extra := []) first (by simp [start]))
  have good := first.trans ev.2.1
  have binds : t1.frame.bindings = s.frame.bindings ++ extra := by simpa [start] using ev.2.2
  have state := good.1
  have rights := good.2.1
  have binding1 : t1.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩ := by
    rw [binds,List.getElem?_append_left (List.getElem?_eq_some_iff.mp binding).1]; exact binding
  have chi := CppRowsGraph.child_row t1.frame rb R ty sc ids epoch k owner (by rw [state]; exact g) lookup wr maximum
    binding1 (by rw [state,rights]; exact lengths) (by rw [rights]; exact flag) perm
  simp only [Frame.addBinding] at chi
  let frame : Frame := {t1.frame with bindings := t1.frame.bindings ++ [CppRowsGraph.binding R ty epoch k owner wr]}
  let out := ({t1 with frame := frame} : NState).charge 1 1
  refine ⟨out,extra,?_,?_,?_⟩
  · have localEval := eval_local (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)) slot rb
      (by simpa [NState.vectorSlot] using hslot)
    have size : t1.frame.bindings.length = s.frame.bindings.length+extra.length := by simp [binds]
    have hv : (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).vectorSlot slot = some rb := by simpa [NState.vectorSlot] using hslot
    have hidx := ev.1
    dsimp only [start] at hidx
    simp [Container.eval,hv,hidx,chi,out,frame,size]
  · have framed := good.withFrame frame rfl rfl
    have final := framed.trans (GoodF.charge ({t1 with frame := frame} : NState) 1 1)
    exact final.mono (by omega) (by simp [Container.nodes] at final ⊢; omega)
  · simp [out,frame,binds,List.append_assoc]

-- Flat-root reads also preserve the bindings created by a general index.
theorem read_root (s : NState) (slot vb V vsc : Nat) (idx : NExpr) (j : Nat) (ty : Ty)
    (wr maximum : Bool) (buffer : Buffer Value) (x : Int) (wi pi : Nat)
    (index : ∀ u, Ext s u → ∃ t extra, Ev u idx t (j : Int) extra wi pi)
    (hslot : s.vectorSlot slot = some vb) (binding : s.frame.bindings[vb]? = some ⟨V,.integer ty,wr,.root vsc⟩)
    (valid : s.frame.state.wellFormed = true)
    (tag : s.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (found : s.frame.state.storage.lookup V = some buffer)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[V]? = some maximum) (perm : wr = true → maximum = true)
    (item : buffer.items[j]? = some (.integer x)) :
    ∃ t extra, Ev s (.read ty (.local slot) idx) t x extra (wi+2) (max (idx.nodes+3) (max pi 2)) := by
  let start := (s.charge 0 ((Container.local slot).nodes+idx.nodes+2)).charge 1 1
  have first := (GoodF.charge s 0 ((Container.local slot).nodes+idx.nodes+2)).trans (GoodF.charge _ 1 1)
  obtain ⟨t1,extra,ev⟩ := index start (Ext.of_goodF (extra := []) first (by simp [start]))
  have good := first.trans ev.2.1
  have binds : t1.frame.bindings = s.frame.bindings ++ extra := by simpa [start] using ev.2.2
  have state := good.1
  have rights := good.2.1
  have binding1 : t1.frame.bindings[vb]? = some ⟨V,.integer ty,wr,.root vsc⟩ := by
    rw [binds,List.getElem?_append_left (List.getElem?_eq_some_iff.mp binding).1]; exact binding
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot t1.frame vb V vsc ty wr maximum buffer binding1
    (by rw [state]; exact valid) (by rw [state]; exact tag) (by rw [state]; exact found)
    (by rw [state,rights]; exact lengths) (by rw [rights]; exact flag) perm
  obtain ⟨reference,hreference,hread⟩ := read_ok t1.frame vb ty j x ⟨V,.integer ty,wr,.root vsc⟩ buffer
    ⟨.integer ty,none,some vsc,[]⟩ maximum binding1 rfl resolved object vmax perm item
  refine ⟨t1.charge 1 2,extra,?_,?_,by simpa using binds⟩
  · have localEval := eval_local (s.charge 0 ((Container.local slot).nodes+idx.nodes+2)) slot vb
      (by simpa [NState.vectorSlot] using hslot)
    simp [NExpr.eval,localEval,ev.1,hreference,hread,start]
  · have final := good.trans (GoodF.charge t1 1 2)
    exact final.mono (by omega) (by simp [Container.nodes] at final ⊢; omega)

end Proofs.DynamicIndexEval
