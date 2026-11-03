import Proofs.DynamicIndexEval

namespace Proofs.DynamicIndexRead
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct Proofs.CppNestedRows Proofs.CppNestedStmt
open Proofs.CppRowsGraph

theorem read_row (s : NState) (slot rb : Nat) (idx pos : NExpr) (k j R sc epoch owner : Nat) (ids : List Nat) (ty : Ty) (x : Int) (wr m : Bool)
    (prev : Buffer Value) (wi pi wp pp : Nat)
    (idxEv : ∀ u, Ext s u → ∃ t extra, Ev u idx t (k : Int) extra wi pi)
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : Rows s.frame.state R ty sc ids epoch)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (lookup : ids[k]? = some owner)
    (found : s.frame.state.storage.lookup owner = some prev)
    (item : prev.items[j]? = some (Value.integer x))
    (posEv : ∀ u, Ext s u → ∃ u2 extra2, Ev u pos u2 (j : Int) extra2 wp pp) :
    ∃ t extra1 extra2, Ev s (.read ty (.row (.local slot) (.integer ty) idx) pos) t x (extra1 ++ [CppRowsGraph.binding R ty epoch k owner wr] ++ extra2)
      (wi+2+wp+1) (max (idx.nodes+pos.nodes+4) (max pi (max pp 2))) := by
  have nodes := Proofs.CppNestedStmt.container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,extra1,hrow,good1,bindings1⟩ := DynamicIndexEval.eval_row
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) slot rb idx k R sc epoch owner ids ty wr m wi pi
    (fun u ext => idxEv u ((Ext.of_goodF (extra := []) (GoodF.charge s 0 _) (by simp)).trans ext)) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) perm lookup
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).trans good1
  have ext1 : Ext s t1 := Ext.of_goodF g1 (by simpa [List.append_assoc] using bindings1)
  obtain ⟨t2,extra2,hpos,goodp,bp⟩ := posEv t1 ext1
  have gAll := g1.trans goodp
  have stateEq : t2.frame.state = s.frame.state := gAll.1
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := gAll.2.1
  have bindEq : t2.frame.bindings = s.frame.bindings ++ (extra1 ++ [CppRowsGraph.binding R ty epoch k owner wr] ++ extra2) := by
    have : t1.frame.bindings = s.frame.bindings ++ (extra1 ++ [CppRowsGraph.binding R ty epoch k owner wr]) := by simpa using bindings1
    rw [bp,this]; simp
  have g2 : Rows t2.frame.state R ty sc ids epoch := by rw [stateEq]; exact g
  have lengths2 : t2.frame.rootWritable.length = t2.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t2.frame.rootWritable[R]? = some m := by rw [rwEq]; exact flag
  have hb : t2.frame.bindings[(s.frame.bindings.length+extra1.length)]? = some (CppRowsGraph.binding R ty epoch k owner wr) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := CppRowsGraph.resolve_row t2.frame (s.frame.bindings.length+extra1.length) R ty sc ids epoch k owner g2 lookup wr m hb
    lengths2 flag2 perm
  have sameBuffer : buffer = prev := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain,_⟩ := CppRowsGraph.row_object t2.frame R ty sc ids epoch k owner g2 lookup
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  obtain ⟨reference,hreference,hread⟩ := read_ok t2.frame (s.frame.bindings.length+extra1.length) ty j x (CppRowsGraph.binding R ty epoch k owner wr)
    objectBuffer ⟨.integer ty,some R,none,[]⟩ m hb rfl resolved object
    (CppRowsGraph.maximum_row t2.frame R ty sc ids epoch k owner g2 lookup m lengths2 flag2) perm item
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) =
        some (t1,(s.frame.bindings.length+extra1.length)) := by simpa using hrow
  refine ⟨t2.charge 1 2,extra1,extra2,?_,?_,?_⟩
  · simp [NExpr.eval,evalRow,hpos,hreference,hread]
  · have := gAll.trans (GoodF.charge t2 1 2)
    rw [nodes] at this
    refine this.mono (by omega) (by omega)
  · simpa using bindEq

/-- `g[k].size()` for a nested root `g` of permission `wr`. -/
theorem size_row (s : NState) (slot rb : Nat) (idx : NExpr) (k R sc epoch owner : Nat) (ids : List Nat) (ty : Ty) (wr m : Bool)
    (prev : Buffer Value) (wi pi : Nat)
    (idxEv : ∀ u, Ext s u → ∃ t extra, Ev u idx t (k : Int) extra wi pi)
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : Rows s.frame.state R ty sc ids epoch)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (lookup : ids[k]? = some owner)
    (found : s.frame.state.storage.lookup owner = some prev) (small : prev.items.length < 2^64) :
    ∃ t extra1, Ev s (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) t (prev.items.length : Int)
      (extra1 ++ [CppRowsGraph.binding R ty epoch k owner wr]) (wi+3) (max (idx.nodes+4) (max pi 2)) := by
  have nodes := Proofs.CppNestedStmt.container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,extra1,hrow,good1,bindings1⟩ := DynamicIndexEval.eval_row
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) slot rb idx k R sc epoch owner ids ty wr m wi pi
    (fun u ext => idxEv u ((Ext.of_goodF (extra := []) (GoodF.charge s 0 _) (by simp)).trans ext)) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) perm lookup
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)).trans good1
  have stateEq : t1.frame.state = s.frame.state := g1.1
  have rwEq : t1.frame.rootWritable = s.frame.rootWritable := g1.2.1
  have bindEq : t1.frame.bindings = s.frame.bindings ++ (extra1 ++ [CppRowsGraph.binding R ty epoch k owner wr]) := by simpa using bindings1
  have g2 : Rows t1.frame.state R ty sc ids epoch := by rw [stateEq]; exact g
  have lengths2 : t1.frame.rootWritable.length = t1.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t1.frame.rootWritable[R]? = some m := by rw [rwEq]; exact flag
  have hb : t1.frame.bindings[(s.frame.bindings.length+extra1.length)]? = some (CppRowsGraph.binding R ty epoch k owner wr) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := CppRowsGraph.resolve_row t1.frame (s.frame.bindings.length+extra1.length) R ty sc ids epoch k owner g2 lookup wr m hb
    lengths2 flag2 perm
  have sameBuffer : buffer = prev := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  have sized : (⟨64,false,false⟩ : Ty).valid (buffer.items.length : Int) = true := by
    simp [Ty.valid]; omega
  have size := CppNestedOps.size_runs t1.frame (s.frame.bindings.length+extra1.length) (.integer ty) _ buffer resolved sized
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) =
        some (t1,(s.frame.bindings.length+extra1.length)) := by simpa using hrow
  refine ⟨(t1.charge 1 2),extra1,?_,?_,?_⟩
  · simp [NExpr.eval,evalRow,size]
  · have := g1.trans (GoodF.charge t1 1 2)
    rw [nodes] at this
    refine this.mono (by omega) (by omega)
  · simpa using bindEq


end Proofs.DynamicIndexRead
