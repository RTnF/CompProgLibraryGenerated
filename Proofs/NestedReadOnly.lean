import Proofs.CppNestedStmt

/-! Row access `g[k]` on a nested root with an arbitrary permission (the constructed roots of `CppNestedRows` are the
writable special case).  A const root yields const rows. -/

namespace Proofs.NestedReadOnly
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct Proofs.CppNestedRows Proofs.CppNestedStmt

/-- The binding of row `k` created by `g[k]` when `g` has permission `wr`. -/
def rowBindingW (R : Nat) (ty : Ty) (k : Nat) (wr : Bool) : Binding :=
  ⟨R+1+k,.integer ty,wr,.child ⟨R,0,k⟩⟩

theorem maximum_root_g (f : Frame) (R : Nat) (ty : Ty) (w sc : Nat) (g : RootGraph f.state R ty w sc)
    (lengths : f.rootWritable.length = f.state.forest.objects.length) (m : Bool)
    (flag : f.rootWritable[R]? = some m) : f.maximum R = some m :=
  maximum_runs f R R m lengths (CppVectorOwnership.root_runs f.state.forest R _ g.tag rfl) flag

theorem maximum_row_g (f : Frame) (R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (lengths : f.rootWritable.length = f.state.forest.objects.length) (m : Bool)
    (flag : f.rootWritable[R]? = some m) (inside : k < w) : f.maximum (R+1+k) = some m := by
  obtain ⟨root,_,rootFound,_,items⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  obtain ⟨childBuffer,tagFound,_,_⟩ := facts.2.2.2 (R+1+k) ((mem_rowIds R w (R+1+k)).mpr ⟨k,inside,rfl⟩)
  have rooted : f.state.forest.rootOwner (R+1+k) = some R := by
    rw [CppVectorOwnership.child_runs f.state.forest (R+1+k) R ⟨.integer ty,some R,none,[]⟩ tagFound rfl (by omega)]
    exact CppVectorOwnership.root_runs f.state.forest R _ g.tag rfl
  exact maximum_runs f (R+1+k) R m lengths rooted flag

theorem child_row_g (f : Frame) (rb R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc) (wr m : Bool)
    (binding : f.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some m) (perm : wr = true → m = true) (inside : k < w) :
    f.child rb (.integer ty) k = some (f.addBinding (rowBindingW R ty k wr)) := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object f R ty w sc g
  have resolved : f.resolve rb (.vector (.integer ty)) = some (⟨R,.vector (.integer ty),wr,.root sc⟩,root) :=
    resolve_root f rb _ _ sc root (rootTag ty sc R w) m binding rfl rfl rootObject rfl rfl
      (maximum_root_g f R ty w sc g lengths m flag) perm
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  have sizeOK : (k : Int).toNat < root.items.length := by
    simp [items,rowIds_length]; exact inside
  have address : CppVector.elementRef root (accepts (.vector (.integer ty))) k =
      some ⟨R,0,k⟩ := by
    have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
    have := CppVector.elementRef_runs root (accepts (.vector (.integer ty))) k valid (by omega) sizeOK
    simpa [facts.1,epoch] using this
  have lookup : root.items[k]? = some (Value.child (R+1+k)) := by
    simp [items,List.getElem?_map,rowIds_get R w k inside]
  have read : readRef root (accepts (.vector (.integer ty))) ⟨R,0,k⟩ =
      some ⟨root,Value.child (R+1+k),1,root.capacity+2⟩ := by
    have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
    have := CppVector.readRef_runs root (accepts (.vector (.integer ty))) k _ valid lookup
    simpa [facts.1,epoch] using this
  obtain ⟨rowBuffer,rowObject,_⟩ := row_object f R ty w sc k g inside
  exact child_runs f rb (.integer ty) k _ root ⟨R,0,k⟩ _ (R+1+k) rowBuffer _ resolved address read rfl rowObject rfl

theorem resolve_row_g (f : Frame) (cb R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc) (wr m : Bool)
    (binding : f.bindings[cb]? = some (rowBindingW R ty k wr))
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some m) (perm : wr = true → m = true) (inside : k < w) :
    ∃ buffer, f.resolve cb (.integer ty) = some (rowBindingW R ty k wr,buffer) ∧
      f.state.storage.lookup (R+1+k) = some buffer := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
  have lookup : root.items[k]? = some (Value.child (R+1+k)) := by
    simp [items,List.getElem?_map,rowIds_get R w k inside]
  have read : readRef root (accepts (.vector (.integer ty))) ⟨R,0,k⟩ =
      some ⟨root,Value.child (R+1+k),1,root.capacity+2⟩ := by
    have := CppVector.readRef_runs root (accepts (.vector (.integer ty))) k _ valid lookup
    simpa [facts.1,epoch] using this
  obtain ⟨rowBuffer,rowObject,found⟩ := row_object f R ty w sc k g inside
  refine ⟨rowBuffer,?_,found⟩
  exact resolve_child f cb (.integer ty) (rowBindingW R ty k wr) ⟨R,0,k⟩ root (rootTag ty sc R w) _
    (R+1+k) rowBuffer _ m binding rfl rfl rfl rootObject read rfl rowObject
    (maximum_row_g f R ty w sc k g lengths m flag inside) perm

theorem eval_row_g (s : NState) (slot rb : Nat) (idx : NExpr) (k R w sc : Nat) (ty : Ty) (wr m : Bool)
    (scalar : idx.scalarOnly = true) (value : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (inside : k < w) :
    ∃ t, (Container.row (.local slot) (.integer ty) idx).eval s = some (t,s.frame.bindings.length) ∧
      GoodF s t (idx.nodes+2) (idx.nodes+2) ∧ t.frame.bindings = s.frame.bindings ++ [rowBindingW R ty k wr] := by
  have parent := eval_local (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)) slot rb
    (by simpa [NState.vectorSlot] using hslot)
  have env : envOf ((s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).charge 1 1) = envOf s :=
    envOf_core (Core.trans (core_charge _ _ _) (core_charge _ _ _))
  obtain ⟨t1,hidx,good1⟩ := scalar_eval idx _ k scalar (by rw [env]; exact value)
  have frame1 : t1.frame = s.frame := by
    have := good1.1.1
    simpa using this
  have chi := child_row_g s.frame rb R ty w sc k g wr m binding lengths flag perm inside
  simp only [Frame.addBinding] at chi
  refine ⟨({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [rowBindingW R ty k wr]}} : NState).charge 1 1,?_,?_,?_⟩
  · have hv : (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).vectorSlot slot = some rb := by
      simpa [NState.vectorSlot] using hslot
    simp [Container.eval,hv,hidx,chi,frame1]
  · have a := (GoodF.charge s 0 ((Container.local slot).nodes+idx.nodes+1)).trans
      ((GoodF.charge _ 1 1).trans good1.toF)
    have b := a.withFrame {s.frame with bindings := s.frame.bindings ++ [rowBindingW R ty k wr]}
      (by simp [frame1]) (by simp [frame1])
    have c := b.trans (GoodF.charge ({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [rowBindingW R ty k wr]}} : NState) 1 1)
    refine c.mono ?_ ?_ <;> simp [Container.nodes] <;> omega
  · simp

theorem container_nodes_g (slot : Nat) (ty : Ty) (idx : NExpr) :
    (Container.row (.local slot) (.integer ty) idx).nodes = idx.nodes+2 := container_nodes slot ty idx

/-- `g[k][j]` for a nested root `g` of permission `wr`. -/
theorem Ev.readRow_g (s : NState) (slot rb : Nat) (idx pos : NExpr) (k j R w sc : Nat) (ty : Ty) (x : Int) (wr m : Bool)
    (prev : Buffer Value) (extra2 : List Binding) (wp pp : Nat)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some prev)
    (item : prev.items[j]? = some (Value.integer x))
    (posEv : ∀ u, Ext s u → ∃ u2, Ev u pos u2 (j : Int) extra2 wp pp) :
    ∃ t, Ev s (.read ty (.row (.local slot) (.integer ty) idx) pos) t x ([rowBindingW R ty k wr] ++ extra2)
      (idx.nodes+2+wp+1) (max (idx.nodes+pos.nodes+4) (max (idx.nodes+2) (max pp 2))) := by
  have nodes := container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row_g
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) slot rb idx k R w sc ty wr m
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) perm inside
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).trans good1
  have ext1 : Ext s t1 := Ext.of_goodF g1 (by simpa using bindings1)
  obtain ⟨t2,hpos,goodp,bp⟩ := posEv t1 ext1
  have gAll := g1.trans goodp
  have stateEq : t2.frame.state = s.frame.state := gAll.1
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := gAll.2.1
  have bindEq : t2.frame.bindings = s.frame.bindings ++ ([rowBindingW R ty k wr] ++ extra2) := by
    have : t1.frame.bindings = s.frame.bindings ++ [rowBindingW R ty k wr] := by simpa using bindings1
    rw [bp,this]; simp
  have g2 : RootGraph t2.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths2 : t2.frame.rootWritable.length = t2.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t2.frame.rootWritable[R]? = some m := by rw [rwEq]; exact flag
  have hb : t2.frame.bindings[s.frame.bindings.length]? = some (rowBindingW R ty k wr) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row_g t2.frame s.frame.bindings.length R ty w sc k g2 wr m hb
    lengths2 flag2 perm inside
  have sameBuffer : buffer = prev := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain⟩ := row_object t2.frame R ty w sc k g2 inside
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  obtain ⟨reference,hreference,hread⟩ := read_ok t2.frame s.frame.bindings.length ty j x (rowBindingW R ty k wr)
    objectBuffer ⟨.integer ty,some R,none,[]⟩ m hb rfl resolved object
    (maximum_row_g t2.frame R ty w sc k g2 lengths2 m flag2 inside) perm item
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) =
        some (t1,s.frame.bindings.length) := by simpa using hrow
  refine ⟨t2.charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,evalRow,hpos,hreference,hread]
  · have := gAll.trans (GoodF.charge t2 1 2)
    rw [nodes] at this
    refine this.mono (by omega) (by omega)
  · simpa using bindEq

/-- `g[k].size()` for a nested root `g` of permission `wr`. -/
theorem Ev.sizeRow_g (s : NState) (slot rb : Nat) (idx : NExpr) (k R w sc : Nat) (ty : Ty) (wr m : Bool)
    (prev : Buffer Value)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some prev) (small : prev.items.length < 2^64) :
    ∃ t, Ev s (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) t (prev.items.length : Int)
      [rowBindingW R ty k wr] (idx.nodes+3) (idx.nodes+4) := by
  have nodes := container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row_g
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) slot rb idx k R w sc ty wr m
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) perm inside
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)).trans good1
  have stateEq : t1.frame.state = s.frame.state := g1.1
  have rwEq : t1.frame.rootWritable = s.frame.rootWritable := g1.2.1
  have bindEq : t1.frame.bindings = s.frame.bindings ++ [rowBindingW R ty k wr] := by simpa using bindings1
  have g2 : RootGraph t1.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths2 : t1.frame.rootWritable.length = t1.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t1.frame.rootWritable[R]? = some m := by rw [rwEq]; exact flag
  have hb : t1.frame.bindings[s.frame.bindings.length]? = some (rowBindingW R ty k wr) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row_g t1.frame s.frame.bindings.length R ty w sc k g2 wr m hb
    lengths2 flag2 perm inside
  have sameBuffer : buffer = prev := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  have sized : (⟨64,false,false⟩ : Ty).valid (buffer.items.length : Int) = true := by
    simp [Ty.valid]; omega
  have size := CppNestedOps.size_runs t1.frame s.frame.bindings.length (.integer ty) _ buffer resolved sized
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+2)) =
        some (t1,s.frame.bindings.length) := by simpa using hrow
  refine ⟨(t1.charge 1 2),?_,?_,?_⟩
  · simp [NExpr.eval,evalRow,size]
  · have := g1.trans (GoodF.charge t1 1 2)
    rw [nodes] at this
    refine this.mono (by omega) (by omega)
  · simpa using bindEq

/-- `g.size()` for a nested root `g` with `w` rows. -/
theorem Ev.sizeNested_g (s : NState) (slot rb R sc w : Nat) (ty : Ty) (wr m : Bool)
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),wr,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some m) (perm : wr = true → m = true) (small : w < 2^64) :
    ∃ t, Ev s (.size (.vector (.integer ty)) (.local slot)) t (w : Int) [] 3 3 := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object s.frame R ty w sc g
  have resolved : s.frame.resolve rb (.vector (.integer ty)) = some (⟨R,.vector (.integer ty),wr,.root sc⟩,root) :=
    resolve_root s.frame rb _ _ sc root (rootTag ty sc R w) m binding rfl rfl rootObject rfl rfl
      (maximum_root_g s.frame R ty w sc g lengths m flag) perm
  have hlen : root.items.length = w := by simp [items,rowIds_length]
  have sized : (⟨64,false,false⟩ : Ty).valid (root.items.length : Int) = true := by
    simp [Ty.valid]; omega
  have size := CppNestedOps.size_runs s.frame rb (.vector (.integer ty)) _ root resolved sized
  have container := eval_local (s.charge 0 ((Container.local slot).nodes+2)) slot rb
    (by simpa [NState.vectorSlot] using hslot)
  refine ⟨((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,container,size,hlen]
    rfl
  · have := ((GoodF.charge s 0 ((Container.local slot).nodes+2)).trans (GoodF.charge _ 1 1)).trans
      (GoodF.charge (((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1)) 1 2)
    exact this.mono (by simp [Container.nodes]) (by simp [Container.nodes])
  · simp

end Proofs.NestedReadOnly
