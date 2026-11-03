import Proofs.CppNestedRows

namespace Proofs.CppNestedStmt
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct

theorem scalar_eval (e : NExpr) (s : NState) (v : Int) (scalar : e.scalarOnly = true)
    (value : e.denote (envOf s) = some v) :
    ∃ t, e.eval s = some (t,v) ∧ Good s t e.nodes e.nodes := by
  obtain ⟨t,ran⟩ := denote_complete e s v scalar value
  exact ⟨t,ran,eval_scalar e s t v scalar ran⟩

-- The state after declaring one scalar local.
def _root_.Proofs.CppNestedProgram.NState.declared (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    NState :=
  let scalars : CppState.State := {s.scalars with
    memory := s.scalars.memory ++ [⟨ty,value⟩],
    bindings := s.scalars.bindings ++ [⟨s.scalars.memory.length,writable⟩]}
  {s with scalars := scalars,slots := s.slots ++ [.scalar s.scalars.bindings.length]}

theorem check_run (e : NExpr) (s t : NState) (v : Int) (ran : e.eval s = some (t,v)) (nonzero : v ≠ 0) :
    (NStmt.check e).run s = some ⟨(t.release s).charge 1 0,none,false⟩ := by
  simp [NStmt.run,ran,nonzero]

theorem check_fault (e : NExpr) (s t : NState) (ran : e.eval s = some (t,0)) :
    (NStmt.check e).run s = none := by
  simp [NStmt.run,ran]

theorem declare_run (e : NExpr) (ty : Ty) (writable : Bool) (s t : NState) (v v' : Int)
    (ran : e.eval s = some (t,v)) (converted : ty.convert v = some v') :
    (NStmt.declare ty writable e).run s =
      some ⟨((t.release s).declared ty writable v').charge 1 0,none,false⟩ := by
  simp [NStmt.run,ran,converted,NState.declared]

theorem assign_run (e : NExpr) (slot : Nat) (ty : Ty) (s t : NState) (v v' : Int)
    (binding : CppState.Binding) (cell : CppState.Cell)
    (ran : e.eval s = some (t,v)) (resolved : (t.release s).scalarCell slot ty = some (binding,cell))
    (writable : binding.writable = true) (converted : ty.convert v = some v') :
    (NStmt.assign slot ty e).run s = some ⟨({(t.release s) with scalars := {(t.release s).scalars with
      memory := (t.release s).scalars.memory.set binding.address ⟨cell.type,v'⟩}} : NState).charge 1 0,
      none,false⟩ := by
  simp [NStmt.run,ran,resolved,writable,converted]

-- Like `Good`, but the frame may gain reference bindings; its storage state
-- and root permissions are unchanged.
def GoodF (s t : NState) (w p : Nat) : Prop :=
  t.frame.state = s.frame.state ∧ t.frame.rootWritable = s.frame.rootWritable ∧
  t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
  t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
  s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+w ∧
  s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+p) ∧
  s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak)

theorem _root_.Proofs.CppNestedEval.Good.toF {s t : NState} {w p : Nat} (good : Good s t w p) : GoodF s t w p := by
  obtain ⟨⟨frame,slots,scope,memory,bindings,base⟩,l,u,storage,pl,pu,ql,qu⟩ := good
  exact ⟨by rw [frame],by rw [frame],slots,scope,memory,bindings,base,l,u,pl,pu,ql,qu⟩

theorem liveS_of_memory {s t : NState} (memory : t.scalars.memory = s.scalars.memory)
    (bindings : t.scalars.bindings = s.scalars.bindings) (base : t.scalars.baseMemory = s.scalars.baseMemory) :
    liveS t = liveS s := by simp [liveS,memory,bindings,base]

theorem GoodF.trans {a b c : NState} {w1 p1 w2 p2 : Nat} (x : GoodF a b w1 p1) (y : GoodF b c w2 p2) :
    GoodF a c (w1+w2) (max p1 p2) := by
  obtain ⟨st1,rw1,sl1,sc1,m1,b1,k1,l1,u1,pl1,pu1,ql1,qu1⟩ := x
  obtain ⟨st2,rw2,sl2,sc2,m2,b2,k2,l2,u2,pl2,pu2,ql2,qu2⟩ := y
  have live : liveS b = liveS a := liveS_of_memory m1 b1 k1
  rw [live] at pu2
  have storage : c.frame.state.storage.peak = a.frame.state.storage.peak := by rw [st2,st1]
  have storageB : b.frame.state.storage.peak = a.frame.state.storage.peak := by rw [st1]
  exact ⟨st2.trans st1,rw2.trans rw1,sl2.trans sl1,sc2.trans sc1,m2.trans m1,b2.trans b1,k2.trans k1,
    by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem GoodF.mono {s t : NState} {w p w' p' : Nat} (good : GoodF s t w p) (hw : w ≤ w') (hp : p ≤ p') :
    GoodF s t w' p' := by
  obtain ⟨a,b,c,d,e,f,g,l,u,pl,pu,ql,qu⟩ := good
  exact ⟨a,b,c,d,e,f,g,l,by omega,pl,by omega,ql,qu⟩

theorem GoodF.withFrame {s t : NState} {w p : Nat} (good : GoodF s t w p) (frame : Frame)
    (state : frame.state = t.frame.state) (rootWritable : frame.rootWritable = t.frame.rootWritable) :
    GoodF s {t with frame := frame} w p := by
  obtain ⟨a,b,c,d,e,f,g,l,u,pl,pu,ql,qu⟩ := good
  exact ⟨by simpa [state] using a,by simpa [rootWritable] using b,c,d,e,f,g,l,u,pl,pu,ql,by simpa [state] using qu⟩

theorem GoodF.charge (s : NState) (work temporaries : Nat) :
    GoodF s (s.charge work temporaries) work temporaries :=
  (Good.charge s work temporaries).toF

open Proofs.CppNestedRows

theorem eval_local (s : NState) (slot binding : Nat) (found : s.vectorSlot slot = some binding) :
    (Container.local slot).eval s = some (s.charge 1 1,binding) := by
  simp [Container.eval,found]

theorem eval_row (s : NState) (slot rb : Nat) (idx : NExpr) (k R w sc : Nat) (ty : Ty)
    (scalar : idx.scalarOnly = true) (value : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w) :
    ∃ t, (Container.row (.local slot) (.integer ty) idx).eval s = some (t,s.frame.bindings.length) ∧
      GoodF s t (idx.nodes+2) (idx.nodes+2) ∧ t.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by
  have parent := eval_local (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)) slot rb
    (by simpa [NState.vectorSlot] using hslot)
  have env : envOf ((s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).charge 1 1) = envOf s :=
    envOf_core (Core.trans (core_charge _ _ _) (core_charge _ _ _))
  obtain ⟨t1,hidx,good1⟩ := scalar_eval idx _ k scalar (by rw [env]; exact value)
  have frame1 : t1.frame = s.frame := by
    have := good1.1.1
    simpa using this
  have chi := child_row s.frame rb R ty w sc k g binding lengths flag inside
  simp only [Frame.addBinding] at chi
  refine ⟨({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [rowBinding R ty k]}} : NState).charge 1 1,?_,?_,?_⟩
  · have hv : (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).vectorSlot slot = some rb := by
      simpa [NState.vectorSlot] using hslot
    simp [Container.eval,hv,hidx,chi,frame1]
  · have a := (GoodF.charge s 0 ((Container.local slot).nodes+idx.nodes+1)).trans
      ((GoodF.charge _ 1 1).trans good1.toF)
    have b := a.withFrame {s.frame with bindings := s.frame.bindings ++ [rowBinding R ty k]}
      (by simp [frame1]) (by simp [frame1])
    have c := b.trans (GoodF.charge ({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [rowBinding R ty k]}} : NState) 1 1)
    refine c.mono ?_ ?_ <;> simp [Container.nodes] <;> omega
  · simp

theorem envOf_goodF {s t : NState} {w p : Nat} (good : GoodF s t w p) : envOf t = envOf s := by
  obtain ⟨_,_,slots,_,memory,bindings,_,_⟩ := good
  funext slot ty
  simp [envOf,NState.scalarCell,NState.scalarSlot,slots,memory,bindings]

theorem vectorSlot_goodF {s t : NState} {w p : Nat} (good : GoodF s t w p) (slot : Nat) :
    t.vectorSlot slot = s.vectorSlot slot := by
  obtain ⟨_,_,slots,_⟩ := good
  simp [NState.vectorSlot,slots]

-- `container[k].reserve(n)` where the container is a row of a constructed root.
-- Outer peak after releasing temporaries and a final charge.
theorem peak_after (t2 X s : NState) (work temporaries : Nat) (hp : X.peak = t2.peak)
    (hsp : X.scalars = t2.scalars) (hst : t2.frame.state.storage.peak ≤ X.frame.state.storage.peak)
    (base : s.peak ≤ t2.peak) (upper : t2.peak ≤ max s.peak (t2.scalars.peak+t2.frame.state.storage.peak)) :
    s.peak ≤ ((X.release s).charge work temporaries).peak ∧
      ((X.release s).charge work temporaries).peak ≤ max s.peak
        (((X.release s).charge work temporaries).scalars.peak +
          ((X.release s).charge work temporaries).frame.state.storage.peak) := by
  have h := charge_release_peak X s work temporaries
  have grows : X.scalars.peak ≤ ((X.release s).charge work temporaries).scalars.peak := by
    simp only [charge_scalar_peak,release_scalars]; omega
  have storage : ((X.release s).charge work temporaries).frame.state.storage.peak = X.frame.state.storage.peak := rfl
  rw [hp] at h
  rw [hsp] at grows
  rw [storage]
  constructor <;> omega

theorem reserve_row_stmt (s : NState) (slot rb : Nat) (idx e : NExpr) (k n R w sc : Nat) (ty : Ty)
    (rowBuffer : Buffer Value)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (eScalar : e.scalarOnly = true) (eValue : e.denote (envOf s) = some (n : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some rowBuffer) (limit : n ≤ rowBuffer.limit) :
    ∃ t result, (NStmt.reserve (.row (.local slot) (.integer ty) idx) ty e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated (R+1+k) rowBuffer result ∧
      ((rowBuffer.capacity < n ∧ result = ⟨{rowBuffer with capacity := n,epoch := rowBuffer.epoch+1},(),
          rowBuffer.items.length+1,rowBuffer.capacity+n+2⟩) ∨
       (n ≤ rowBuffer.capacity ∧ result = ⟨rowBuffer,(),1,rowBuffer.capacity+1⟩)) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+idx.nodes+e.nodes+5 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+idx.nodes+e.nodes+5) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)) slot rb idx k R w sc ty
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) inside
  have env1 : envOf t1 = envOf s := (envOf_goodF good1).trans env0
  obtain ⟨t2,hexp,good2⟩ := scalar_eval e t1 n eScalar (by rw [env1]; exact eValue)
  have frame2 : t2.frame = t1.frame := good2.1.1
  have frame1state : t1.frame.state = s.frame.state := good1.1
  have frame1rw : t1.frame.rootWritable = s.frame.rootWritable := good1.2.1
  have bindings1' : t1.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by simpa using bindings1
  have g1 : RootGraph t1.frame.state R ty w sc := by rw [frame1state]; exact g
  have lengths1 : t1.frame.rootWritable.length = t1.frame.state.forest.objects.length := by
    rw [frame1rw,frame1state]; exact lengths
  have flag1 : t1.frame.rootWritable[R]? = some true := by rw [frame1rw]; exact flag
  have hb : t1.frame.bindings[s.frame.bindings.length]? = some (rowBinding R ty k) := by
    simp [bindings1']
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row t1.frame s.frame.bindings.length R ty w sc k g1 hb
    lengths1 flag1 inside
  have sameBuffer : buffer = rowBuffer := by
    rw [frame1state,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain⟩ := row_object t1.frame R ty w sc k g1 inside
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  have resolved2 : t2.frame.resolve s.frame.bindings.length (.integer ty) = some (rowBinding R ty k,objectBuffer) := by
    rw [frame2]; exact resolved
  have object2 : t2.frame.object (rowBinding R ty k).owner (.integer ty) = some (objectBuffer,⟨.integer ty,some R,none,[]⟩) := by
    rw [frame2]; exact object
  have stateEq : t2.frame.state = s.frame.state := by rw [frame2]; exact frame1state
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := by rw [frame2]; exact frame1rw
  have bindEq : t2.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by rw [frame2]; exact bindings1'
  have gAll := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)).trans
    (good1.trans good2.toF)
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)) = some (t1,s.frame.bindings.length) := by
    simpa using hrow
  have finalState : ∀ (f : Frame) (result : Result Value Unit),
      t2.frame.reserve s.frame.bindings.length (.integer ty) n = some f →
      f.bindings = s.frame.bindings ++ [rowBinding R ty k] →
      ∃ t, (NStmt.reserve (.row (.local slot) (.integer ty) idx) ty e).run s = some ⟨t,none,false⟩ ∧
        t.frame = {f with bindings := s.frame.bindings} ∧ t.scalars.work = t2.scalars.work+1 ∧
        t.scalars.peak = max t2.scalars.peak (liveS t2+1) ∧ t.slots = t2.slots ∧ t.scope = t2.scope ∧
        t.scalars.memory = t2.scalars.memory ∧ t.scalars.bindings = t2.scalars.bindings ∧
        t.scalars.baseMemory = t2.scalars.baseMemory ∧
        t.peak = max t2.peak (t.scalars.peak+t.frame.state.storage.peak) ∧
        t.frame.state.storage = f.state.storage := by
    intro f _ reserved hf
    refine ⟨(({t2 with frame := f} : NState).release s).charge 1 1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [NStmt.run,evalRow,hexp,reserved]
    · simp [NState.release,hf]
    · simp [charge_work]
    · simp [charge_scalar_peak,liveS]
    · simp
    · simp
    · simp
    · simp
    · simp
    · have := charge_release_peak ({t2 with frame := f} : NState) s 1 1
      simpa using this
    · simp
  have counters : s.scalars.work ≤ t2.scalars.work ∧
      t2.scalars.work ≤ s.scalars.work+(idx.nodes+2)+e.nodes ∧ s.scalars.peak ≤ t2.scalars.peak ∧
      t2.scalars.peak ≤ max s.scalars.peak (liveS s+max ((Container.row (.local slot) (.integer ty) idx).nodes+e.nodes+2)
        (max (idx.nodes+2) e.nodes)) := by
    obtain ⟨_,_,_,_,_,_,_,l,u,pl,pu,_,_⟩ := gAll
    exact ⟨l,by omega,pl,pu⟩
  have frameOf : ∀ result : Result Value Unit,
      {t2.frame.updated (R+1+k) objectBuffer result with bindings := s.frame.bindings} =
        s.frame.updated (R+1+k) objectBuffer result := by
    intro result
    simp [Frame.updated,stateEq,rwEq]
  have nodes : (Container.row (.local slot) (.integer ty) idx).nodes = idx.nodes+2 := by simp [Container.nodes] <;> omega
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t2 = liveS s := liveS_of_memory m b k'
  rw [nodes] at gpu
  by_cases grow : objectBuffer.capacity < n
  · have reserved := reserve_grow_ok t2.frame s.frame.bindings.length ty n (rowBinding R ty k) objectBuffer
      ⟨.integer ty,some R,none,[]⟩ resolved2 rfl object2 limit grow
    obtain ⟨t,run,tf,tw,tp,ts,tc,tm,tb,tbase,tpk,tst⟩ := finalState _
      ⟨{objectBuffer with capacity := n,epoch := objectBuffer.epoch+1},(),objectBuffer.items.length+1,
        objectBuffer.capacity+n+2⟩ reserved (by simp [Frame.updated,bindEq])
    refine ⟨t,⟨{objectBuffer with capacity := n,epoch := objectBuffer.epoch+1},(),
      objectBuffer.items.length+1,objectBuffer.capacity+n+2⟩,run,?_,Or.inl ⟨grow,rfl⟩,
      ts.trans sl,tc.trans sc',tm.trans m,tb.trans b,tbase.trans k',?_,?_,?_,?_,?_,?_⟩
    · rw [tf]; exact frameOf _
    · omega
    · omega
    · omega
    · rw [live] at tp
      omega
    · omega
    · have hst : s.frame.state.storage.peak ≤ t.frame.state.storage.peak := by
        rw [tst]; simp [Frame.updated,stateEq] <;> omega
      have st2 : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [stateEq]
      omega
  · have fits : n ≤ objectBuffer.capacity := by omega
    have reserved := reserve_keep_ok t2.frame s.frame.bindings.length ty n (rowBinding R ty k) objectBuffer
      ⟨.integer ty,some R,none,[]⟩ resolved2 rfl object2 fits
    obtain ⟨t,run,tf,tw,tp,ts,tc,tm,tb,tbase,tpk,tst⟩ := finalState _
      ⟨objectBuffer,(),1,objectBuffer.capacity+1⟩ reserved (by simp [Frame.updated,bindEq])
    refine ⟨t,⟨objectBuffer,(),1,objectBuffer.capacity+1⟩,run,?_,Or.inr ⟨fits,rfl⟩,
      ts.trans sl,tc.trans sc',tm.trans m,tb.trans b,tbase.trans k',?_,?_,?_,?_,?_,?_⟩
    · rw [tf]; exact frameOf _
    · omega
    · omega
    · omega
    · rw [live] at tp
      omega
    · omega
    · have hst : s.frame.state.storage.peak ≤ t.frame.state.storage.peak := by
        rw [tst]; simp [Frame.updated,stateEq] <;> omega
      have st2 : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [stateEq]
      omega

-- Successful evaluation with its value, counters and the reference bindings it adds.
def Ev (s : NState) (e : NExpr) (t : NState) (v : Int) (extra : List Binding) (w p : Nat) : Prop :=
  e.eval s = some (t,v) ∧ GoodF s t w p ∧ t.frame.bindings = s.frame.bindings ++ extra

theorem Ev.scalar {e : NExpr} {s : NState} {v : Int} (scalar : e.scalarOnly = true)
    (value : e.denote (envOf s) = some v) : ∃ t, Ev s e t v [] e.nodes e.nodes := by
  obtain ⟨t,ran,good⟩ := scalar_eval e s v scalar value
  exact ⟨t,ran,good.toF,by simp [good.1.1]⟩

theorem Ev.cast {ty : Ty} {operand : NExpr} {s t : NState} {v v' : Int} {extra : List Binding} {w p : Nat}
    (inner : Ev (s.charge 0 (operand.nodes+1)) operand t v extra w p) (converted : ty.convert v = some v') :
    Ev s (.cast ty operand) (t.charge 1 1) v' extra (w+1) (max (operand.nodes+1) (max p 1)) := by
  obtain ⟨ran,good,bindings⟩ := inner
  refine ⟨by simp [NExpr.eval,ran,converted],?_,by simpa using bindings⟩
  have := (GoodF.charge s 0 (operand.nodes+1)).trans (good.trans (GoodF.charge t 1 1))
  exact this.mono (by omega) (by omega)

theorem Ev.unary {ty : Ty} {op : Unary} {operand : NExpr} {s t : NState} {v v' : Int} {extra : List Binding} {w p : Nat}
    (inner : Ev (s.charge 0 (operand.nodes+1)) operand t v extra w p)
    (converted : ty.convert (unaryValue op v) = some v') :
    Ev s (.unary ty op operand) (t.charge 1 1) v' extra (w+1) (max (operand.nodes+1) (max p 1)) := by
  obtain ⟨ran,good,bindings⟩ := inner
  refine ⟨by simp [NExpr.eval,ran,converted],?_,by simpa using bindings⟩
  have := (GoodF.charge s 0 (operand.nodes+1)).trans (good.trans (GoodF.charge t 1 1))
  exact this.mono (by omega) (by omega)

theorem Ev.mono {s t : NState} {e : NExpr} {v : Int} {extra : List Binding} {w p w' p' : Nat}
    (ev : Ev s e t v extra w p) (hw : w ≤ w') (hp : p ≤ p') : Ev s e t v extra w' p' :=
  ⟨ev.1,ev.2.1.mono hw hp,ev.2.2⟩

theorem envOf_ev {s t : NState} {e : NExpr} {v : Int} {extra : List Binding} {w p : Nat}
    (ev : Ev s e t v extra w p) : envOf t = envOf s := envOf_goodF ev.2.1

-- `u` is `s` with extra reference bindings appended; nothing else changed.
def Ext (s u : NState) : Prop :=
  u.frame.state = s.frame.state ∧ u.frame.rootWritable = s.frame.rootWritable ∧
  (∃ extra, u.frame.bindings = s.frame.bindings ++ extra) ∧
  u.slots = s.slots ∧ u.scope = s.scope ∧ u.scalars.memory = s.scalars.memory ∧
  u.scalars.bindings = s.scalars.bindings ∧ u.scalars.baseMemory = s.scalars.baseMemory

theorem Ext.of_goodF {s t : NState} {w p : Nat} {extra : List Binding} (good : GoodF s t w p)
    (bindings : t.frame.bindings = s.frame.bindings ++ extra) : Ext s t :=
  ⟨good.1,good.2.1,⟨extra,bindings⟩,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1,good.2.2.2.2.2.1,
    good.2.2.2.2.2.2.1⟩

theorem Ext.charge (s : NState) (work temporaries : Nat) : Ext s (s.charge work temporaries) :=
  ⟨rfl,rfl,⟨[],by simp⟩,rfl,rfl,rfl,rfl,rfl⟩

theorem Ext.trans {a b c : NState} (x : Ext a b) (y : Ext b c) : Ext a c := by
  obtain ⟨s1,r1,⟨e1,b1⟩,sl1,sc1,m1,bi1,ba1⟩ := x
  obtain ⟨s2,r2,⟨e2,b2⟩,sl2,sc2,m2,bi2,ba2⟩ := y
  exact ⟨s2.trans s1,r2.trans r1,⟨e1++e2,by rw [b2,b1,List.append_assoc]⟩,sl2.trans sl1,sc2.trans sc1,
    m2.trans m1,bi2.trans bi1,ba2.trans ba1⟩

theorem container_nodes (slot : Nat) (ty : Ty) (idx : NExpr) :
    (Container.row (.local slot) (.integer ty) idx).nodes = idx.nodes+2 := by
  simp [Container.nodes]; omega

theorem Ev.readRow (s : NState) (slot rb : Nat) (idx pos : NExpr) (k j R w sc : Nat) (ty : Ty) (x : Int)
    (prev : Buffer Value) (extra2 : List Binding) (wp pp : Nat)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some prev)
    (item : prev.items[j]? = some (Value.integer x))
    (posEv : ∀ u, Ext s u → ∃ u2, Ev u pos u2 (j : Int) extra2 wp pp) :
    ∃ t, Ev s (.read ty (.row (.local slot) (.integer ty) idx) pos) t x ([rowBinding R ty k] ++ extra2)
      (idx.nodes+2+wp+1) (max (idx.nodes+pos.nodes+4) (max (idx.nodes+2) (max pp 2))) := by
  have nodes := container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) slot rb idx k R w sc ty
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) inside
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)).trans good1
  have ext1 : Ext s t1 := Ext.of_goodF g1 (by simpa using bindings1)
  obtain ⟨t2,hpos,goodp,bp⟩ := posEv t1 ext1
  have gAll := g1.trans goodp
  have stateEq : t2.frame.state = s.frame.state := gAll.1
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := gAll.2.1
  have bindEq : t2.frame.bindings = s.frame.bindings ++ ([rowBinding R ty k] ++ extra2) := by
    have : t1.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by simpa using bindings1
    rw [bp,this]; simp
  have g2 : RootGraph t2.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths2 : t2.frame.rootWritable.length = t2.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t2.frame.rootWritable[R]? = some true := by rw [rwEq]; exact flag
  have hb : t2.frame.bindings[s.frame.bindings.length]? = some (rowBinding R ty k) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row t2.frame s.frame.bindings.length R ty w sc k g2 hb
    lengths2 flag2 inside
  have sameBuffer : buffer = prev := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain⟩ := row_object t2.frame R ty w sc k g2 inside
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  obtain ⟨reference,hreference,hread⟩ := read_ok t2.frame s.frame.bindings.length ty j x (rowBinding R ty k)
    objectBuffer ⟨.integer ty,some R,none,[]⟩ true hb rfl resolved object
    (maximum_row t2.frame R ty w sc k g2 lengths2 flag2 inside) (fun _ => rfl) item
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+pos.nodes+2)) =
        some (t1,s.frame.bindings.length) := by simpa using hrow
  refine ⟨t2.charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,evalRow,hpos,hreference,hread]
  · have := gAll.trans (GoodF.charge t2 1 2)
    rw [nodes] at this
    refine this.mono (by omega) (by omega)
  · simpa using bindEq

-- `container[k].emplace_back(value)` on a row with spare capacity.
theorem append_row_stmt (s : NState) (slot rb : Nat) (idx value : NExpr) (k R w sc : Nat) (ty : Ty) (x : Int)
    (rowBuffer : Buffer Value) (extra : List Binding) (wv pv : Nat)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some rowBuffer)
    (room : rowBuffer.items.length < rowBuffer.capacity) (accepted : ty.valid x = true)
    (valueEv : ∀ u, Ext s u → ∃ u2, Ev u value u2 x extra wv pv) :
    ∃ t, (NStmt.append (.row (.local slot) (.integer ty) idx) ty value).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated (R+1+k) rowBuffer
        ⟨{rowBuffer with items := rowBuffer.items ++ [Value.integer x]},(),2,rowBuffer.capacity+2⟩ ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+idx.nodes+wv+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+max (idx.nodes+value.nodes+4)
        (max (idx.nodes+2) (max pv 1))) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have nodes := container_nodes slot ty idx
  have env0 : envOf (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row
    (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)) slot rb idx k R w sc ty
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) inside
  have g1 := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)).trans good1
  have bindings1' : t1.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by simpa using bindings1
  have ext1 : Ext s t1 := Ext.of_goodF g1 bindings1'
  obtain ⟨t2,hvalue,goodv,bv⟩ := valueEv t1 ext1
  have gAll := g1.trans goodv
  have stateEq : t2.frame.state = s.frame.state := gAll.1
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := gAll.2.1
  have bindEq : t2.frame.bindings = s.frame.bindings ++ ([rowBinding R ty k] ++ extra) := by
    rw [bv,bindings1']; simp
  have g2 : RootGraph t2.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths2 : t2.frame.rootWritable.length = t2.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag2 : t2.frame.rootWritable[R]? = some true := by rw [rwEq]; exact flag
  have hb : t2.frame.bindings[s.frame.bindings.length]? = some (rowBinding R ty k) := by
    simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row t2.frame s.frame.bindings.length R ty w sc k g2 hb
    lengths2 flag2 inside
  have sameBuffer : buffer = rowBuffer := by
    rw [stateEq,found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain⟩ := row_object t2.frame R ty w sc k g2 inside
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  have appended := append_ok t2.frame s.frame.bindings.length ty x (rowBinding R ty k) objectBuffer
    ⟨.integer ty,some R,none,[]⟩ resolved rfl object accepted room
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)) =
        some (t1,s.frame.bindings.length) := by simpa using hrow
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t2 = liveS s := liveS_of_memory m b k'
  rw [nodes] at gpu
  let result : Result Value Unit :=
    ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x]},(),2,objectBuffer.capacity+2⟩
  have appended' : t2.frame.append s.frame.bindings.length ty x = some (t2.frame.updated (rowBinding R ty k).owner objectBuffer result) := appended
  refine ⟨(({t2 with frame := t2.frame.updated (rowBinding R ty k).owner objectBuffer result} : NState).release s).charge 1 1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,evalRow,hvalue,appended']
  · simp [NState.release,Frame.updated,bindEq,stateEq,rwEq,rowBinding,result]
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp [charge_work]; omega
  · simp [charge_work]; omega
  · simp [charge_scalar_peak,liveS] ; omega
  · simp only [liveS] at gpu live
    simp [charge_scalar_peak,m,b,k']
    unfold liveS
    omega
  · exact (peak_after t2 {t2 with frame := t2.frame.updated (rowBinding R ty k).owner objectBuffer result} s 1 1
      rfl rfl (by simp [Frame.updated] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after t2 {t2 with frame := t2.frame.updated (rowBinding R ty k).owner objectBuffer result} s 1 1
      rfl rfl (by simp [Frame.updated] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).2

-- `container[k].assign(v.begin(), v.end())` from a distinct root `v`.
theorem assign_range_stmt (s : NState) (slot rb source vb : Nat) (idx : NExpr) (k R w sc V vsc : Nat)
    (ty : Ty) (wV : Bool) (maximum : Bool) (rowBuffer vBuffer : Buffer Value)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb) (hsource : s.vectorSlot source = some vb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (vbinding : s.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some rowBuffer)
    (vtag : s.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : s.frame.state.storage.lookup V = some vBuffer)
    (vflag : s.frame.rootWritable[V]? = some maximum) (vpermission : wV = true → maximum = true)
    (before : V < R) (limit : vBuffer.items.length ≤ rowBuffer.limit) :
    ∃ t, (NStmt.assignRange (.row (.local slot) (.integer ty) idx) source source ty false true).run s =
        some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated (R+1+k) rowBuffer
        (CppVectorRange.assignResult rowBuffer vBuffer 0 vBuffer.items.length) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+idx.nodes+8 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+idx.nodes+9) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have nodes := container_nodes slot ty idx
  have env0 : envOf (s.charge 6 ((Container.row (.local slot) (.integer ty) idx).nodes+7)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have slot0 : (s.charge 6 ((Container.row (.local slot) (.integer ty) idx).nodes+7)).vectorSlot slot =
      some rb := by simpa [NState.vectorSlot] using hslot
  obtain ⟨t1,hrow,good1,bindings1⟩ := eval_row
    (s.charge 6 ((Container.row (.local slot) (.integer ty) idx).nodes+7)) slot rb idx k R w sc ty
    idxScalar (by rw [env0]; exact idxValue) slot0 (by simpa using binding) (by simpa using g)
    (by simpa using lengths) (by simpa using flag) inside
  have g1 := (GoodF.charge s 6 ((Container.row (.local slot) (.integer ty) idx).nodes+7)).trans good1
  have bindings1' : t1.frame.bindings = s.frame.bindings ++ [rowBinding R ty k] := by simpa using bindings1
  have stateEq : t1.frame.state = s.frame.state := g1.1
  have rwEq : t1.frame.rootWritable = s.frame.rootWritable := g1.2.1
  have slotEq : t1.slots = s.slots := g1.2.2.1
  have g1' : RootGraph t1.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths1 : t1.frame.rootWritable.length = t1.frame.state.forest.objects.length := by
    rw [rwEq,stateEq]; exact lengths
  have flag1 : t1.frame.rootWritable[R]? = some true := by rw [rwEq]; exact flag
  -- the target row
  have hb : t1.frame.bindings[s.frame.bindings.length]? = some (rowBinding R ty k) := by simp [bindings1']
  obtain ⟨rowBuf,resolvedRow,foundRow⟩ := resolve_row t1.frame s.frame.bindings.length R ty w sc k g1' hb
    lengths1 flag1 inside
  have sameRow : rowBuf = rowBuffer := by
    rw [stateEq,found] at foundRow
    exact (Option.some.inj foundRow).symm
  subst sameRow
  obtain ⟨rowObjectBuffer,rowObject,foundAgain⟩ := row_object t1.frame R ty w sc k g1' inside
  have sameObject : rowObjectBuffer = rowBuf := by
    rw [foundRow] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  -- the source root
  have vobject : t1.frame.object V (.integer ty) = some (vBuffer,⟨.integer ty,none,some vsc,[]⟩) :=
    object_runs t1.frame V _ vBuffer _ g1'.valid (by rw [stateEq]; exact vfound) (by rw [stateEq]; exact vtag) rfl
  have vrooted : t1.frame.state.forest.rootOwner V = some V :=
    CppVectorOwnership.root_runs _ V _ (by rw [stateEq]; exact vtag) rfl
  have vmax : t1.frame.maximum V = some maximum :=
    maximum_runs t1.frame V V maximum lengths1 vrooted (by rw [rwEq]; exact vflag)
  have vbinding1 : t1.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩ := by
    have inRange : vb < s.frame.bindings.length := (List.getElem?_eq_some_iff.mp vbinding).1
    rw [bindings1',List.getElem?_append_left inRange]; exact vbinding
  have vresolved : t1.frame.resolve vb (.integer ty) = some (⟨V,.integer ty,wV,.root vsc⟩,vBuffer) :=
    resolve_root t1.frame vb _ _ vsc vBuffer _ maximum vbinding1 rfl rfl vobject rfl rfl vmax vpermission
  obtain ⟨vvalid,vowner,vbufferValid,_,_⟩ := buffer_facts t1.frame V ty vBuffer _ vobject
  have iterator := iterator_whole t1.frame vb ty _ vBuffer vresolved vbufferValid
  have distinct : rowObjectBuffer.owner ≠ vBuffer.owner := by
    obtain ⟨_,rowOwner,_,_,_⟩ := buffer_facts t1.frame (R+1+k) ty rowObjectBuffer _ rowObject
    rw [rowOwner,vowner]; omega
  have assigned := assign_ok t1.frame s.frame.bindings.length vb ty ⟨vBuffer.owner,vBuffer.epoch,0,vBuffer.items.length⟩
    0 vBuffer.items.length (rowBinding R ty k) ⟨V,.integer ty,wV,.root vsc⟩ rowObjectBuffer vBuffer _
    resolvedRow vresolved rfl rowObject ⟨_,vobject⟩ distinct rfl (by rw [vowner]) (by omega) (by omega)
    (by simpa using limit)
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 6 ((Container.row (.local slot) (.integer ty) idx).nodes+7)) =
        some (t1,s.frame.bindings.length) := by simpa using hrow
  have sourceSlot : t1.vectorSlot source = some vb := by
    simpa [NState.vectorSlot,slotEq] using hsource
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := g1
  generalize CppVectorRange.assignResult rowObjectBuffer vBuffer 0 vBuffer.items.length = result at assigned ⊢
  refine ⟨({t1 with frame := t1.frame.updated (rowBinding R ty k).owner rowObjectBuffer result} : NState).release s,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,evalRow,sourceSlot,iterator,assigned]
  · simp [NState.release,Frame.updated,bindings1',stateEq,rwEq,rowBinding]
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; rw [nodes] at gpu; unfold liveS at gpu ⊢; omega
  · simp [NState.release]; omega
  · have st1 : t1.frame.state.storage.peak = s.frame.state.storage.peak := by rw [stateEq]
    rw [st1] at gqu
    simp [NState.release,Frame.updated,stateEq]
    omega

-- `v.size()` and `v[j]` for a caller root vector `v`.
theorem Ev.sizeRoot (s : NState) (slot vb V vsc : Nat) (ty : Ty) (wV maximum : Bool) (vBuffer : Buffer Value)
    (hslot : s.vectorSlot slot = some vb) (vbinding : s.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩)
    (valid : s.frame.state.wellFormed = true)
    (vtag : s.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : s.frame.state.storage.lookup V = some vBuffer)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (vflag : s.frame.rootWritable[V]? = some maximum) (vpermission : wV = true → maximum = true)
    (small : vBuffer.items.length < 2^64) :
    ∃ t, Ev s (.size (.integer ty) (.local slot)) t (vBuffer.items.length : Int) [] 3 3 := by
  obtain ⟨resolved,object,_⟩ := resolve_vroot s.frame vb V vsc ty wV maximum vBuffer vbinding valid vtag vfound
    lengths vflag vpermission
  have sized : (⟨64,false,false⟩ : Ty).valid (vBuffer.items.length : Int) = true := by
    simp [Ty.valid]; omega
  have size := CppNestedOps.size_runs s.frame vb (.integer ty) _ vBuffer resolved sized
  have container := eval_local (s.charge 0 ((Container.local slot).nodes+2)) slot vb
    (by simpa [NState.vectorSlot] using hslot)
  refine ⟨((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,container,size]
    rfl
  · have := ((GoodF.charge s 0 ((Container.local slot).nodes+2)).trans (GoodF.charge _ 1 1)).trans
      (GoodF.charge (((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1)) 1 2)
    exact this.mono (by simp [Container.nodes]) (by simp [Container.nodes])
  · simp

theorem Ev.readRoot (s : NState) (slot vb V vsc : Nat) (index : NExpr) (j : Nat) (ty : Ty)
    (wV maximum : Bool) (vBuffer : Buffer Value) (x : Int)
    (indexScalar : index.scalarOnly = true) (indexValue : index.denote (envOf s) = some (j : Int))
    (hslot : s.vectorSlot slot = some vb) (vbinding : s.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩)
    (valid : s.frame.state.wellFormed = true)
    (vtag : s.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : s.frame.state.storage.lookup V = some vBuffer)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (vflag : s.frame.rootWritable[V]? = some maximum) (vpermission : wV = true → maximum = true)
    (item : vBuffer.items[j]? = some (Value.integer x)) :
    ∃ t, Ev s (.read ty (.local slot) index) t x [] (index.nodes+3) (index.nodes+3) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame vb V vsc ty wV maximum vBuffer vbinding valid vtag vfound
    lengths vflag vpermission
  have env0 : envOf (s.charge 0 ((Container.local slot).nodes+index.nodes+2)) = envOf s :=
    envOf_core (core_charge _ _ _)
  have container := eval_local (s.charge 0 ((Container.local slot).nodes+index.nodes+2)) slot vb
    (by simpa [NState.vectorSlot] using hslot)
  have env1 : envOf ((s.charge 0 ((Container.local slot).nodes+index.nodes+2)).charge 1 1) = envOf s :=
    (envOf_core (core_charge _ _ _)).trans env0
  obtain ⟨t1,hidx,good1⟩ := scalar_eval index _ j indexScalar (by rw [env1]; exact indexValue)
  have frame1 : t1.frame = s.frame := by simpa using good1.1.1
  obtain ⟨reference,hreference,hread⟩ := read_ok s.frame vb ty j x ⟨V,.integer ty,wV,.root vsc⟩ vBuffer
    ⟨.integer ty,none,some vsc,[]⟩ maximum vbinding rfl resolved object vmax vpermission item
  refine ⟨t1.charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,container,hidx,frame1,hreference,hread]
  · have := ((GoodF.charge s 0 ((Container.local slot).nodes+index.nodes+2)).trans (GoodF.charge _ 1 1)).trans
      (good1.toF.trans (GoodF.charge t1 1 2))
    exact this.mono (by simp [Container.nodes]; omega) (by simp [Container.nodes]; omega)
  · simp [frame1]

def _root_.Proofs.CppNestedProgram.NState.rowsDeclared (x : NState) (frame : Frame) (binding : Nat) : NState :=
  {x with frame := frame,slots := x.slots ++ [.vector binding]}

-- `std::vector<std::vector<T>> name(count)` as a writable local.
theorem construct_rows_stmt (s : NState) (count : NExpr) (w : Nat) (ty : Ty)
    (scalar : count.scalarOnly = true) (value : count.denote (envOf s) = some (w : Int))
    (supported : CppVectorBindings.supported ty) (limit : w ≤ rowLimit)
    (valid : s.frame.state.wellFormed = true)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length) :
    ∃ t next, s.frame.state.constructRows ty s.scope w = some next ∧
      (NStmt.constructRows ty true count).run s = some ⟨t,none,false⟩ ∧
      t.frame = ⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,
        s.frame.bindings ++ [⟨s.frame.state.storage.objects.length,.vector (.integer ty),true,.root s.scope⟩]⟩ ∧
      t.slots = s.slots ++ [.vector s.frame.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ∧ t.scalars.bindings = s.scalars.bindings ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+count.nodes+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+count.nodes) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨t0,ran,good⟩ := scalar_eval count s w scalar value
  have frame0 : t0.frame = s.frame := good.1.1
  have scope0 : t0.scope = s.scope := good.1.2.2.1
  obtain ⟨lengthsEq,_,_⟩ := wellFormed_parts s.frame.state valid
  have constructed : s.frame.state.constructRows ty s.scope w =
      some ⟨s.frame.state.forest.constructRows ty s.scope w,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ some (rootBuffer s.frame.state.storage.objects.length w) ::
            (List.range w).map fun j => some (rowBuffer ty (s.frame.state.storage.objects.length+1+j)),
          work := s.frame.state.storage.work+w+1,
          peak := max s.frame.state.storage.peak
            (s.frame.state.liveSpace+(w+2)-s.frame.state.storage.baseSpace)}⟩ := by
    simp [CppNestedVectorStore.State.constructRows,valid,supported,limit]
  generalize hnext : (⟨s.frame.state.forest.constructRows ty s.scope w,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ some (rootBuffer s.frame.state.storage.objects.length w) ::
            (List.range w).map fun j => some (rowBuffer ty (s.frame.state.storage.objects.length+1+j)),
          work := s.frame.state.storage.work+w+1,
          peak := max s.frame.state.storage.peak
            (s.frame.state.liveSpace+(w+2)-s.frame.state.storage.baseSpace)}⟩ : CppNestedVectorStore.State) = next at constructed
  have nextValid := constructRows_state_wellFormed s.frame.state ty s.scope w next constructed
  have nextPeak : s.frame.state.storage.peak ≤ next.storage.peak := by
    rw [← hnext]; simp <;> omega
  obtain ⟨_,_,_,gst,_,_,gql,gqu⟩ := id good
  have st0 : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [gst]
  have forestEq := constructRows_forest _ ty s.scope w next constructed
  have rootTagLookup : next.forest.lookup s.frame.state.storage.objects.length =
      some (rootTag ty s.scope s.frame.state.storage.objects.length w) := by
    rw [forestEq,← lengthsEq]
    exact constructRows_root s.frame.state.forest ty s.scope w
  have rootFound := constructRows_storage_root _ ty s.scope w next constructed
  have newLength : next.forest.objects.length = s.frame.state.forest.objects.length+1+w := by
    rw [forestEq,constructRows_length]
  have gobject : (⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings⟩ : Frame).object
      s.frame.state.storage.objects.length (.vector (.integer ty)) =
        some (rootBuffer s.frame.state.storage.objects.length w,
          rootTag ty s.scope s.frame.state.storage.objects.length w) :=
    object_runs _ _ _ _ _ nextValid rootFound rootTagLookup rfl
  have glengths : (s.frame.rootWritable ++ [true] ++ List.replicate w false).length = next.forest.objects.length := by
    simp [newLength,lengths]; omega
  have gflag : (s.frame.rootWritable ++ [true] ++ List.replicate w false)[s.frame.state.storage.objects.length]? =
      some true := by
    have : s.frame.rootWritable.length = s.frame.state.storage.objects.length := by omega
    simp [List.append_assoc,List.getElem?_append_right,this]
  have gmax : (⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings⟩ : Frame).maximum
      s.frame.state.storage.objects.length = some true :=
    maximum_runs _ _ s.frame.state.storage.objects.length true glengths
      (CppVectorOwnership.root_runs _ _ _ rootTagLookup rfl) gflag
  have bound : (⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings⟩ : Frame).bindRoot
      s.frame.state.storage.objects.length (.vector (.integer ty)) s.scope true =
        some ((⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings⟩ : Frame).addBinding
          ⟨s.frame.state.storage.objects.length,.vector (.integer ty),true,.root s.scope⟩) := by
    simp only [Frame.bindRoot,gobject,gmax,Bind.bind,Option.bind]
    simp [rootTag]
  have release : (t0.release s).frame = s.frame := by simp [NState.release,frame0]
  have releaseScope : (t0.release s).scope = s.scope := by simp [scope0]
  have nonneg : (0 : Int) ≤ w := by omega
  have grownFrame : ∀ rb : Binding, (⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings⟩ : Frame).addBinding rb =
      (⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,s.frame.bindings ++ [rb]⟩,s.frame.bindings.length) := by
    intro rb; rfl
  rw [grownFrame] at bound
  have bound2 := bound
  simp only [List.append_assoc,List.singleton_append] at bound2
  refine ⟨(((t0.release s).rowsDeclared ⟨next,s.frame.rootWritable ++ [true] ++ List.replicate w false,
      s.frame.bindings ++ [⟨s.frame.state.storage.objects.length,.vector (.integer ty),true,.root s.scope⟩]⟩
      s.frame.bindings.length)).charge 3 0,next,constructed,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,ran,nonneg,constructed,bound2,NState.rowsDeclared,NState.release,frame0,scope0]
  · simp [NState.rowsDeclared,NState.release,frame0]
  · simp [NState.rowsDeclared,good.1.2.1]
  · simp [NState.rowsDeclared,scope0]
  · simp [NState.rowsDeclared,good.1.2.2.2.1]
  · simp [NState.rowsDeclared,good.1.2.2.2.2.1]
  · simp [NState.rowsDeclared,good.1.2.2.2.2.2]
  · simp [NState.rowsDeclared,charge_work]; have := good.2.1; omega
  · simp [NState.rowsDeclared,charge_work]; have := good.2.2.1; omega
  · simp [NState.rowsDeclared,charge_scalar_peak]; have := good.2.2.2.2.1; omega
  · simp [NState.rowsDeclared,charge_scalar_peak,liveS]
    have := good.2.2.2.2.2
    have live : liveS t0 = liveS s := liveS_core good.1
    unfold liveS at this live
    omega
  · simp [NState.rowsDeclared,charge_peak,NState.release]; omega
  · simp [NState.rowsDeclared,charge_peak,charge_scalar_peak,NState.release,frame0]
    rw [st0] at gqu
    omega

-- A scalar-only statement leaves the frame untouched.
theorem release_self {t0 s : NState} (frame : t0.frame = s.frame) : t0.release s = t0 := by
  obtain ⟨scalars,f,slots,scope,peak⟩ := t0
  simp only [] at frame
  subst frame
  simp [NState.release]

theorem check_good (e : NExpr) (s : NState) (v : Int) (scalar : e.scalarOnly = true)
    (value : e.denote (envOf s) = some v) (nonzero : v ≠ 0) :
    ∃ t, (NStmt.check e).run s = some ⟨t,none,false⟩ ∧ Good s t (e.nodes+1) (e.nodes) := by
  obtain ⟨t0,ran,good⟩ := scalar_eval e s v scalar value
  have run := check_run e s t0 v ran nonzero
  rw [release_self good.1.1] at run
  exact ⟨_,run,(good.trans (Good.charge t0 1 0)).mono (by omega) (by omega)⟩

theorem nodes_pos (e : NExpr) : 1 ≤ e.nodes := by
  cases e <;> simp [NExpr.nodes] <;> omega

-- Declaring a scalar local from a scalar expression.
theorem declare_good (e : NExpr) (ty : Ty) (writable : Bool) (s : NState) (v v' : Int)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf s) = some v) (converted : ty.convert v = some v') :
    ∃ t, (NStmt.declare ty writable e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame ∧ t.slots = s.slots ++ [.scalar s.scalars.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ++ [⟨ty,v'⟩] ∧
      t.scalars.bindings = s.scalars.bindings ++ [⟨s.scalars.memory.length,writable⟩] ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+e.nodes+1 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes+1) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨t0,ran,good⟩ := scalar_eval e s v scalar value
  have run := declare_run e ty writable s t0 v v' ran converted
  rw [release_self good.1.1] at run
  obtain ⟨⟨f,sl,sc,m,b,k⟩,l,u,st,pl,pu,ql,qu⟩ := good
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NState.declared,f]
  · simp [NState.declared,sl,b]
  · simp [NState.declared,sc]
  · simp [NState.declared,m]
  · simp [NState.declared,b,m]
  · simp [NState.declared,k]
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_scalar_peak]; omega
  · have pos := nodes_pos e
    simp [NState.declared,charge_scalar_peak,liveS,m,b,k]; unfold liveS at pu; omega
  · simp [NState.declared,charge_peak]; omega
  · simp [NState.declared,charge_peak,charge_scalar_peak,f]
    have st' : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [st]
    simp [f] at qu
    omega

-- Assigning to a writable scalar local.
theorem assign_good (e : NExpr) (slot idx : Nat) (ty : Ty) (s : NState) (v v' : Int)
    (binding : CppState.Binding) (cell : CppState.Cell)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf s) = some v) (converted : ty.convert v = some v')
    (hs : s.slots[slot]? = some (.scalar idx)) (hb : s.scalars.bindings[idx]? = some binding)
    (hm : s.scalars.memory[binding.address]? = some cell) (ctype : cell.type = ty)
    (cvalid : ty.valid cell.value = true) (writable : binding.writable = true) :
    ∃ t, (NStmt.assign slot ty e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame ∧ t.slots = s.slots ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory.set binding.address ⟨ty,v'⟩ ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+e.nodes+1 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) ∧
      liveS t = liveS s := by
  obtain ⟨t0,ran,good⟩ := scalar_eval e s v scalar value
  have self := release_self good.1.1
  have cellFound : (t0.release s).scalarCell slot ty = some (binding,cell) := by
    rw [self]
    obtain ⟨⟨f,sl,sc,m,b,k⟩,_⟩ := good
    simp [NState.scalarCell,NState.scalarSlot,sl,b,m,hs,hb,hm,ctype,cvalid]
  have run := assign_run e slot ty s t0 v v' binding cell ran cellFound writable converted
  rw [self] at run
  obtain ⟨⟨f,sl,sc,m,b,k⟩,l,u,st,pl,pu,ql,qu⟩ := good
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using f
  · simpa using sl
  · simpa using sc
  · simp [m,ctype]
  · simpa using b
  · simpa using k
  · simp [charge_work]; omega
  · simp [charge_work]; omega
  · simp [charge_scalar_peak]; omega
  · simp [charge_scalar_peak,liveS,m,b,k]
    have mlen : (s.scalars.memory.set binding.address ⟨ty,v'⟩).length = s.scalars.memory.length := by simp
    simp [mlen]
    unfold liveS at pu; omega
  · simp [charge_peak]; omega
  · simp [charge_peak,charge_scalar_peak,f]
    have st' : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [st]
    simp [f] at qu
    omega
  · simp [liveS,m,b,k]

theorem Ev.binary {ty : Ty} {op : Binary} {left right : NExpr} {s t1 t2 : NState} {a b v : Int}
    {extra1 extra2 : List Binding} {w1 p1 w2 p2 : Nat}
    (first : Ev (s.charge 0 (left.nodes+right.nodes+1)) left t1 a extra1 w1 p1)
    (second : Ev t1 right t2 b extra2 w2 p2) (converted : ty.convert (binaryValue op a b) = some v) :
    Ev s (.binary ty op left right) (t2.charge 1 1) v (extra1 ++ extra2)
      (w1+w2+1) (max (left.nodes+right.nodes+1) (max (max p1 p2) 1)) := by
  obtain ⟨ran1,good1,bind1⟩ := first
  obtain ⟨ran2,good2,bind2⟩ := second
  refine ⟨by simp [NExpr.eval,ran1,ran2,converted],?_,?_⟩
  · have := ((GoodF.charge s 0 (left.nodes+right.nodes+1)).trans (good1.trans good2)).trans (GoodF.charge t2 1 1)
    exact this.mono (by omega) (by omega)
  · simp only [charge_frame_bindings]
    rw [bind2,bind1]; simp

-- A condition that may read vectors: checks pass when the value is nonzero.
theorem check_ev (e : NExpr) (s t : NState) (v : Int) (extra : List Binding) (w p : Nat)
    (ev : Ev s e t v extra w p) (nonzero : v ≠ 0) :
    ∃ r, (NStmt.check e).run s = some ⟨r,none,false⟩ ∧ r = (t.release s).charge 1 0 := by
  exact ⟨_,check_run e s t v ev.1 nonzero,rfl⟩

theorem declare_ev (e : NExpr) (ty : Ty) (writable : Bool) (s t : NState) (v v' : Int) (extra : List Binding)
    (w p : Nat) (ev : Ev s e t v extra w p) (converted : ty.convert v = some v') :
    (NStmt.declare ty writable e).run s = some ⟨((t.release s).declared ty writable v').charge 1 0,none,false⟩ :=
  declare_run e ty writable s t v v' ev.1 converted

end Proofs.CppNestedStmt
