import Proofs.DoublingNested


namespace Proofs.DoublingPrologue
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested
open Proofs.CppState (Cell)

-- Appending objects never changes the root of an existing owner.
theorem rootOwner_extend (f g : Forest) (mono : ∀ i t, f.lookup i = some t → g.lookup i = some t) :
    ∀ owner root, f.rootOwner owner = some root → g.rootOwner owner = some root := by
  intro owner
  induction owner using Nat.strongRecOn with
  | _ owner ih =>
    intro root h
    rw [Forest.rootOwner] at h ⊢
    cases hl : f.lookup owner with
    | none => simp [hl] at h
    | some tag =>
      have hg := mono owner tag hl
      simp only [hl,hg,Bind.bind,Option.bind] at h ⊢
      generalize tag.parent = pp at h ⊢
      cases pp with
      | none => exact h
      | some parent =>
        by_cases less : parent < owner
        · simp only [less,ite_true] at h ⊢
          exact ih parent less root h
        · simp [less] at h

theorem rootOwner_eq (f : Forest) (owner : Nat) : f.rootOwner owner = (do
    let tag ← f.lookup owner
    match tag.parent with
    | none => some owner
    | some parent => if parent < owner then f.rootOwner parent else none) := by
  rw [Forest.rootOwner]
  rfl

theorem rootOwner_agree (f g : Forest) (n : Nat) (agree : ∀ i, i < n → g.lookup i = f.lookup i) :
    ∀ owner, owner < n → g.rootOwner owner = f.rootOwner owner := by
  intro owner
  induction owner using Nat.strongRecOn with
  | _ owner ih =>
    intro inside
    rw [rootOwner_eq g,rootOwner_eq f,agree owner inside]
    cases hl : f.lookup owner with
    | none => rfl
    | some tag =>
      simp only [Bind.bind,Option.bind]
      generalize tag.parent = pp
      cases pp with
      | none => rfl
      | some parent =>
        by_cases less : parent < owner
        · simp only [less,ite_true]
          exact ih parent less (by omega)
        · simp [less]

theorem rootOwner_le (f : Forest) : ∀ owner r, f.rootOwner owner = some r → r ≤ owner := by
  intro owner
  induction owner using Nat.strongRecOn with
  | _ owner ih =>
    intro r h
    rw [rootOwner_eq] at h
    cases hl : f.lookup owner with
    | none => simp [hl] at h
    | some tag =>
      simp only [hl,Bind.bind,Option.bind] at h
      generalize tag.parent = pp at h
      cases pp with
      | none => cases h; exact Nat.le_refl _
      | some parent =>
        by_cases less : parent < owner
        · simp only [less,ite_true] at h
          have := ih parent less r h
          omega
        · simp [less] at h

theorem context_agree (f g : Forest) (n : Nat) (agree : ∀ i, i < n → g.lookup i = f.lookup i)
    (owner : Nat) (inside : owner < n) : g.context owner = f.context owner := by
  have root := rootOwner_agree f g n agree owner inside
  simp only [Forest.context,root]
  cases hr : f.rootOwner owner with
  | none => rfl
  | some r =>
    have le := rootOwner_le f owner r hr
    simp only [Bind.bind,Option.bind]
    rw [agree r (by omega)]

-- Every owner of the extended forest is either an old owner or in the new tree.
theorem construct_ctx (T next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat)
    (ran : T.constructRows ty scope count = some next) (owner context : Nat)
    (h : next.forest.context owner = some context) :
    (T.forest.context owner = some context) ∨
      (next.forest.rootOwner owner = some T.forest.objects.length ∧ context = scope) := by
  have forestEq := constructRows_forest T ty scope count next ran
  rw [forestEq] at h
  rw [forestEq]
  by_cases old : owner < T.forest.objects.length
  · have agree : ∀ i, i < T.forest.objects.length →
        (T.forest.constructRows ty scope count).lookup i = T.forest.lookup i :=
      fun i hi => constructRows_old T.forest ty scope count i hi
    rw [context_agree T.forest _ _ agree owner old] at h
    exact Or.inl h
  · have rootRoot : (T.forest.constructRows ty scope count).rootOwner T.forest.objects.length =
        some T.forest.objects.length := by
      rw [rootOwner_eq]
      simp [constructRows_root,rootTag]
    by_cases isRoot : owner = T.forest.objects.length
    · subst isRoot
      simp [Forest.context,rootRoot,constructRows_root,rootTag] at h
      exact Or.inr ⟨rootRoot,by omega⟩
    · by_cases isRow : owner < T.forest.objects.length+1+count
      · obtain ⟨j,hj⟩ : ∃ j, owner = T.forest.objects.length+1+j := ⟨owner-T.forest.objects.length-1,by omega⟩
        have jc : j < count := by omega
        have rowRoot : (T.forest.constructRows ty scope count).rootOwner owner =
            some T.forest.objects.length := by
          rw [rootOwner_eq,hj,constructRows_row T.forest ty scope count j jc]
          simp only [Bind.bind,Option.bind,rowTag]
          have lt : T.forest.objects.length < T.forest.objects.length+1+j := by omega
          simp only [lt,ite_true]
          exact rootRoot
        simp [Forest.context,rowRoot,constructRows_root,rootTag] at h
        exact Or.inr ⟨rowRoot,by omega⟩
      · have absent : (T.forest.constructRows ty scope count).lookup owner = none := by
          simp only [Forest.lookup]
          have : (T.forest.constructRows ty scope count).objects[owner]? = none :=
            List.getElem?_eq_none (by rw [constructRows_length]; omega)
          simp [this]
        have ro : (T.forest.constructRows ty scope count).rootOwner owner = none := by
          rw [rootOwner_eq,absent]; rfl
        simp [Forest.context,ro] at h

-- A fresh root and its rows never lower the scope bound.
theorem bnd_construct (T next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat)
    (ran : T.constructRows ty scope count = some next)
    (strict : ∀ owner c, T.forest.context owner = some c → c < scope) : Bnd next scope := by
  have forestEq := constructRows_forest T ty scope count next ran
  refine ⟨fun owner context h => ?_,T.forest.objects.length,fun owner h => ?_⟩
  · rcases construct_ctx T next ty scope count ran owner context h with old | ⟨_,eq⟩
    · have := strict owner context old; omega
    · omega
  · rcases construct_ctx T next ty scope count ran owner scope h with old | ⟨root,_⟩
    · have := strict owner scope old; omega
    · exact root

theorem Frame.eq_of (f g : Frame) (h1 : f.state = g.state) (h2 : f.rootWritable = g.rootWritable)
    (h3 : f.bindings = g.bindings) : f = g := by
  cases f; cases g; simp_all

-- An evaluation that binds no reference leaves everything but the counters alone.
theorem Ev.good {s t : NState} {e : NExpr} {v : Int} {w p : Nat} (ev : Ev s e t v [] w p) : Good s t w p := by
  obtain ⟨ran,⟨state,rw,sl,sc,me,bi,ba,l,u,pl,pu,ql,qu⟩,bindings⟩ := ev
  have frame : t.frame = s.frame := Frame.eq_of _ _ state rw (by simpa using bindings)
  refine ⟨⟨frame,sl,sc,me,bi,ba⟩,l,u,by rw [frame],pl,pu,ql,qu⟩

theorem Ev.eval {s t : NState} {e : NExpr} {v : Int} {extra : List Binding} {w p : Nat}
    (ev : Ev s e t v extra w p) : e.eval s = some (t,v) := ev.1

theorem check_of_ev (e : NExpr) (s t : NState) (v : Int) (w p : Nat) (ev : Ev s e t v [] w p) (nonzero : v ≠ 0) :
    ∃ r, (NStmt.check e).run s = some ⟨r,none,false⟩ ∧ Good s r (w+1) p := by
  have good := Ev.good ev
  have run := check_run e s t v ev.1 nonzero
  rw [release_self good.1.1] at run
  exact ⟨_,run,(good.trans (Good.charge t 1 0)).mono (by omega) (by omega)⟩

theorem declare_of_good (e : NExpr) (ty : Ty) (writable : Bool) (s t0 : NState) (v v' : Int) (w p : Nat)
    (ran : e.eval s = some (t0,v)) (good : Good s t0 w p) (hp : 1 ≤ p) (converted : ty.convert v = some v') :
    ∃ t, (NStmt.declare ty writable e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame ∧ t.slots = s.slots ++ [.scalar s.scalars.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ++ [⟨ty,v'⟩] ∧
      t.scalars.bindings = s.scalars.bindings ++ [⟨s.scalars.memory.length,writable⟩] ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+w+1 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+p+1) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
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
  · simp [NState.declared,charge_scalar_peak,liveS,m,b,k]; unfold liveS at pu; omega
  · simp [NState.declared,charge_peak]; omega
  · simp [NState.declared,charge_peak,charge_scalar_peak,f]
    have st' : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [st]
    simp [f] at qu
    omega

-- Facts about the frame that survive every statement of the prologue that does not touch vectors.
structure VF (F : Fixed) (L0 T0 : Nat) (fr : Frame) : Prop where
  valid : fr.state.wellFormed = true
  vtag : fr.state.forest.lookup F.V = some ⟨.integer i32,none,some F.vsc,[]⟩
  vfound : fr.state.storage.lookup F.V = some F.vbuf
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  flag : ∃ m, fr.rootWritable[F.V]? = some m
  strict : ∀ owner c, fr.state.forest.context owner = some c → c < F.sc
  live : fr.state.liveSpace = L0
  work : fr.state.storage.work = T0
  rootId : F.R = fr.state.storage.objects.length

theorem VF.fresh {F : Fixed} {L0 T0 scope : Nat} {fr : Frame} (vf : VF F L0 T0 fr) (hsc : F.sc ≤ scope) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := vf.strict owner _ h
  omega

theorem VF.of_eq {F : Fixed} {L0 T0 : Nat} {S t : NState} (vf : VF F L0 T0 S.frame) (frame : t.frame = S.frame) :
    VF F L0 T0 t.frame := by rw [frame]; exact vf

-- Counters carried through the prologue.
structure Cb (F : Fixed) (W : Nat) (S : NState) : Prop where
  work : S.scalars.work ≤ W
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

theorem Cb.good {F : Fixed} {W w p : Nat} {S t : NState} (cb : Cb F W S) (good : Good S t w p)
    (cap : liveS S+p ≤ F.SPB) : Cb F (W+w) t := by
  obtain ⟨_,l,u,st,pl,pu,ql,qu⟩ := good
  have sp : t.scalars.peak ≤ F.SPB := by have := cb.scalarPeak; omega
  have stp : t.frame.state.storage.peak ≤ F.TPB := by rw [st]; exact cb.storagePeak
  refine ⟨by have := cb.work; omega,sp,stp,?_⟩
  have := cb.outerPeak
  omega

theorem Cb.mono {F : Fixed} {W W' : Nat} {S : NState} (cb : Cb F W S) (le : W ≤ W') : Cb F W' S :=
  ⟨by have := cb.work; omega,cb.scalarPeak,cb.storagePeak,cb.outerPeak⟩

theorem Cb.step {F : Fixed} {W w p : Nat} {S t : NState} (cb : Cb F W S) (frame : t.frame = S.frame)
    (wu : t.scalars.work ≤ S.scalars.work+w) (pu : t.scalars.peak ≤ max S.scalars.peak (liveS S+p))
    (cap : liveS S+p ≤ F.SPB)
    (qu : t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak)) : Cb F (W+w) t := by
  have sp : t.scalars.peak ≤ F.SPB := by have := cb.scalarPeak; omega
  have stp : t.frame.state.storage.peak ≤ F.TPB := by rw [frame]; exact cb.storagePeak
  refine ⟨by have := cb.work; omega,sp,stp,?_⟩
  have := cb.outerPeak
  omega

-- Shape of the scalar part of the prologue states; the frame holds only `v`.
structure PS (F : Fixed) (scope : Nat) (rw0 : List Bool) (S : NState) (cells : List Cell) (binds : List CppState.Binding)
    (slots : List Location) : Prop where
  slots : S.slots = slots
  memory : S.scalars.memory = F.P ++ cells
  bindings : S.scalars.bindings = binds
  base : S.scalars.baseMemory = F.B
  scope : S.scope = scope
  frameBindings : S.frame.bindings = [vbind F.V F.vsc]
  writable : S.frame.rootWritable = rw0

theorem PS.core {F : Fixed} {scope : Nat} {rw0 : List Bool} {S t : NState} {cells binds slots}
    (ps : PS F scope rw0 S cells binds slots) (core : Core S t) : PS F scope rw0 t cells binds slots := by
  obtain ⟨frame,sl,sc,me,bi,ba⟩ := core
  exact ⟨by rw [sl]; exact ps.slots,by rw [me]; exact ps.memory,by rw [bi]; exact ps.bindings,
    by rw [ba]; exact ps.base,by rw [sc]; exact ps.scope,by rw [frame]; exact ps.frameBindings,
    by rw [frame]; exact ps.writable⟩

theorem PS.live_eq {F : Fixed} {scope : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PS F scope rw0 S cells binds slots) : liveS S = F.P.length+cells.length-F.B+binds.length := by
  simp [liveS,ps.memory,ps.bindings,ps.base]

abbrev ePos : NExpr := .binary bl .gt (.variable u64 1) (.cast u64 (.literal i32 0))
abbrev eMax : NExpr := .binary bl .le (.size (.integer i32) (.local 0)) (.cast u64 (.literal i32 2147483647))
abbrev eN : NExpr := .cast i32 (.size (.integer i32) (.local 0))

def entrySlots : List Location := [.vector 0,.scalar 0]

theorem ePos_scalar : ePos.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem e1_step (F : Fixed) {rw0 : List Bool} {W : Nat} (S : NState) (hK : 0 < F.K) (hK2 : F.K < 2^64)
    (ps : PS F F.sc rw0 S [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots) (cb : Cb F W S)
    (cap : liveS S+8 ≤ F.SPB) :
    ∃ t, (NStmt.check ePos).run S = some ⟨t,none,false⟩ ∧
      PS F F.sc rw0 t [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots ∧ t.frame = S.frame ∧ Cb F (W+9) t := by
  have kv : u64.valid F.K = true := by simp [Ty.valid]; omega
  have env : envOf S 1 u64 = some F.K :=
    envOf_at S 1 0 ⟨F.P.length,true⟩ u64 F.K (by simp [ps.slots,entrySlots]) (by simp [ps.bindings])
      (by simp [ps.memory]) kv
  have zero : u64.valid 0 = true := by simp [Ty.valid]
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  have value : ePos.denote (envOf S) = some 1 := by
    simp [NExpr.denote,env,lit,Ty.convert_of_valid _ _ zero,binaryValue,hK,Ty.convert_of_valid bl 1 (by simp [Ty.valid])]
  obtain ⟨t,run,good⟩ := check_good ePos S 1 ePos_scalar value (by decide)
  refine ⟨t,run,ps.core good.1,good.1.1,?_⟩
  exact (cb.good good (by simp [NExpr.nodes]; omega)).mono (by simp [NExpr.nodes])
theorem sizeV_ev (F : Fixed) {L0 T0 : Nat} (S : NState) (N : Nat) (hs : S.vectorSlot 0 = some 0)
    (fb : S.frame.bindings = [vbind F.V F.vsc]) (vf : VF F L0 T0 S.frame) (small : F.vbuf.items.length < 2^64) :
    ∃ t, Ev (S.charge 0 N) (.size (.integer i32) (.local 0)) t (F.vbuf.items.length : Int) [] 3 3 := by
  obtain ⟨m,hm⟩ := vf.flag
  exact Ev.sizeRoot (S.charge 0 N) 0 0 F.V F.vsc i32 false m F.vbuf (by simpa [NState.vectorSlot] using hs)
    (by simp [fb,vbind,atom]) vf.valid vf.vtag vf.vfound vf.lengths hm (by simp) small

theorem e2_step (F : Fixed) {rw0 : List Bool} {L0 T0 W : Nat} (S : NState) (hn : F.vbuf.items.length < 2147483648)
    (ps : PS F F.sc rw0 S [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, (NStmt.check eMax).run S = some ⟨t,none,false⟩ ∧
      PS F F.sc rw0 t [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots ∧ t.frame = S.frame ∧ Cb F (W+20) t := by
  have hs : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,ps.slots,entrySlots]
  obtain ⟨t1,first⟩ := sizeV_ev F S ((NExpr.size (.integer i32) (.local 0)).nodes+(NExpr.cast u64 (.literal i32 2147483647)).nodes+1) hs ps.frameBindings vf (by omega)
  have lit : i32.valid 2147483647 = true := by simp [Ty.valid]
  have big : u64.valid 2147483647 = true := by simp [Ty.valid]
  have rightScalar : (NExpr.cast u64 (.literal i32 2147483647)).scalarOnly = true := by simp [NExpr.scalarOnly]
  have rightValue : (NExpr.cast u64 (.literal i32 2147483647)).denote (envOf t1) = some 2147483647 := by
    simp [NExpr.denote,lit,Ty.convert_of_valid _ _ big]
  obtain ⟨t2,second⟩ := Ev.scalar rightScalar rightValue (s := t1)
  have conv : bl.convert (binaryValue .le (F.vbuf.items.length : Int) 2147483647) = some 1 := by
    have : (F.vbuf.items.length : Int) ≤ 2147483647 := by omega
    simp only [binaryValue,this,if_true]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  have ev := Ev.binary first second conv
  obtain ⟨t,run,good⟩ := check_of_ev eMax S _ 1 _ _ (by simpa using ev) (by decide)
  refine ⟨t,run,ps.core good.1,good.1.1,?_⟩
  exact (cb.good good (by simp [NExpr.nodes,Container.nodes]; omega)).mono (by simp [NExpr.nodes,Container.nodes])

def slots3 : List Location := [.vector 0,.scalar 0,.scalar 1]

theorem e3_step (F : Fixed) {rw0 : List Bool} {L0 T0 W : Nat} (S : NState) (hvn : F.vbuf.items.length = F.n)
    (hn : F.n < 2147483648)
    (ps : PS F F.sc rw0 S [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, (NStmt.declare i32 false eN).run S = some ⟨t,none,false⟩ ∧
      PS F F.sc rw0 t [⟨u64,F.K⟩,⟨i32,F.n⟩] [⟨F.P.length,true⟩,⟨F.P.length+1,false⟩] slots3 ∧
      t.frame = S.frame ∧ Cb F (W+10) t := by
  have hs : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,ps.slots,entrySlots]
  obtain ⟨t1,first⟩ := sizeV_ev F S ((NExpr.size (.integer i32) (.local 0)).nodes+1) hs ps.frameBindings vf (by omega)
  have valid : i32.valid (F.n : Int) = true := i32_valid_nat F.n hn
  have ev := Ev.cast first (v' := (F.n : Int)) (by rw [hvn]; exact Ty.convert_of_valid _ _ valid)
  have good := Ev.good (by simpa using ev : Ev S eN _ (F.n : Int) [] _ _)
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_of_good eN i32 false S _ _ _ _ _ (Ev.eval ev) good
    (Nat.le_trans (by omega) (Nat.le_max_right _ _)) (Ty.convert_of_valid _ _ valid)
  have memLen : S.scalars.memory.length = F.P.length+1 := by simp [ps.memory]
  have bindLen : S.scalars.bindings.length = 1 := by simp [ps.bindings]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl,bindLen,ps.slots]; simp [entrySlots,slots3]
  · rw [me,ps.memory]; simp
  · rw [bi,memLen,ps.bindings]; rfl
  · rw [ba]; exact ps.base
  · rw [sc]; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by
      try simp [NExpr.nodes,Container.nodes] at pu ⊢
      omega
    have wu' : t.scalars.work ≤ S.scalars.work+10 := by
      try simp [NExpr.nodes,Container.nodes] at wu ⊢
      omega
    exact cb.step frame wu' pu' cap qu

theorem readV_ev (F : Fixed) {L0 T0 : Nat} (S u : NState) (core : Core S u) (hs : S.vectorSlot 0 = some 0)
    (fb : S.frame.bindings = [vbind F.V F.vsc]) (vf : VF F L0 T0 S.frame) (index : NExpr) (j : Nat)
    (idxScalar : index.scalarOnly = true) (idxValue : index.denote (envOf S) = some (j : Int)) (x : Int)
    (item : F.vbuf.items[j]? = some (Value.integer x)) :
    ∃ t, Ev u (.read i32 (.local 0) index) t x [] (index.nodes+3) (index.nodes+3) := by
  obtain ⟨m,hm⟩ := vf.flag
  have frame := core.1
  have slots := core.2.1
  exact Ev.readRoot u 0 0 F.V F.vsc index j i32 false m F.vbuf x idxScalar
    (by rw [envOf_core core]; exact idxValue)
    (by simpa [NState.vectorSlot,slots] using hs) (by rw [frame,fb]; simp [vbind,atom])
    (by rw [frame]; exact vf.valid) (by rw [frame]; exact vf.vtag) (by rw [frame]; exact vf.vfound)
    (by rw [frame]; exact vf.lengths) (by rw [frame]; exact hm) (by simp) item

theorem VF.of_same {F : Fixed} {L0 T0 : Nat} {fr fr' : Frame} (vf : VF F L0 T0 fr)
    (same : SameObjects fr.state fr'.state) (rw : fr'.rootWritable = fr.rootWritable)
    (work : fr'.state.storage.work = fr.state.storage.work) : VF F L0 T0 fr' := by
  obtain ⟨valid,vtag,vfound,lengths,flag,bnd,live,stw,rootId⟩ := vf
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [same.wellFormed]; exact valid
  · rw [same.1]; exact vtag
  · rw [same.lookup]; exact vfound
  · rw [rw,same.1]; exact lengths
  · rw [rw]; exact flag
  · intro owner c h
    rw [same.1] at h
    exact bnd owner c h
  · rw [same.liveSpace]; exact live
  · rw [work]; exact stw
  · rw [rootId,same.2.1]

theorem Cb.left {F : Fixed} {W W' : Nat} {outer inner : NState} (co : Cb F W outer) (ci : Cb F W' inner)
    (lengthTake : (inner.scalars.memory.take outer.scalars.memory.length).length = outer.scalars.memory.length)
    (liveOuter : liveS outer ≤ F.SPB)
    (hl : inner.frame.state.liveSpace-inner.frame.state.storage.baseSpace ≤ F.TPB) :
    Cb F (W'+1) (outer.left inner) := by
  have e : outer.scalars.memory.length-outer.scalars.baseMemory+outer.scalars.bindings.length+0 ≤ F.SPB := by
    unfold liveS at liveOuter; omega
  have hs : (outer.left inner).scalars.peak ≤ F.SPB := by
    rw [left_scalar_peak,lengthTake]; exact mid_scalar _ _ _ _ co.scalarPeak ci.scalarPeak e
  have ht : (noopRetired inner.frame).state.storage.peak ≤ F.TPB := by
    show max inner.frame.state.storage.peak
      (inner.frame.state.liveSpace-inner.frame.state.storage.baseSpace) ≤ F.TPB
    have := ci.storagePeak
    omega
  refine ⟨?_,hs,?_,?_⟩
  · rw [left_work]; have := ci.work; omega
  · rw [left_state]; exact ht
  · rw [left_peak]; exact mid_peak _ _ _ _ _ _ co.outerPeak ci.outerPeak hs ht

def slots4 : List Location := [.vector 0,.scalar 0,.scalar 1,.scalar 2]
def binds2 (F : Fixed) : List CppState.Binding := [⟨F.P.length,true⟩,⟨F.P.length+1,false⟩]
def binds3 (F : Fixed) : List CppState.Binding := binds2 F ++ [⟨F.P.length+2,true⟩]
def cells2 (F : Fixed) : List Cell := [⟨u64,F.K⟩,⟨i32,F.n⟩]
def cells3 (F : Fixed) (i : Nat) : List Cell := cells2 F ++ [⟨i32,i⟩]

abbrev iIdx : NExpr := .cast u64 (.variable i32 3)
abbrev cA : NExpr := .binary bl .le (.literal i32 0) (.read i32 (.local 0) iIdx)
abbrev cB : NExpr := .binary bl .lt (.read i32 (.local 0) iIdx) (.variable i32 2)
abbrev checksCmd : Command :=
  .scope (.sequence (.primitive (.check cA)) (.sequence (.primitive (.check cB)) (.primitive .skip)))
abbrev incAI : NExpr := .binary i32 .add (.variable i32 3) (.literal i32 1)
abbrev assertBody : Command :=
  .sequence checksCmd (.sequence (.primitive (.assign 3 i32 incAI)) (.primitive .skip))
abbrev assertCond : NExpr := .binary bl .lt (.variable i32 3) (.variable i32 2)
abbrev assertWhile : Command := .whileLoop assertCond assertBody
abbrev declAI : NStmt := .declare i32 true (.literal i32 0)
abbrev assertScope : Command := .scope (.sequence (.primitive declAI) (.sequence assertWhile (.primitive .skip)))

theorem declAI_step (F : Fixed) {sc : Nat} {rw0 : List Bool} {W : Nat} (S : NState)
    (ps : PS F sc rw0 S (cells2 F) (binds2 F) slots3) (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, declAI.run S = some ⟨t,none,false⟩ ∧ PS F sc rw0 t (cells3 F 0) (binds3 F) slots4 ∧
      t.frame = S.frame ∧ Cb F (W+2) t := by
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good (.literal i32 0) i32 true S 0 0
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,lit]) (Ty.convert_of_valid _ _ lit)
  have memLen : S.scalars.memory.length = F.P.length+2 := by simp [ps.memory,cells2]
  have bindLen : S.scalars.bindings.length = 2 := by simp [ps.bindings,binds2]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl,bindLen,ps.slots]; simp [slots3,slots4]
  · rw [me,ps.memory]; simp [cells3,cells2]
  · rw [bi,memLen,ps.bindings]; simp [binds3,binds2]
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · have wu' : t.scalars.work ≤ S.scalars.work+2 := by simp [NExpr.nodes] at wu; omega
    have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by simp [NExpr.nodes] at pu; omega
    exact cb.step frame wu' pu' cap qu

theorem incAI_scalar : incAI.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem envAI (F : Fixed) {sc : Nat} {rw0 : List Bool} {i : Nat} (S : NState) (hi : i < 2147483648) (hn : F.n < 2147483648)
    (ps : PS F sc rw0 S (cells3 F i) (binds3 F) slots4) :
    envOf S 3 i32 = some (i : Int) ∧ envOf S 2 i32 = some (F.n : Int) :=
  ⟨envOf_at S 3 2 ⟨F.P.length+2,true⟩ i32 i (by simp [ps.slots,slots4]) (by simp [ps.bindings,binds3,binds2])
      (by simp [ps.memory,cells3,cells2]) (i32_valid_nat i hi),
   envOf_at S 2 1 ⟨F.P.length+1,false⟩ i32 F.n (by simp [ps.slots,slots4]) (by simp [ps.bindings,binds3,binds2])
      (by simp [ps.memory,cells3,cells2]) (i32_valid_nat F.n hn)⟩

theorem assignAI_step (F : Fixed) {sc : Nat} {rw0 : List Bool} {W i : Nat} (S : NState) (hi : i+1 < 2147483648) (hn : F.n < 2147483648)
    (ps : PS F sc rw0 S (cells3 F i) (binds3 F) slots4) (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, (NStmt.assign 3 i32 incAI).run S = some ⟨t,none,false⟩ ∧
      PS F sc rw0 t (cells3 F (i+1)) (binds3 F) slots4 ∧ t.frame = S.frame ∧ Cb F (W+4) t := by
  have vi := i32_valid_nat i (by omega)
  have vi1 := i32_valid_nat (i+1) hi
  have e3 := (envAI F S (by omega) hn ps).1
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incAI.denote (envOf S) = some ((i : Int)+1) := by
    have vi1' : i32.valid ((i : Int)+1) = true := by simp [Ty.valid]; omega
    exact denote_inc (envOf S) 3 i32 i e3 lit (Ty.convert_of_valid _ _ vi1')
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_good incAI 3 2 i32 S _ ((i : Int)+1)
    ⟨F.P.length+2,true⟩ ⟨i32,i⟩ incAI_scalar value (Ty.convert_of_valid _ _ (by simp [Ty.valid]; omega))
    (by simp [ps.slots,slots4]) (by simp [ps.bindings,binds3,binds2]) (by simp [ps.memory,cells3,cells2]) rfl vi rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl]; exact ps.slots
  · rw [me,ps.memory]; simp [cells3,cells2,List.set_append_right]
  · rw [bi]; exact ps.bindings
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · have wu' : t.scalars.work ≤ S.scalars.work+4 := by simp [NExpr.nodes] at wu; omega
    have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by simp [NExpr.nodes] at pu; omega
    exact cb.step frame wu' pu' cap qu

theorem iIdx_scalar : iIdx.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem iIdx_value (F : Fixed) {sc : Nat} {rw0 : List Bool} {i : Nat} (S : NState) (hi : i < 2147483648)
    (hn : F.n < 2147483648) (ps : PS F sc rw0 S (cells3 F i) (binds3 F) slots4) :
    iIdx.denote (envOf S) = some (i : Int) := by
  have e3 := (envAI F S hi hn ps).1
  have valid : u64.valid (i : Int) = true := u64_valid_nat i (by omega)
  simp [NExpr.denote,e3,Ty.convert_of_valid _ _ valid]

theorem item_at (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer) (i : Nat)
    (hi : i < F.n) : ∃ x : Int, F.vbuf.items[i]? = some (Value.integer x) ∧ F.items[i]? = some x ∧
      0 ≤ x ∧ x < F.n := by
  have inside : i < F.items.length := by have := ok.nEq; omega
  refine ⟨F.items[i],?_,by simp [inside],?_⟩
  · rw [hv]; simp [List.getElem?_map,inside]
  · have := ok.itemsValid F.items[i] (List.getElem_mem inside)
    have := ok.nEq
    omega

theorem checkA_step (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {sc : Nat} {rw0 : List Bool} {L0 T0 W i : Nat} (S : NState) (hi : i < F.n)
    (ps : PS F sc rw0 S (cells3 F i) (binds3 F) slots4) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+30 ≤ F.SPB) :
    ∃ r, (NStmt.check cA).run S = some ⟨r,none,false⟩ ∧ PS F sc rw0 r (cells3 F i) (binds3 F) slots4 ∧
      r.frame = S.frame ∧ Cb F (W+30) r := by
  have hs : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,ps.slots,slots4]
  obtain ⟨x,item,_,x0,xn⟩ := item_at F ok hv i hi
  have nS := ok.nSmall
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  have litScalar : (NExpr.literal i32 0).scalarOnly = true := by simp [NExpr.scalarOnly]
  obtain ⟨t1,first⟩ := Ev.scalar litScalar (v := 0) (by simp [NExpr.denote,lit]) (s := S.charge 0 ((NExpr.literal i32 0).nodes+(NExpr.read i32 (.local 0) iIdx).nodes+1))
  have core1 : Core S t1 := (core_charge S _ _).trans (Ev.good first).1
  obtain ⟨t2,second⟩ := readV_ev F S t1 core1 hs ps.frameBindings vf iIdx i iIdx_scalar
    (iIdx_value F S (by omega) nS ps) x item
  have conv : bl.convert (binaryValue .le 0 x) = some 1 := by
    simp only [binaryValue,x0,ite_true]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  have ev := Ev.binary first second conv
  obtain ⟨r,run,good⟩ := check_of_ev cA S _ 1 _ _ (by simpa using ev) (by decide)
  refine ⟨r,run,ps.core good.1,good.1.1,?_⟩
  exact (cb.good good (by simp [NExpr.nodes,Container.nodes]; omega)).mono (by simp [NExpr.nodes,Container.nodes])

theorem checkB_step (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {sc : Nat} {rw0 : List Bool} {L0 T0 W i : Nat} (S : NState) (hi : i < F.n)
    (ps : PS F sc rw0 S (cells3 F i) (binds3 F) slots4) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+30 ≤ F.SPB) :
    ∃ r, (NStmt.check cB).run S = some ⟨r,none,false⟩ ∧ PS F sc rw0 r (cells3 F i) (binds3 F) slots4 ∧
      r.frame = S.frame ∧ Cb F (W+30) r := by
  have hs : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,ps.slots,slots4]
  obtain ⟨x,item,_,x0,xn⟩ := item_at F ok hv i hi
  have nS := ok.nSmall
  obtain ⟨t1,first⟩ := readV_ev F S (S.charge 0 ((NExpr.read i32 (.local 0) iIdx).nodes+(NExpr.variable i32 2).nodes+1))
    (core_charge S _ _) hs ps.frameBindings vf iIdx i iIdx_scalar (iIdx_value F S (by omega) nS ps) x item
  have core1 : Core S t1 := (core_charge S _ _).trans (Ev.good first).1
  have env2 := (envAI F S (by omega) nS ps).2
  have varScalar : (NExpr.variable i32 2).scalarOnly = true := by simp [NExpr.scalarOnly]
  obtain ⟨t2,second⟩ := Ev.scalar varScalar (v := (F.n : Int)) (by simp [NExpr.denote,envOf_core core1,env2]) (s := t1)
  have conv : bl.convert (binaryValue .lt x (F.n : Int)) = some 1 := by
    simp only [binaryValue,xn,ite_true]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  have ev := Ev.binary first second conv
  obtain ⟨r,run,good⟩ := check_of_ev cB S _ 1 _ _ (by simpa using ev) (by decide)
  refine ⟨r,run,ps.core good.1,good.1.1,?_⟩
  exact (cb.good good (by simp [NExpr.nodes,Container.nodes]; omega)).mono (by simp [NExpr.nodes,Container.nodes])

-- Leaving a scalar-only scope whose frame changed no object: the shape and facts return to the outer state.
theorem leave_back (F : Fixed) {sc : Nat} {rw0 : List Bool} {L0 T0 W W' : Nat} {cells : List Cell}
    {binds : List CppState.Binding} {slots : List Location} (S tB : NState) (hsc : F.sc ≤ sc)
    (ps : PS F sc rw0 S cells binds slots) (psB : PS F (sc+1) rw0 tB cells binds slots)
    (vfB : VF F L0 T0 tB.frame) (hL : L0 ≤ F.TPB) (co : Cb F W S) (ci : Cb F W' tB) (cap : liveS S ≤ F.SPB) :
    ∃ restored, S.leave tB none = some restored ∧ PS F sc rw0 restored cells binds slots ∧
      VF F L0 T0 restored.frame ∧ Cb F (W'+1) restored := by
  have take : tB.scalars.memory.take S.scalars.memory.length = S.scalars.memory := by
    rw [psB.memory,ps.memory]; exact List.take_length
  have fits : S.scalars.memory.length ≤ tB.scalars.memory.length := by rw [psB.memory,ps.memory]; exact Nat.le_refl _
  have leaveEq : S.leave tB none = some (S.left tB) :=
    leave_scalar S tB none (by simp) fits (by rw [take]) vfB.valid
      (by rw [ps.scope]; exact vfB.fresh hsc)
  have sameBind : tB.frame.bindings = S.frame.bindings := by rw [psB.frameBindings,ps.frameBindings]
  have lengthTake : (tB.scalars.memory.take S.scalars.memory.length).length = S.scalars.memory.length := by
    rw [take]
  refine ⟨S.left tB,leaveEq,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact ps.slots
  · rw [left_memory,take]; exact ps.memory
  · rw [left_bindings]; exact ps.bindings
  · rw [left_baseMemory]; exact ps.base
  · rw [left_scope]; exact ps.scope
  · rw [left_frameBindings,sameBind]; simpa using ps.frameBindings
  · rw [left_rootWritable]; exact psB.writable
  · refine vfB.of_same ?_ (by rw [left_rootWritable]) ?_
    · rw [left_state]; exact noopRetired_same _
    · rw [left_state]; rfl
  · refine co.left ci lengthTake cap ?_
    rw [vfB.live]; omega

theorem PS.enter {F : Fixed} {sc : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PS F sc rw0 S cells binds slots) : PS F (sc+1) rw0 {S with scope := S.scope+1} cells binds slots :=
  ⟨ps.slots,ps.memory,ps.bindings,ps.base,by simp [ps.scope],ps.frameBindings,ps.writable⟩

theorem Cb.enter {F : Fixed} {W : Nat} {S : NState} (cb : Cb F W S) : Cb F W {S with scope := S.scope+1} :=
  ⟨cb.work,cb.scalarPeak,cb.storagePeak,cb.outerPeak⟩

theorem checks_phase (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W i : Nat} (S : NState) (hi : i < F.n) (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB)
    (ps : PS F S.scope rw0 S (cells3 F i) (binds3 F) slots4) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+30 ≤ F.SPB) :
    RunsTo checksCmd S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (cells3 F i) (binds3 F) slots4 ∧ VF F L0 T0 step.state.frame ∧
      Cb F (W+61) step.state := by
  have ps1 := ps.enter
  have cb1 := cb.enter
  have capEq : liveS ({S with scope := S.scope+1} : NState) = liveS S := rfl
  obtain ⟨tA,runA,psA,frameA,cbA⟩ := checkA_step F ok hv _ hi ps1 (by simpa using vf) cb1 (by rw [capEq]; omega)
  have capA : liveS tA = liveS S := by
    have core : Core ({S with scope := S.scope+1} : NState) tA :=
      ⟨frameA,psA.slots.trans ps1.slots.symm,psA.scope.trans ps1.scope.symm,psA.memory.trans ps1.memory.symm,
        psA.bindings.trans ps1.bindings.symm,psA.base.trans ps1.base.symm⟩
    exact (liveS_core core).trans capEq
  have vfA : VF F L0 T0 tA.frame := vf.of_eq (frameA.trans rfl)
  obtain ⟨tB,runB,psB,frameB,cbB⟩ := checkB_step F ok hv tA hi psA vfA cbA (by rw [capA]; omega)
  have vfB : VF F L0 T0 tB.frame := vfA.of_eq frameB
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive runA
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  apply RunsTo.primitive runB
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_back F S tB hsc ps psB vfB hL cb (cbB.mono (show W+30+30 ≤ W+60 by omega)) (by omega)
  exact ⟨restored,leaveEq,rfl,rfl,psR,vfR,cbR.mono (by omega)⟩

theorem assertCond_scalar : assertCond.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem assert_loop (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W i0 : Nat} (S : NState) (hi0 : i0 ≤ F.n) (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB)
    (ps : PS F S.scope rw0 S (cells3 F i0) (binds3 F) slots4) (vf : VF F L0 T0 S.frame)
    (cb : Cb F (W+i0*100) S) (cap : liveS S+30 ≤ F.SPB) :
    RunsTo assertWhile S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (cells3 F F.n) (binds3 F) slots4 ∧ VF F L0 T0 step.state.frame ∧
      Cb F (W+F.n*100+8) step.state := by
  have nS := ok.nSmall
  have liveEq : ∀ t : NState, PS F S.scope rw0 t (cells3 F i0) (binds3 F) slots4 → liveS t = liveS S :=
    fun t pt => by rw [pt.live_eq,ps.live_eq]
  refine RunsTo.whileGhost (fun g t => ∃ i, g = F.n-i ∧ i ≤ F.n ∧ PS F S.scope rw0 t (cells3 F i) (binds3 F) slots4 ∧
      VF F L0 T0 t.frame ∧ Cb F (W+i*100) t) _ ?_ F.n (F.n-i0) S (by omega) ⟨i0,rfl,hi0,ps,vf,cb⟩
  intro g t ⟨i,hg,hle,pt,vft,cbt⟩
  have liveT : liveS t = F.P.length+(cells3 F i).length-F.B+(binds3 F).length := pt.live_eq
  have liveS0 : liveS S = F.P.length+(cells3 F i0).length-F.B+(binds3 F).length := ps.live_eq
  have lenCells : (cells3 F i).length = (cells3 F i0).length := by simp [cells3,cells2]
  have liveTS : liveS t = liveS S := by rw [liveT,liveS0,lenCells]
  have capT : liveS t+30 ≤ F.SPB := by omega
  obtain ⟨ei,en⟩ := envAI F t (by omega) nS pt
  have value : assertCond.denote (envOf t) = some (if (i : Int) < (F.n : Int) then 1 else 0) :=
    denote_lt (envOf t) 3 2 i32 i F.n ei en
  obtain ⟨u,hu,good⟩ := scalar_eval assertCond t _ assertCond_scalar value
  have self := release_self good.1.1
  have cbU : Cb F (W+i*100+4) u := (cbt.good good (by simp [NExpr.nodes]; omega)).mono (by simp [NExpr.nodes])
  have cbC : Cb F (W+i*100+8) (u.charge 1 0) :=
    (cbU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp [NExpr.nodes]; omega)).mono (by omega)
  have ptU : PS F S.scope rw0 (u.charge 1 0) (cells3 F i) (binds3 F) slots4 :=
    pt.core (good.1.trans (core_charge u 1 0))
  have vfU : VF F L0 T0 (u.charge 1 0).frame := vft.of_eq (by simpa using good.1.1)
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLt : ¬ i < F.n := by
      intro h
      have : ((i : Int) < (F.n : Int)) := by omega
      simp [this] at zero
    have eq : i = F.n := by omega
    subst eq
    rw [self]
    exact ⟨rfl,rfl,ptU,vfU,cbC⟩
  · intro nonzero
    have lt : i < F.n := by
      by_cases h : i < F.n
      · exact h
      · have : ¬ ((i : Int) < (F.n : Int)) := by omega
        simp [this] at nonzero
    rw [self]
    have scopeU : (u.charge 1 0).scope = S.scope := by rw [ptU.scope]
    have capU : liveS (u.charge 1 0)+30 ≤ F.SPB := by
      rw [ptU.live_eq]; rw [liveT] at capT; omega
    have checks := checks_phase F ok hv (W := W+i*100+8) (u.charge 1 0) lt (by rw [ptU.scope]; exact hsc) hL
      (by rw [ptU.scope] at *; exact ptU) vfU cbC capU
    apply RunsTo.seq
    refine checks.mono ?_
    intro mid ⟨nr,nb,psM,vfM,cbM⟩
    refine ⟨nr,nb,?_⟩
    have capM : liveS mid.state+12 ≤ F.SPB := by
      rw [psM.live_eq]; rw [liveT] at capT; omega
    obtain ⟨t2,runA,psA,frameA,cbA⟩ := assignAI_step F mid.state (by omega) nS psM cbM capM
    apply RunsTo.seqSkip
    apply RunsTo.primitive runA
    exact ⟨rfl,rfl,rfl,rfl,F.n-(i+1),by omega,i+1,rfl,by omega,by rw [← scopeU]; exact psA,vfM.of_eq frameA,cbA.mono (by omega)⟩

-- Leaving a scope that only declared scalar locals: the outer shape returns, the extra cells are dropped.
theorem leave_extra (F : Fixed) {sc : Nat} {rw0 : List Bool} {L0 T0 W W' : Nat} {cells extra : List Cell}
    {binds binds' : List CppState.Binding} {slots slots' : List Location} (S tB : NState) (hsc : F.sc ≤ sc)
    (ps : PS F sc rw0 S cells binds slots) (psB : PS F (sc+1) rw0 tB (cells ++ extra) binds' slots')
    (vfB : VF F L0 T0 tB.frame) (hL : L0 ≤ F.TPB) (co : Cb F W S) (ci : Cb F W' tB) (cap : liveS S ≤ F.SPB) :
    ∃ restored, S.leave tB none = some restored ∧ PS F sc rw0 restored cells binds slots ∧
      VF F L0 T0 restored.frame ∧ Cb F (W'+1) restored := by
  have take : tB.scalars.memory.take S.scalars.memory.length = S.scalars.memory := by
    rw [psB.memory,ps.memory,← List.append_assoc]
    exact List.take_left
  have fits : S.scalars.memory.length ≤ tB.scalars.memory.length := by
    rw [psB.memory,ps.memory]; simp
  have leaveEq : S.leave tB none = some (S.left tB) :=
    leave_scalar S tB none (by simp) fits (by rw [take]) vfB.valid
      (by rw [ps.scope]; exact vfB.fresh hsc)
  have sameBind : tB.frame.bindings = S.frame.bindings := by rw [psB.frameBindings,ps.frameBindings]
  have lengthTake : (tB.scalars.memory.take S.scalars.memory.length).length = S.scalars.memory.length := by
    rw [take]
  refine ⟨S.left tB,leaveEq,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact ps.slots
  · rw [left_memory,take]; exact ps.memory
  · rw [left_bindings]; exact ps.bindings
  · rw [left_baseMemory]; exact ps.base
  · rw [left_scope]; exact ps.scope
  · rw [left_frameBindings,sameBind]; simpa using ps.frameBindings
  · rw [left_rootWritable]; exact psB.writable
  · refine vfB.of_same ?_ (by rw [left_rootWritable]) ?_
    · rw [left_state]; exact noopRetired_same _
    · rw [left_state]; rfl
  · refine co.left ci lengthTake cap ?_
    rw [vfB.live]; omega

theorem PS.self {F : Fixed} {sc : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PS F sc rw0 S cells binds slots) : PS F S.scope rw0 S cells binds slots :=
  ⟨ps.slots,ps.memory,ps.bindings,ps.base,rfl,ps.frameBindings,ps.writable⟩

theorem assert_scope (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W : Nat} (S : NState) (hL : L0 ≤ F.TPB) (hsc : S.scope = F.sc)
    (ps : PS F F.sc rw0 S (cells2 F) (binds2 F) slots3) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+40 ≤ F.SPB) :
    RunsTo assertScope S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F F.sc rw0 step.state (cells2 F) (binds2 F) slots3 ∧ VF F L0 T0 step.state.frame ∧
      Cb F (W+F.n*100+20) step.state := by
  have ps1 := ps.enter
  have cb1 := cb.enter
  have capEq : liveS ({S with scope := S.scope+1} : NState) = liveS S := rfl
  obtain ⟨tD,runD,psD,frameD,cbD⟩ := declAI_step F _ ps1 cb1 (by rw [capEq]; omega)
  have vfD : VF F L0 T0 tD.frame := vf.of_eq frameD
  have scopeD : tD.scope = F.sc+1 := psD.scope
  have liveD : liveS tD = liveS S + 2 := by
    have hB := ok.base
    have a : liveS S = F.P.length+2-F.B+2 := by rw [ps.live_eq]; simp [cells2,binds2]
    have b : liveS tD = F.P.length+3-F.B+3 := by rw [psD.live_eq]; simp [cells3,cells2,binds3,binds2]
    omega
  have loop := assert_loop F ok hv (W := W+2) (i0 := 0) tD (by omega) (by omega) hL
    psD.self vfD (by simpa using cbD) (by omega)
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive runD
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  refine loop.mono ?_
  intro step ⟨nr,nb,psL,vfL,cbL⟩
  rw [scopeD] at psL
  obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_extra F S step.state (by omega) ps psL vfL hL cb
    cbL (by omega)
  exact ⟨nr,nb,rfl,rfl,restored,leaveEq,rfl,rfl,psR,vfR,cbR.mono (by omega)⟩

end Proofs.DoublingPrologue
