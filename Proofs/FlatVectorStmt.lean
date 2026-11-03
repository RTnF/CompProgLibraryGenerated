import Proofs.CppNestedScope

namespace Proofs.FlatVectorStmt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedFacts

def appRes (buf : Buffer Value) (x : Int) : CppVector.Result Value Unit :=
  ⟨{buf with items := buf.items ++ [Value.integer x]},(),2,buf.capacity+2⟩

def withFrame (t : NState) (f : Frame) : NState := {t with frame := f}
@[simp] theorem withFrame_slots (t : NState) (f : Frame) : (withFrame t f).slots = t.slots := rfl
@[simp] theorem withFrame_scope (t : NState) (f : Frame) : (withFrame t f).scope = t.scope := rfl
@[simp] theorem withFrame_scalars (t : NState) (f : Frame) : (withFrame t f).scalars = t.scalars := rfl
@[simp] theorem withFrame_frame (t : NState) (f : Frame) : (withFrame t f).frame = f := rfl
@[simp] theorem withFrame_peak (t : NState) (f : Frame) : (withFrame t f).peak = t.peak := rfl

-- The binding of a flat local vector root.
def flatBinding (R : Nat) (ty : Ty) (sc : Nat) : Binding := ⟨R,.integer ty,true,.root sc⟩

def flatDeclared (s : NState) (frame : Frame) (binding : Nat) : NState := {s with frame := frame,slots := s.slots ++ [.vector binding]}

-- `std::vector<ty> name;` as a writable local.
theorem declare_vec_stmt (s : NState) (ty : Ty) (supported : CppVectorBindings.supported ty)
    (valid : s.frame.state.wellFormed = true)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length) :
    ∃ t next, s.frame.state.declareVector ty s.scope = some next ∧
      (NStmt.declareVector ty true).run s = some ⟨t,none,false⟩ ∧
      t.frame = ⟨next,s.frame.rootWritable ++ [true],
        s.frame.bindings ++ [flatBinding s.frame.state.storage.objects.length ty s.scope]⟩ ∧
      t.slots = s.slots ++ [.vector s.frame.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ∧ t.scalars.bindings = s.scalars.bindings ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧ t.scalars.work = s.scalars.work+1 ∧
      t.scalars.peak = max s.scalars.peak (liveS s) ∧
      t.peak = max s.peak (t.scalars.peak+next.storage.peak) := by
  have declared : s.frame.state.declareVector ty s.scope =
      some ⟨s.frame.state.forest.declareRoot ty s.scope,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ [some (flatBuffer ty s.frame.state.storage.objects.length)],
          work := s.frame.state.storage.work+1,
          peak := max s.frame.state.storage.peak
            (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)}⟩ := by
    simp [CppNestedVectorStore.State.declareVector,valid,supported]
  generalize hnext : (⟨s.frame.state.forest.declareRoot ty s.scope,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ [some (flatBuffer ty s.frame.state.storage.objects.length)],
          work := s.frame.state.storage.work+1,
          peak := max s.frame.state.storage.peak
            (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)}⟩ : CppNestedVectorStore.State) = next at declared
  have nextValid := declareVector_wellFormed s.frame.state ty s.scope next declared
  obtain ⟨lengthsEq,_,_⟩ := wellFormed_parts s.frame.state valid
  have forestEq := declareVector_forest s.frame.state ty s.scope next declared
  have tagLookup : next.forest.lookup s.frame.state.storage.objects.length = some (flatTag ty s.scope) := by
    rw [forestEq,← lengthsEq]; exact declareRoot_new _ ty s.scope
  have found := declareVector_storage_new s.frame.state ty s.scope next declared
  have newLength : next.forest.objects.length = s.frame.state.forest.objects.length+1 := by
    rw [forestEq]; exact declareRoot_length _ ty s.scope
  have gobject : (⟨next,s.frame.rootWritable ++ [true],s.frame.bindings⟩ : Frame).object
      s.frame.state.storage.objects.length (.integer ty) = some (flatBuffer ty s.frame.state.storage.objects.length,
        flatTag ty s.scope) :=
    object_runs _ _ _ _ _ nextValid found tagLookup rfl
  have glengths : (s.frame.rootWritable ++ [true]).length = next.forest.objects.length := by
    simp [newLength,lengths]
  have gflag : (s.frame.rootWritable ++ [true])[s.frame.state.storage.objects.length]? = some true := by
    have : s.frame.rootWritable.length = s.frame.state.storage.objects.length := by omega
    simp [List.getElem?_append_right,this]
  have gmax : (⟨next,s.frame.rootWritable ++ [true],s.frame.bindings⟩ : Frame).maximum
      s.frame.state.storage.objects.length = some true :=
    maximum_runs _ _ s.frame.state.storage.objects.length true glengths
      (CppVectorOwnership.root_runs _ _ _ tagLookup rfl) gflag
  have bound : (⟨next,s.frame.rootWritable ++ [true],s.frame.bindings⟩ : Frame).bindRoot
      s.frame.state.storage.objects.length (.integer ty) s.scope true =
        some (⟨next,s.frame.rootWritable ++ [true],s.frame.bindings ++
          [flatBinding s.frame.state.storage.objects.length ty s.scope]⟩,s.frame.bindings.length) := by
    simp only [Frame.bindRoot,gobject,gmax,Bind.bind,Option.bind]
    simp [flatTag,Frame.addBinding,flatBinding]
  refine ⟨(flatDeclared s ⟨next,s.frame.rootWritable ++ [true],s.frame.bindings ++
      [flatBinding s.frame.state.storage.objects.length ty s.scope]⟩ s.frame.bindings.length).charge 1 0,
    next,declared,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,declared,bound,flatDeclared]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [charge_scalar_peak,liveS,flatDeclared]
  · simp [charge_peak,charge_scalar_peak,liveS,flatDeclared]

theorem Frame.eq_of_parts (f : Frame) {b : List Binding} (hf : f.bindings = b) :
    ({state := f.state, rootWritable := f.rootWritable, bindings := b} : Frame) = f := by
  cases f; simp_all

-- `local.reserve(n)` on a flat local root.
theorem reserve_flat_stmt (s : NState) (slot rb : Nat) (e : NExpr) (n R sc : Nat) (ty : Ty) (buf : Buffer Value)
    (eScalar : e.scalarOnly = true) (eValue : e.denote (envOf s) = some (n : Int))
    (hslot : s.vectorSlot slot = some rb) (binding : s.frame.bindings[rb]? = some (flatBinding R ty sc))
    (valid : s.frame.state.wellFormed = true) (vtag : s.frame.state.forest.lookup R = some (flatTag ty sc))
    (vfound : s.frame.state.storage.lookup R = some buf)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (limit : n ≤ buf.limit) :
    ∃ t result, (NStmt.reserve (.local slot) ty e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated R buf result ∧
      ((buf.capacity < n ∧ result = ⟨{buf with capacity := n,epoch := buf.epoch+1},(),
          buf.items.length+1,buf.capacity+n+2⟩) ∨
       (n ≤ buf.capacity ∧ result = ⟨buf,(),1,buf.capacity+1⟩)) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+e.nodes+4 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes+4) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  have container : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+e.nodes+2)) =
      some (((s.charge 0 ((Container.local slot).nodes+e.nodes+2)).charge 1 1),rb) :=
    eval_local _ slot rb (by simpa [NState.vectorSlot] using hslot)
  have env1 : envOf ((s.charge 0 ((Container.local slot).nodes+e.nodes+2)).charge 1 1) = envOf s :=
    (envOf_core (core_charge _ _ _)).trans (envOf_core (core_charge _ _ _))
  obtain ⟨t2,hexp,good2⟩ := scalar_eval e _ n eScalar (by rw [env1]; exact eValue)
  have frame2 : t2.frame = s.frame := good2.1.1
  have resolved2 : t2.frame.resolve rb (.integer ty) = some (flatBinding R ty sc,buf) := by
    rw [frame2]; exact resolved
  have object2 : t2.frame.object R (.integer ty) = some (buf,⟨.integer ty,none,some sc,[]⟩) := by
    rw [frame2]; exact object
  have gAll := (GoodF.charge s 0 ((Container.local slot).nodes+e.nodes+2)).trans
    ((GoodF.charge _ 1 1).trans good2.toF)
  have finalState : ∀ (f : Frame),
      t2.frame.reserve rb (.integer ty) n = some f → f.bindings = s.frame.bindings →
      ∃ t, (NStmt.reserve (.local slot) ty e).run s = some ⟨t,none,false⟩ ∧
        t.frame = f ∧ t.scalars.work = t2.scalars.work+1 ∧
        t.scalars.peak = max t2.scalars.peak (liveS t2+1) ∧ t.slots = t2.slots ∧ t.scope = t2.scope ∧
        t.scalars.memory = t2.scalars.memory ∧ t.scalars.bindings = t2.scalars.bindings ∧
        t.scalars.baseMemory = t2.scalars.baseMemory ∧
        t.peak = max t2.peak (t.scalars.peak+t.frame.state.storage.peak) := by
    intro f reserved hf
    refine ⟨(({t2 with frame := f} : NState).release s).charge 1 1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [NStmt.run,container,hexp,reserved]
    · simp [NState.release]; exact Frame.eq_of_parts f (by rw [hf]; exact List.take_length.symm)
    · simp [charge_work]
    · simp [charge_scalar_peak,liveS]
    · simp
    · simp
    · simp
    · simp
    · simp
    · have := charge_release_peak ({t2 with frame := f} : NState) s 1 1
      simpa using this
  have stateEq : t2.frame.state = s.frame.state := by rw [frame2]
  have rwEq : t2.frame.rootWritable = s.frame.rootWritable := by rw [frame2]
  have frameOf : ∀ result : Result Value Unit,
      t2.frame.updated R buf result = s.frame.updated R buf result := by
    intro result; rw [frame2]
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t2 = liveS s := liveS_of_memory m b k'
  by_cases grow : buf.capacity < n
  · have reserved := reserve_grow_ok t2.frame rb ty n (flatBinding R ty sc) buf
      ⟨.integer ty,none,some sc,[]⟩ resolved2 rfl object2 limit grow
    obtain ⟨t,run,tf,tw,tp,ts,tc,tm,tb,tbase,tpk⟩ := finalState _ reserved
      (by simp [Frame.updated,frame2])
    refine ⟨t,⟨{buf with capacity := n,epoch := buf.epoch+1},(),buf.items.length+1,buf.capacity+n+2⟩,run,?_,
      Or.inl ⟨grow,rfl⟩,ts.trans sl,tc.trans sc',tm.trans m,tb.trans b,tbase.trans k',?_,?_,?_,?_,?_,?_⟩
    · rw [tf]; exact frameOf _
    · omega
    · simp [Container.nodes] at gu; omega
    · omega
    · rw [live] at tp
      simp [Container.nodes] at gpu
      omega
    · omega
    · have hst : s.frame.state.storage.peak ≤ t.frame.state.storage.peak := by
        rw [tf]; simp [Frame.updated,stateEq,appRes] <;> omega
      have st2 : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [stateEq]
      omega
  · have fits : n ≤ buf.capacity := by omega
    have reserved := reserve_keep_ok t2.frame rb ty n (flatBinding R ty sc) buf
      ⟨.integer ty,none,some sc,[]⟩ resolved2 rfl object2 fits
    obtain ⟨t,run,tf,tw,tp,ts,tc,tm,tb,tbase,tpk⟩ := finalState _ reserved
      (by simp [Frame.updated,frame2])
    refine ⟨t,⟨buf,(),1,buf.capacity+1⟩,run,?_,Or.inr ⟨fits,rfl⟩,
      ts.trans sl,tc.trans sc',tm.trans m,tb.trans b,tbase.trans k',?_,?_,?_,?_,?_,?_⟩
    · rw [tf]; exact frameOf _
    · omega
    · simp [Container.nodes] at gu; omega
    · omega
    · rw [live] at tp
      simp [Container.nodes] at gpu
      omega
    · omega
    · have hst : s.frame.state.storage.peak ≤ t.frame.state.storage.peak := by
        rw [tf]; simp [Frame.updated,stateEq,appRes] <;> omega
      have st2 : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [stateEq]
      omega

-- `local.emplace_back(x)` on a flat local root with spare capacity.
theorem append_flat_stmt (s : NState) (slot rb : Nat) (e : NExpr) (x : Int) (R sc : Nat) (ty : Ty) (buf : Buffer Value)
    (eScalar : e.scalarOnly = true) (eValue : e.denote (envOf s) = some x)
    (hslot : s.vectorSlot slot = some rb) (binding : s.frame.bindings[rb]? = some (flatBinding R ty sc))
    (valid : s.frame.state.wellFormed = true) (vtag : s.frame.state.forest.lookup R = some (flatTag ty sc))
    (vfound : s.frame.state.storage.lookup R = some buf)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (room : buf.items.length < buf.capacity)
    (accepted : ty.valid x = true) :
    ∃ t, (NStmt.append (.local slot) ty e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated R buf (appRes buf x) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+e.nodes+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes+4) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  have container : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+e.nodes+2)) =
      some (((s.charge 0 ((Container.local slot).nodes+e.nodes+2)).charge 1 1),rb) :=
    eval_local _ slot rb (by simpa [NState.vectorSlot] using hslot)
  have env1 : envOf ((s.charge 0 ((Container.local slot).nodes+e.nodes+2)).charge 1 1) = envOf s :=
    (envOf_core (core_charge _ _ _)).trans (envOf_core (core_charge _ _ _))
  obtain ⟨t2,hexp,good2⟩ := scalar_eval e _ x eScalar (by rw [env1]; exact eValue)
  have frame2 : t2.frame = s.frame := good2.1.1
  have resolved2 : t2.frame.resolve rb (.integer ty) = some (flatBinding R ty sc,buf) := by
    rw [frame2]; exact resolved
  have object2 : t2.frame.object R (.integer ty) = some (buf,⟨.integer ty,none,some sc,[]⟩) := by
    rw [frame2]; exact object
  have gAll := (GoodF.charge s 0 ((Container.local slot).nodes+e.nodes+2)).trans
    ((GoodF.charge _ 1 1).trans good2.toF)
  have appended := append_ok t2.frame rb ty x (flatBinding R ty sc) buf ⟨.integer ty,none,some sc,[]⟩
    resolved2 rfl object2 accepted room
  have appended' : t2.frame.append rb ty x = some (s.frame.updated R buf
      (appRes buf x)) := by
    rw [appended]
    show some (t2.frame.updated R buf (appRes buf x)) = _
    rw [frame2]
  have stateEq : t2.frame.state = s.frame.state := by rw [frame2]
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t2 = liveS s := liveS_of_memory m b k'
  refine ⟨((withFrame t2 (s.frame.updated R buf (appRes buf x))).release s).charge 1 1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,container,hexp,appended',withFrame]
  · simp [NState.release,Frame.updated,appRes,withFrame,List.take_length]
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp [charge_work]; omega
  · simp [charge_work]; simp [Container.nodes] at gu; omega
  · simp [charge_scalar_peak,liveS]; omega
  · simp [charge_scalar_peak,m,b,k']
    simp [Container.nodes] at gpu
    unfold liveS at gpu live ⊢
    omega
  · exact (peak_after t2 (withFrame t2 (s.frame.updated R buf (appRes buf x))) s 1 1
      rfl rfl (by simp [Frame.updated,stateEq,appRes] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after t2 (withFrame t2 (s.frame.updated R buf (appRes buf x))) s 1 1
      rfl rfl (by simp [Frame.updated,stateEq,appRes] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).2

end Proofs.FlatVectorStmt
