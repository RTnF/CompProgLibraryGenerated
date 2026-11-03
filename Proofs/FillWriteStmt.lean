import Proofs.FlatVectorStmt
import Proofs.DoublingPrologue

namespace Proofs.FillWriteStmt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedFacts Proofs.FlatVectorStmt Proofs.DoublingPrologue

-- `std::vector<ty> name(n, x);` as a writable local.
theorem fill_vec_stmt (s : NState) (ty : Ty) (cE vE : NExpr) (n : Nat) (x : Int)
    (cScalar : cE.scalarOnly = true) (vScalar : vE.scalarOnly = true)
    (cValue : cE.denote (envOf s) = some (n : Int)) (vValue : vE.denote (envOf s) = some x)
    (supported : CppVectorBindings.supported ty) (limit : n ≤ CppVectorBindings.sizeLimit ty)
    (xv : ty.valid x = true) (valid : s.frame.state.wellFormed = true)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length) :
    ∃ t next, s.frame.state.fillVector ty s.scope n x = some next ∧
      (NStmt.fillVector ty true cE vE).run s = some ⟨t,none,false⟩ ∧
      t.frame = ⟨next,s.frame.rootWritable ++ [true],
        s.frame.bindings ++ [flatBinding s.frame.state.storage.objects.length ty s.scope]⟩ ∧
      t.slots = s.slots ++ [.vector s.frame.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ∧ t.scalars.bindings = s.scalars.bindings ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+cE.nodes+vE.nodes+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+cE.nodes+vE.nodes+3) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+next.storage.peak) := by
  obtain ⟨t1,ran1,good1⟩ := scalar_eval cE s (n : Int) cScalar cValue
  obtain ⟨t2,ran2,good2⟩ := scalar_eval vE t1 x vScalar (by rw [envOf_core good1.1]; exact vValue)
  have good := good1.trans good2
  have frame2 : t2.frame = s.frame := good.1.1.symm ▸ rfl
  have self : t2.release s = t2 := release_self frame2
  have declared : s.frame.state.fillVector ty s.scope n x = some
      ⟨s.frame.state.forest.declareRoot ty s.scope,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ [some ⟨s.frame.state.storage.objects.length,
            List.replicate n (Value.integer x),n,CppVectorBindings.sizeLimit ty,0⟩],
          work := s.frame.state.storage.work+(n+1),
          peak := max s.frame.state.storage.peak (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace)}⟩ := by
    simp [CppNestedVectorStore.State.fillVector,valid,supported,limit,xv]
  generalize hnext : (⟨s.frame.state.forest.declareRoot ty s.scope,
        {s.frame.state.storage with
          objects := s.frame.state.storage.objects ++ [some ⟨s.frame.state.storage.objects.length,
            List.replicate n (Value.integer x),n,CppVectorBindings.sizeLimit ty,0⟩],
          work := s.frame.state.storage.work+(n+1),
          peak := max s.frame.state.storage.peak (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace)}⟩ : CppNestedVectorStore.State) = next at declared
  have nextValid := fillVector_wellFormed s.frame.state ty s.scope n x next declared
  obtain ⟨lengthsEq,_,_⟩ := wellFormed_parts s.frame.state valid
  have forestEq := fillVector_forest s.frame.state ty s.scope n x next declared
  have tagLookup : next.forest.lookup s.frame.state.storage.objects.length = some (flatTag ty s.scope) := by
    rw [forestEq,← lengthsEq]; exact declareRoot_new _ ty s.scope
  have found := fillVector_storage_new s.frame.state ty s.scope n x next declared
  have newLength : next.forest.objects.length = s.frame.state.forest.objects.length+1 := by
    rw [forestEq]; exact declareRoot_length _ ty s.scope
  have gobject : (⟨next,s.frame.rootWritable ++ [true],s.frame.bindings⟩ : Frame).object
      s.frame.state.storage.objects.length (.integer ty) = some (_,flatTag ty s.scope) :=
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
  have scope2 : t2.scope = s.scope := good.1.2.2.1
  have slots2 : t2.slots = s.slots := good.1.2.1
  have nonneg : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
  have run : (NStmt.fillVector ty true cE vE).run s = some ⟨(flatDeclared t2 ⟨next,s.frame.rootWritable ++ [true],
      s.frame.bindings ++ [flatBinding s.frame.state.storage.objects.length ty s.scope]⟩
      s.frame.bindings.length).charge 3 0,none,false⟩ := by
    simp only [NStmt.run,ran1,ran2,Bind.bind,Option.bind,if_pos nonneg,self,frame2,scope2,Int.toNat_natCast,declared,bound]
    simp [flatDeclared,scope2]
  refine ⟨_,next,declared,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · simp [flatDeclared,slots2]
  · simp [flatDeclared,scope2]
  · simpa [flatDeclared] using good.1.2.2.2.1
  · simpa [flatDeclared] using good.1.2.2.2.2.1
  · simpa [flatDeclared] using good.1.2.2.2.2.2
  · simp [charge_work,flatDeclared]; have := good.2.1; omega
  · simp [charge_work,flatDeclared]; have := good.2.2.1; omega
  · obtain ⟨core,l,u,st,pl,pu,ql,qu⟩ := good
    simp [charge_scalar_peak,flatDeclared]; omega
  · obtain ⟨core,l,u,st,pl,pu,ql,qu⟩ := good
    have lv := liveS_core core
    simp [charge_scalar_peak,flatDeclared]
    unfold liveS at lv pu ⊢
    omega
  · obtain ⟨core,l,u,st,pl,pu,ql,qu⟩ := good
    simp [charge_peak,flatDeclared]; omega
  · obtain ⟨core,l,u,st,pl,pu,ql,qu⟩ := good
    have nextPeak : s.frame.state.storage.peak ≤ next.storage.peak := by
      rw [← hnext]
      exact Nat.le_max_left _ _
    have st2 : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [frame2]
    simp [charge_peak,charge_scalar_peak,flatDeclared]
    omega


-- `local[pos] = x;` on a writable root: the reference exists and the write replaces one item.
theorem write_ok (f : Frame) (slot : Nat) (ty : Ty) (pos : Nat) (x : Int) (binding : Binding)
    (buffer : Buffer Value) (tag : Tag) (maximum : Bool)
    (found : f.bindings[slot]? = some binding) (bindingElement : binding.element = .integer ty)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (max : f.maximum binding.owner = some maximum) (writable : binding.writable = true) (cap : maximum = true)
    (accepted : ty.valid x = true) (inside : pos < buffer.items.length) :
    ∃ reference, f.elementRef slot ty pos = some reference ∧
      f.write reference x = some (f.updated binding.owner buffer
        ⟨{buffer with items := buffer.items.set pos (Value.integer x)},(),1,buffer.capacity+2⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,foundBuffer,_,_⟩ := object_buffer f binding.owner _ buffer tag object
  have captured : CppVector.elementRef buffer (accepts (.integer ty)) pos =
      some ⟨buffer.owner,buffer.epoch,pos⟩ := by
    have := CppVector.elementRef_runs buffer (accepts (.integer ty)) pos bufferValid (by omega)
      (by simpa using inside)
    simpa using this
  have reference : f.elementRef slot ty pos =
      some ⟨slot,ty,binding.writable,⟨buffer.owner,buffer.epoch,pos⟩⟩ := by
    simp [Frame.elementRef,resolved,captured]
  refine ⟨_,reference,?_⟩
  have grant := grant_runs f ⟨slot,ty,binding.writable,⟨buffer.owner,buffer.epoch,pos⟩⟩ binding found
    (by simp [owns]) (by simpa using bindingElement) (fun h => h) maximum max (fun _ => cap)
  have written : CppVector.writeRef buffer (accepts (.integer ty)) true ⟨buffer.owner,buffer.epoch,pos⟩ (Value.integer x) =
      some ⟨{buffer with items := buffer.items.set pos (Value.integer x)},(),1,buffer.capacity+2⟩ :=
    CppVector.writeRef_runs buffer _ pos (Value.integer x) bufferValid inside (by simpa [accepts] using accepted)
  have object' : f.object buffer.owner (.integer ty) = some (buffer,tag) := by rw [owns]; exact object
  have wr := write_runs f ⟨slot,ty,binding.writable,⟨buffer.owner,buffer.epoch,pos⟩⟩ x binding buffer tag _
    grant (by simpa using writable) writable object' (by simpa using written)
  rw [wr]
  have newValid := CppVector.writeRef_preserves_valid buffer (accepts (.integer ty)) pos (Value.integer x) bufferValid
    (by simpa [accepts] using accepted)
  have owner' : buffer.owner = binding.owner := owns
  have := commit_runs f binding.owner (.integer ty) buffer tag
    ⟨{buffer with items := buffer.items.set pos (Value.integer x)},(),1,buffer.capacity+2⟩ valid object tagFound
    foundBuffer (by simpa using owns) (by simp [payloadOK,element,newValid]) (by simp) (by simp)
  simpa [owner'] using this


-- `local[index] = value;` on a flat local root, the index being any evaluable expression.
theorem write_flat_stmt (s : NState) (slot rb : Nat) (iE vE : NExpr) (pos : Nat) (x : Int) (R sc : Nat) (ty : Ty)
    (buf : Buffer Value) (wi pi : Nat)
    (vScalar : vE.scalarOnly = true) (vValue : vE.denote (envOf s) = some x)
    (index : ∀ u : NState, Core s u → ∃ t, Ev u iE t (pos : Int) [] wi pi)
    (hslot : s.vectorSlot slot = some rb) (binding : s.frame.bindings[rb]? = some (flatBinding R ty sc))
    (valid : s.frame.state.wellFormed = true) (vtag : s.frame.state.forest.lookup R = some (flatTag ty sc))
    (vfound : s.frame.state.storage.lookup R = some buf)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (accepted : ty.valid x = true) (inside : pos < buf.items.length) :
    ∃ t, (NStmt.write (.local slot) ty iE vE).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated R buf ⟨{buf with items := buf.items.set pos (Value.integer x)},(),1,buf.capacity+2⟩ ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+vE.nodes+wi+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+iE.nodes+vE.nodes+pi+5) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  obtain ⟨t1,hexp,good1⟩ := scalar_eval vE (s.charge 0 ((Container.local slot).nodes+iE.nodes+vE.nodes+3)) x vScalar
    (by rw [envOf_core (core_charge _ _ _)]; exact vValue)
  have container : (Container.local slot).eval t1 = some (t1.charge 1 1,rb) :=
    eval_local _ slot rb (by simpa [NState.vectorSlot,good1.1.2.1,core_charge] using hslot)
  have coreS : Core s (t1.charge 1 1) := (core_charge s 0 _).trans (good1.1.trans (core_charge t1 1 1))
  obtain ⟨t3,evI⟩ := index (t1.charge 1 1) coreS
  have goodI := Ev.good evI
  have frame3 : t3.frame = s.frame := goodI.1.1.trans coreS.1
  have resolved3 : t3.frame.resolve rb (.integer ty) = some (flatBinding R ty sc,buf) := by
    rw [frame3]; simpa [flatBinding] using resolved
  have object3 : t3.frame.object R (.integer ty) = some (buf,⟨.integer ty,none,some sc,[]⟩) := by
    rw [frame3]; exact object
  have max3 : t3.frame.maximum R = some true := by rw [frame3]; exact vmax
  have found3 : t3.frame.bindings[rb]? = some (flatBinding R ty sc) := by rw [frame3]; exact binding
  obtain ⟨ref,hrefs,hwrite⟩ := write_ok t3.frame rb ty pos x (flatBinding R ty sc) buf ⟨.integer ty,none,some sc,[]⟩ true
    found3 rfl resolved3 object3 max3 rfl rfl accepted inside
  have hwrite' : t3.frame.write ref x = some (s.frame.updated R buf
      ⟨{buf with items := buf.items.set pos (Value.integer x)},(),1,buf.capacity+2⟩) := by
    rw [hwrite]
    show some (t3.frame.updated R buf _) = _
    rw [frame3]
  have gAll := (GoodF.charge s 0 ((Container.local slot).nodes+iE.nodes+vE.nodes+3)).trans
    (good1.toF.trans ((GoodF.charge t1 1 1).trans evI.2.1))
  have stateEq : t3.frame.state = s.frame.state := by rw [frame3]
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t3 = liveS s := liveS_of_memory m b k'
  refine ⟨((withFrame t3 (s.frame.updated R buf ⟨{buf with items := buf.items.set pos (Value.integer x)},(),1,
    buf.capacity+2⟩)).release s).charge 1 0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,hexp,container,evI.1,hrefs,hwrite',withFrame]
  · simp [NState.release,Frame.updated,withFrame,List.take_length]
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
  · exact (peak_after t3 (withFrame t3 (s.frame.updated R buf ⟨{buf with items := buf.items.set pos (Value.integer x)},(),1,
      buf.capacity+2⟩)) s 1 0 rfl rfl (by simp [Frame.updated,stateEq] <;> omega) gql
      (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after t3 (withFrame t3 (s.frame.updated R buf ⟨{buf with items := buf.items.set pos (Value.integer x)},(),1,
      buf.capacity+2⟩)) s 1 0 rfl rfl (by simp [Frame.updated,stateEq] <;> omega) gql
      (by rw [stateEq] at gqu ⊢; exact gqu)).2


-- `local[index]` for an index that is itself an evaluable expression (it may read another vector).
theorem Ev.readRootEv (s : NState) (slot vb V vsc : Nat) (index : NExpr) (j : Nat) (ty : Ty)
    (wV maximum : Bool) (vBuffer : Buffer Value) (x : Int) (wi pi : Nat)
    (idx : ∀ u : NState, Core s u → ∃ t, Ev u index t (j : Int) [] wi pi)
    (hslot : s.vectorSlot slot = some vb) (vbinding : s.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩)
    (valid : s.frame.state.wellFormed = true)
    (vtag : s.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : s.frame.state.storage.lookup V = some vBuffer)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (vflag : s.frame.rootWritable[V]? = some maximum) (vpermission : wV = true → maximum = true)
    (item : vBuffer.items[j]? = some (Value.integer x)) :
    ∃ t, Ev s (.read ty (.local slot) index) t x [] (wi+3) (index.nodes+pi+3) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame vb V vsc ty wV maximum vBuffer vbinding valid vtag vfound
    lengths vflag vpermission
  have container := eval_local (s.charge 0 ((Container.local slot).nodes+index.nodes+2)) slot vb
    (by simpa [NState.vectorSlot] using hslot)
  have core1 : Core s ((s.charge 0 ((Container.local slot).nodes+index.nodes+2)).charge 1 1) :=
    (core_charge s 0 _).trans (core_charge _ 1 1)
  obtain ⟨t1,evI⟩ := idx _ core1
  have frame1 : t1.frame = s.frame := (Ev.good evI).1.1.trans core1.1
  obtain ⟨reference,hreference,hread⟩ := read_ok s.frame vb ty j x ⟨V,.integer ty,wV,.root vsc⟩ vBuffer
    ⟨.integer ty,none,some vsc,[]⟩ maximum vbinding rfl resolved object vmax vpermission item
  refine ⟨t1.charge 1 2,?_,?_,?_⟩
  · simp [NExpr.eval,container,evI.1,frame1,hreference,hread]
  · have := ((GoodF.charge s 0 ((Container.local slot).nodes+index.nodes+2)).trans (GoodF.charge _ 1 1)).trans
      (evI.2.1.trans (GoodF.charge t1 1 2))
    exact this.mono (by omega) (by simp [Container.nodes]; omega)
  · simp [frame1]

end Proofs.FillWriteStmt
