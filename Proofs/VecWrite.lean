import Proofs.VecPrepare
import Proofs.FillWriteStmt
import Proofs.InvPermFrame
import Proofs.VecStraight
import Proofs.StlContracts

namespace Proofs.VecWrite
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.FillWriteStmt Proofs.InvPermFrame
open Proofs.VecStraight Proofs.VecStmt
open Proofs.CppState (Cell)

-- The meaning of vector expressions over an explicit element type and contents (so that the contents can change).
def elemAtL (ty : Ty) (vec : List Int) (j : Int) : Option Int :=
  if 0 ≤ j then (vec[j.toNat]?).bind fun x => if ty.valid x = true then some x else none else none

def vdenL (ty : Ty) (vec : List Int) (env : Nat → Ty → Option Int) (e : NExpr) : Option Int :=
  if e.scalarOnly = true then e.denote env else
  match e with
  | .cast t op => (vdenL ty vec env op).bind t.convert
  | .unary t op e => (vdenL ty vec env e).bind fun v => t.convert (unaryValue op v)
  | .binary t op l r => (vdenL ty vec env l).bind fun a => (vdenL ty vec env r).bind fun b => t.convert (binaryValue op a b)
  | .size (.integer t) (.local 0) => if t = ty then some (vec.length : Int) else none
  | .read t (.local 0) index =>
      if t = ty ∧ index.scalarOnly = true then (index.denote env).bind (elemAtL ty vec) else none
  | _ => none

theorem vden_eq (c : VCtx) (env : Nat → Ty → Option Int) : ∀ e, vden c env e = vdenL c.ty c.vec env e := by
  intro e
  induction e using vden.induct c with
  | case1 t h => unfold vden vdenL; simp [h]
  | case2 ty op h ih => unfold vden vdenL; simp [h, ih]
  | case3 ty op e h ih => unfold vden vdenL; simp [h, ih]
  | case4 ty op l r h ihl ihr => unfold vden vdenL; simp [h, ihl, ihr]
  | case5 h => unfold vden vdenL; simp [h]
  | case6 ty hne h => unfold vden vdenL; simp [h, hne]
  | case7 ty index h h2 => unfold vden vdenL; have e : elemAt c = elemAtL c.ty c.vec := rfl; simp [h2, h, e]
  | case8 ty index h h2 => unfold vden vdenL; simp [h2, h]
  | case9 e h h2 h3 h4 h5 =>
    unfold vden vdenL
    simp only [h, if_false]

-- Frame facts for a writable flat root `R` whose contents are `vec`, after `wk` units of storage work.
structure FW (c : VCtx) (vec : List Int) (buf : Buffer Value) (wk : Nat) (fr : Frame) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  live : fr.state.liveSpace = c.L0
  work : fr.state.storage.work = c.T0 + wk
  strict : ∀ owner k, fr.state.forest.context owner = some k → k < c.sc
  count : fr.state.storage.objects.length = c.N
  bindings : fr.bindings = [⟨c.R,.integer c.ty,c.wV,.root c.vsc⟩]
  vtag : fr.state.forest.lookup c.R = some ⟨.integer c.ty,none,some c.vsc,[]⟩
  vfound : fr.state.storage.lookup c.R = some buf
  flagR : fr.rootWritable[c.R]? = some c.flag
  items : buf.items = vec.map Value.integer
  bvalid : buf.Valid (accepts (.integer c.ty))
  limit : buf.limit = CppVectorBindings.sizeLimit c.ty
  owner : buf.owner = c.R
  small : vec.length < 18446744073709551616

-- The read-only context describing the current contents.
def _root_.Proofs.VecExpr.VCtx.now (c : VCtx) (vec : List Int) (buf : Buffer Value) (wk : Nat) (h : buf.items = vec.map Value.integer)
    (small : vec.length < 18446744073709551616) : VCtx :=
  ⟨c.ty,c.wV,c.flag,c.R,c.vsc,buf,vec,h,c.perm,small,c.L0,c.T0+wk,c.sc,c.N⟩

theorem FW.toFV {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) : FV (c.now vec buf wk fw.items fw.small) fr :=
  ⟨fw.valid,fw.lengths,fw.live,fw.work,fw.strict,fw.count,fw.bindings,fw.vtag,fw.vfound,fw.flagR⟩

theorem ev_vdenL (c : VCtx) {vec : List Int} {buf : Buffer Value} {wk : Nat} (e : NExpr) (S : NState) (ps : PS)
    {B sc : Nat} (v : Int) (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) {fr : Frame}
    (hfr : S.frame = fr) (fw : FW c vec buf wk fr) (h : vdenL c.ty vec (penv1 ps) e = some v) :
    ∃ t, Ev S e t v [] (vwp e).1 (vwp e).2 := by
  subst hfr
  have h' : vden (c.now vec buf wk fw.items fw.small) (penv1 ps) e = some v := by
    rw [vden_eq]; exact h
  exact ev_vden (c.now vec buf wk fw.items fw.small) e S ps v qs fw.toFV h'

theorem FW.of_eq {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr fr' : Frame}
    (fw : FW c vec buf wk fr) (h : fr' = fr) : FW c vec buf wk fr' := by rw [h]; exact fw

theorem FW.noop {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr fr' : Frame}
    (fw : FW c vec buf wk fr) (same : SameObjects fr.state fr'.state)
    (rw : fr'.rootWritable = fr.rootWritable) (work : fr'.state.storage.work = fr.state.storage.work)
    (hb : fr'.bindings = fr.bindings) : FW c vec buf wk fr' := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,fw.items,fw.bvalid,fw.limit,fw.owner,fw.small⟩
  · rw [same.wellFormed]; exact fw.valid
  · rw [rw,same.1]; exact fw.lengths
  · rw [same.liveSpace]; exact fw.live
  · rw [work]; exact fw.work
  · intro owner k h
    rw [same.1] at h
    exact fw.strict owner k h
  · rw [same.2.1]; exact fw.count
  · rw [hb]; exact fw.bindings
  · rw [same.1]; exact fw.vtag
  · rw [same.lookup]; exact fw.vfound
  · rw [rw]; exact fw.flagR

theorem FW.wk_eq {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk wk' : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) (h : wk = wk') : FW c vec buf wk' fr := by rw [← h]; exact fw

theorem FW.fresh {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) {scope : Nat} (hsc : c.sc ≤ scope) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := fw.strict owner _ h
  omega

-- A write of one element: the contents change, nothing else does.
theorem FW.update {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) (p : Nat) (hp : p < vec.length) (x : Int) (hx : c.ty.valid x = true) :
    FW c (vec.set p x) {buf with items := buf.items.set p (Value.integer x)} (wk+1)
      (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩) := by
  have bound : c.R < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ c.R buf fw.vfound
  have lengthsEq : (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩).state.storage.objects.length =
      fr.state.storage.objects.length := by simp [Frame.updated]
  have forestEq : (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩).state.forest =
      fr.state.forest := rfl
  have other : ∀ o, o ≠ c.R → (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩).state.storage.lookup o =
      fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr c.R o buf _ (Ne.symm ho)
  have self := CppNestedOps.updated_lookup_self fr c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩ bound
  have live := liveSpace_update fr.state (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩).state
    c.R bound lengthsEq forestEq other
  have tag : fr.state.forest.lookup c.R = some (flatTag c.ty c.vsc) := fw.vtag
  have n0 := nodeSpace_flat_ty fr.state c.R c.vsc c.ty buf tag fw.vfound
  have n1 := nodeSpace_flat_ty (fr.updated c.R buf ⟨{buf with items := buf.items.set p (Value.integer x)},(),1,buf.capacity+2⟩).state
    c.R c.vsc c.ty {buf with items := buf.items.set p (Value.integer x)} (by rw [forestEq]; exact tag) self
  have newValid := CppVector.writeRef_preserves_valid buf (accepts (.integer c.ty)) p (Value.integer x)
    fw.bvalid (by simpa [accepts] using hx)
  have owns : ({buf with items := buf.items.set p (Value.integer x)} : Buffer Value).owner = c.R := fw.owner
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,self,?_,?_,?_,?_,?_,?_⟩
  · exact updated_wellFormed fr c.R buf (flatTag c.ty c.vsc) _ fw.valid tag bound owns
      (by simp [payloadOK,flatTag,newValid])
  · simpa [Frame.updated] using fw.lengths
  · rw [n0,n1] at live
    have := fw.live
    simp only [] at live
    omega
  · simp [Frame.updated,fw.work]
    omega
  · intro owner k h
    exact fw.strict owner k h
  · rw [lengthsEq]; exact fw.count
  · simpa [Frame.updated] using fw.bindings
  · exact fw.vtag
  · simpa [Frame.updated] using fw.flagR
  · simp [fw.items, List.map_set]
  · exact newValid
  · exact fw.limit
  · exact owns
  · simpa using fw.small

theorem write_flat_stmtE (s : NState) (slot rb : Nat) (iE vE : NExpr) (pos : Nat) (x : Int) (wv pv : Nat) (R sc : Nat) (ty : Ty)
    (buf : Buffer Value) (wi pi : Nat)
    (vEv : ∀ u : NState, Core s u → ∃ t, Ev u vE t x [] wv pv)
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
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+wv+wi+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+iE.nodes+vE.nodes+pv+pi+5) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  obtain ⟨t1,evV⟩ := vEv (s.charge 0 ((Container.local slot).nodes+iE.nodes+vE.nodes+3)) (core_charge _ _ _)
  have hexp := evV.1
  have good1 := Ev.good evV
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



-- `x[index] = value;` on the writable vector (location slot 0).
theorem write_stepW (c : VCtx) (hwr : c.wV = true) (hfl : c.flag = true) {vec : List Int} {buf : Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) (fw : FW c vec buf wk S.frame)
    (cq : Cq SPB TPB W S) (iE vE : NExpr) (p : Nat) (x : Int) (wv pv wi pi : Nat)
    (vEv : ∀ u : NState, Core S u → ∃ t, Ev u vE t x [] wv pv)
    (idx : ∀ u : NState, Core S u → ∃ t, Ev u iE t (p : Int) [] wi pi)
    (hp : p < vec.length) (hx : c.ty.valid x = true)
    (cap : liveS S+iE.nodes+vE.nodes+pv+pi+5 ≤ SPB) (space : c.L0+1 ≤ TPB) :
    ∃ t, (NStmt.write (.local 0) c.ty iE vE).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (sl1 ps.bs.length) ∧
      FW c (vec.set p x) {buf with items := buf.items.set p (Value.integer x)} (wk+1) t.frame ∧
      Cq SPB TPB (W+wv+wi+3) t := by
  have hs : S.vectorSlot 0 = some 0 := vectorSlot_zero qs.slots
  have fbind : S.frame.bindings[0]? = some (flatBinding c.R c.ty c.vsc) := by
    rw [fw.bindings, hwr]; rfl
  have lenB : buf.items.length = vec.length := by rw [fw.items]; simp
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := write_flat_stmtE S 0 0 iE vE p x wv pv c.R c.vsc c.ty buf wi pi
    vEv idx hs fbind fw.valid fw.vtag fw.vfound fw.lengths (by rw [fw.flagR, hfl]) hx (by omega)
  have fw' := fw.update p hp x hx
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+(buf.capacity+2-(buf.capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega

theorem mapM_intOf (items : List Value) (ints : List Int) (h : items.mapM Value.intOf = some ints) :
    items = ints.map Value.integer := by
  induction items generalizing ints with
  | nil => simp at h; subst h; rfl
  | cons a t ih =>
    cases a with
    | integer v =>
      simp only [List.mapM_cons, Value.intOf, Option.bind_some] at h
      cases ht : t.mapM Value.intOf with
      | none => simp [ht] at h
      | some rest =>
        simp [ht] at h
        subst h
        simp [ih rest ht]
    | child o => simp [Value.intOf] at h

theorem mapM_integer (ints : List Int) : (ints.map Value.integer).mapM Value.intOf = some ints := by
  induction ints with
  | nil => rfl
  | cons a t ih => simp [List.mapM_cons, Value.intOf, ih]

/-- The sorted contents keep every property the buffer needs. -/
theorem sorted_valid (buffer : Buffer Value) (ty : Ty) (ints : List Int)
    (hv : buffer.Valid (accepts (.integer ty))) (hints : buffer.items.mapM Value.intOf = some ints) :
    ({buffer with items := (ints.mergeSort (fun x y => decide (x ≤ y))).map Value.integer} :
      Buffer Value).Valid (accepts (.integer ty)) := by
  have hi := mapM_intOf _ _ hints
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, h2, ?_⟩
  · simp only [List.length_map, List.length_mergeSort]
    rw [hi] at h1; simpa using h1
  · simp only [List.all_eq_true, List.mem_map] at h3 ⊢
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hxm : x ∈ ints := (List.mem_mergeSort).mp hx
    exact h3 (Value.integer x) (by rw [hi]; exact List.mem_map.mpr ⟨x, hxm, rfl⟩)


/-- `std::sort(v.begin(), v.end())` on a writable flat integer root: the buffer is replaced by the sorted one. -/
theorem sort_ok (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (writable : binding.writable = true) (ints : List Int) (hints : buffer.items.mapM Value.intOf = some ints) :
    f.sortAll slot ty = some (f.updated binding.owner buffer
      ⟨{buffer with items := (ints.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
        Proofs.StlContracts.sortComparisons ints.length + ints.length,buffer.capacity+2⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,foundBuffer,_,_⟩ := CppNestedFacts.object_buffer f binding.owner _ buffer tag object
  have newValid := sorted_valid buffer ty ints bufferValid hints
  have hsort : sortFlat buffer (accepts (.integer ty)) binding.writable =
      some ⟨{buffer with items := (ints.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
        Proofs.StlContracts.sortComparisons ints.length + ints.length,buffer.capacity+2⟩ := by
    simp [sortFlat, bufferValid, writable, hints]
  have commit := commit_runs f binding.owner (.integer ty) buffer tag
    ⟨{buffer with items := (ints.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
      Proofs.StlContracts.sortComparisons ints.length + ints.length,buffer.capacity+2⟩ valid object tagFound
    foundBuffer (by simpa using owns) (by simp [payloadOK, element, newValid]) (by simp) (by simp)
  simp [Frame.sortAll, resolved, hsort, commit]


theorem FW.sort {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) :
    FW c (vec.mergeSort (fun x y => decide (x ≤ y))) {buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer} (wk + (Proofs.StlContracts.sortComparisons vec.length + vec.length))
      (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩) := by
  have bound : c.R < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ c.R buf fw.vfound
  have lengthsEq : (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩).state.storage.objects.length =
      fr.state.storage.objects.length := by simp [Frame.updated]
  have forestEq : (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩).state.forest =
      fr.state.forest := rfl
  have other : ∀ o, o ≠ c.R → (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩).state.storage.lookup o =
      fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr c.R o buf _ (Ne.symm ho)
  have self := CppNestedOps.updated_lookup_self fr c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩ bound
  have live := liveSpace_update fr.state (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩).state
    c.R bound lengthsEq forestEq other
  have tag : fr.state.forest.lookup c.R = some (flatTag c.ty c.vsc) := fw.vtag
  have n0 := nodeSpace_flat_ty fr.state c.R c.vsc c.ty buf tag fw.vfound
  have n1 := nodeSpace_flat_ty (fr.updated c.R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩).state
    c.R c.vsc c.ty {buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer} (by rw [forestEq]; exact tag) self
  have hints : buf.items.mapM Value.intOf = some vec := by
    rw [fw.items]; exact mapM_integer vec
  have newValid := sorted_valid buf c.ty vec fw.bvalid hints
  have owns : ({buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer} : Buffer Value).owner = c.R := fw.owner
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,self,?_,?_,?_,?_,?_,?_⟩
  · exact updated_wellFormed fr c.R buf (flatTag c.ty c.vsc) _ fw.valid tag bound owns
      (by simp [payloadOK,flatTag,newValid])
  · simpa [Frame.updated] using fw.lengths
  · rw [n0,n1] at live
    have := fw.live
    simp only [] at live
    omega
  · simp [Frame.updated,fw.work]
    omega
  · intro owner k h
    exact fw.strict owner k h
  · rw [lengthsEq]; exact fw.count
  · simpa [Frame.updated] using fw.bindings
  · exact fw.vtag
  · simpa [Frame.updated] using fw.flagR
  · rfl
  · exact newValid
  · exact fw.limit
  · exact owns
  · simpa using fw.small


theorem sort_flat_stmtE (s : NState) (slot rb : Nat) (R sc : Nat) (ty : Ty)
    (buf : Buffer Value) (vec : List Int)
    (hslot : s.vectorSlot slot = some rb) (binding : s.frame.bindings[rb]? = some (flatBinding R ty sc))
    (valid : s.frame.state.wellFormed = true) (vtag : s.frame.state.forest.lookup R = some (flatTag ty sc))
    (vfound : s.frame.state.storage.lookup R = some buf)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (hints : buf.items.mapM Value.intOf = some vec) :
    ∃ t, (NStmt.sortVec (.local slot) ty).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
        Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩ ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+3) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  have container : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+2)) =
      some ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1,rb) :=
    eval_local _ slot rb (by simpa [NState.vectorSlot] using hslot)
  have hsort := sort_ok s.frame rb ty (flatBinding R ty sc) buf ⟨.integer ty,none,some sc,[]⟩
    (by simpa [flatBinding] using resolved) (by simpa [flatBinding] using object) rfl vec hints
  have hsort' : ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).frame.sortAll rb ty = some
      (s.frame.updated R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
        Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩) := by
    simpa [flatBinding] using hsort
  have gAll := (GoodF.charge s 0 ((Container.local slot).nodes+2)).trans (GoodF.charge (s.charge 0 ((Container.local slot).nodes+2)) 1 1)
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) = liveS s := liveS_of_memory m b k'
  have stateEq : ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).frame.state = s.frame.state := rfl
  refine ⟨((withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf
    ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
      Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩)).release s).charge 1 1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,container,hsort,flatBinding,withFrame]
  · simp [NState.release,Frame.updated,withFrame,List.take_length]
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp [charge_work] <;> omega
  · simp [charge_work,Container.nodes] <;> omega
  · simp [charge_scalar_peak] <;> omega
  · simp [charge_scalar_peak,Container.nodes,liveS] <;> omega
  · exact (peak_after ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩)) s 1 1 rfl rfl
      (by simp [Frame.updated,stateEq] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf ⟨{buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),Proofs.StlContracts.sortComparisons vec.length + vec.length,buf.capacity+2⟩)) s 1 1 rfl rfl
      (by simp [Frame.updated,stateEq] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).2

-- `std::sort(x.begin(), x.end());` on the writable vector (location slot 0).
theorem sort_stepW (c : VCtx) (hwr : c.wV = true) (hfl : c.flag = true) {vec : List Int} {buf : Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) (fw : FW c vec buf wk S.frame)
    (cq : Cq SPB TPB W S)
    (cap : liveS S+3 ≤ SPB) (space : c.L0+1 ≤ TPB) :
    ∃ t, (NStmt.sortVec (.local 0) c.ty).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (sl1 ps.bs.length) ∧
      FW c (vec.mergeSort (fun x y => decide (x ≤ y))) {buf with items := (vec.mergeSort (fun x y => decide (x ≤ y))).map Value.integer}
        (wk + (Proofs.StlContracts.sortComparisons vec.length + vec.length)) t.frame ∧
      Cq SPB TPB (W+3) t := by
  have hs : S.vectorSlot 0 = some 0 := vectorSlot_zero qs.slots
  have fbind : S.frame.bindings[0]? = some (flatBinding c.R c.ty c.vsc) := by
    rw [fw.bindings, hwr]; rfl
  have hints : buf.items.mapM Value.intOf = some vec := by
    rw [fw.items]; exact mapM_integer vec
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := sort_flat_stmtE S 0 0 c.R c.vsc c.ty buf vec
    hs fbind fw.valid fw.vtag fw.vfound fw.lengths (by rw [fw.flagR, hfl]) hints
  have fw' := FW.sort fw
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+(buf.capacity+2-(buf.capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega

/-- The deduplicated contents keep every property the buffer needs. -/
theorem dedup_valid (buffer : Buffer Value) (ty : Ty) (ints : List Int)
    (hv : buffer.Valid (accepts (.integer ty))) (hints : buffer.items.mapM Value.intOf = some ints) :
    ({buffer with items := (uniqAdj ints).map Value.integer, epoch := buffer.epoch+1} :
      Buffer Value).Valid (accepts (.integer ty)) := by
  have hi := mapM_intOf _ _ hints
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, h2, ?_⟩
  · simp only [List.length_map]
    have := uniqAdj_length ints
    rw [hi] at h1; simp at h1; omega
  · simp only [List.all_eq_true, List.mem_map] at h3 ⊢
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hxm : x ∈ ints := uniqAdj_mem ints x hx
    exact h3 (Value.integer x) (by rw [hi]; exact List.mem_map.mpr ⟨x, hxm, rfl⟩)


/-- `v.erase(std::unique(..), v.end())` on a writable flat integer root: the buffer is replaced by the deduplicated one. -/
theorem dedup_ok (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (writable : binding.writable = true) (ints : List Int) (hints : buffer.items.mapM Value.intOf = some ints) :
    f.dedupAll slot ty = some (f.updated binding.owner buffer
      ⟨{buffer with items := (uniqAdj ints).map Value.integer, epoch := buffer.epoch+1},(),
        ints.length + ints.length,buffer.capacity+2⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,foundBuffer,_,_⟩ := CppNestedFacts.object_buffer f binding.owner _ buffer tag object
  have newValid := dedup_valid buffer ty ints bufferValid hints
  have hsort : dedupFlat buffer (accepts (.integer ty)) binding.writable =
      some ⟨{buffer with items := (uniqAdj ints).map Value.integer, epoch := buffer.epoch+1},(),
        ints.length + ints.length,buffer.capacity+2⟩ := by
    simp [dedupFlat, bufferValid, writable, hints]
  have commit := commit_runs f binding.owner (.integer ty) buffer tag
    ⟨{buffer with items := (uniqAdj ints).map Value.integer, epoch := buffer.epoch+1},(),
      ints.length + ints.length,buffer.capacity+2⟩ valid object tagFound
    foundBuffer (by simpa using owns) (by simp [payloadOK, element, newValid]) (by simp) (by simp)
  simp [Frame.dedupAll, resolved, hsort, commit]


theorem FW.dedup {c : VCtx} {vec : List Int} {buf : Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FW c vec buf wk fr) :
    FW c (uniqAdj vec) {buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1} (wk + (vec.length + vec.length))
      (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩) := by
  have bound : c.R < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ c.R buf fw.vfound
  have lengthsEq : (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩).state.storage.objects.length =
      fr.state.storage.objects.length := by simp [Frame.updated]
  have forestEq : (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩).state.forest =
      fr.state.forest := rfl
  have other : ∀ o, o ≠ c.R → (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩).state.storage.lookup o =
      fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr c.R o buf _ (Ne.symm ho)
  have self := CppNestedOps.updated_lookup_self fr c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩ bound
  have live := liveSpace_update fr.state (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩).state
    c.R bound lengthsEq forestEq other
  have tag : fr.state.forest.lookup c.R = some (flatTag c.ty c.vsc) := fw.vtag
  have n0 := nodeSpace_flat_ty fr.state c.R c.vsc c.ty buf tag fw.vfound
  have n1 := nodeSpace_flat_ty (fr.updated c.R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩).state
    c.R c.vsc c.ty {buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1} (by rw [forestEq]; exact tag) self
  have hints : buf.items.mapM Value.intOf = some vec := by
    rw [fw.items]; exact mapM_integer vec
  have newValid := dedup_valid buf c.ty vec fw.bvalid hints
  have owns : ({buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1} : Buffer Value).owner = c.R := fw.owner
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,self,?_,?_,?_,?_,?_,?_⟩
  · exact updated_wellFormed fr c.R buf (flatTag c.ty c.vsc) _ fw.valid tag bound owns
      (by simp [payloadOK,flatTag,newValid])
  · simpa [Frame.updated] using fw.lengths
  · rw [n0,n1] at live
    have := fw.live
    simp only [] at live
    omega
  · simp [Frame.updated,fw.work]
    omega
  · intro owner k h
    exact fw.strict owner k h
  · rw [lengthsEq]; exact fw.count
  · simpa [Frame.updated] using fw.bindings
  · exact fw.vtag
  · simpa [Frame.updated] using fw.flagR
  · rfl
  · exact newValid
  · exact fw.limit
  · exact owns
  · have := uniqAdj_length vec
    have h := fw.small
    simp only [List.length_map] at *
    omega


theorem dedup_flat_stmtE (s : NState) (slot rb : Nat) (R sc : Nat) (ty : Ty)
    (buf : Buffer Value) (vec : List Int)
    (hslot : s.vectorSlot slot = some rb) (binding : s.frame.bindings[rb]? = some (flatBinding R ty sc))
    (valid : s.frame.state.wellFormed = true) (vtag : s.frame.state.forest.lookup R = some (flatTag ty sc))
    (vfound : s.frame.state.storage.lookup R = some buf)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (hints : buf.items.mapM Value.intOf = some vec) :
    ∃ t, (NStmt.dedupVec (.local slot) ty).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),
        vec.length + vec.length,buf.capacity+2⟩ ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+3 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+3) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨resolved,object,vmax⟩ := resolve_vroot s.frame rb R sc ty true true buf
    (by simpa [flatBinding] using binding) valid (by simpa [flatTag] using vtag) vfound lengths
    (by simpa using flag) (fun h => rfl)
  have container : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+2)) =
      some ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1,rb) :=
    eval_local _ slot rb (by simpa [NState.vectorSlot] using hslot)
  have hsort := dedup_ok s.frame rb ty (flatBinding R ty sc) buf ⟨.integer ty,none,some sc,[]⟩
    (by simpa [flatBinding] using resolved) (by simpa [flatBinding] using object) rfl vec hints
  have hsort' : ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).frame.dedupAll rb ty = some
      (s.frame.updated R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),
        vec.length + vec.length,buf.capacity+2⟩) := by
    simpa [flatBinding] using hsort
  have gAll := (GoodF.charge s 0 ((Container.local slot).nodes+2)).trans (GoodF.charge (s.charge 0 ((Container.local slot).nodes+2)) 1 1)
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) = liveS s := liveS_of_memory m b k'
  have stateEq : ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1).frame.state = s.frame.state := rfl
  refine ⟨((withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf
    ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),
      vec.length + vec.length,buf.capacity+2⟩)).release s).charge 1 1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NStmt.run,container,hsort,flatBinding,withFrame]
  · simp [NState.release,Frame.updated,withFrame,List.take_length]
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp [charge_work] <;> omega
  · simp [charge_work,Container.nodes] <;> omega
  · simp [charge_scalar_peak] <;> omega
  · simp [charge_scalar_peak,Container.nodes,liveS] <;> omega
  · exact (peak_after ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩)) s 1 1 rfl rfl
      (by simp [Frame.updated,stateEq] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (withFrame ((s.charge 0 ((Container.local slot).nodes+2)).charge 1 1) (s.frame.updated R buf ⟨{buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1},(),vec.length + vec.length,buf.capacity+2⟩)) s 1 1 rfl rfl
      (by simp [Frame.updated,stateEq] <;> omega) gql (by rw [stateEq] at gqu ⊢; exact gqu)).2

-- `std::sort(x.begin(), x.end());` on the writable vector (location slot 0).
theorem dedup_stepW (c : VCtx) (hwr : c.wV = true) (hfl : c.flag = true) {vec : List Int} {buf : Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) (fw : FW c vec buf wk S.frame)
    (cq : Cq SPB TPB W S)
    (cap : liveS S+3 ≤ SPB) (space : c.L0+1 ≤ TPB) :
    ∃ t, (NStmt.dedupVec (.local 0) c.ty).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (sl1 ps.bs.length) ∧
      FW c (uniqAdj vec) {buf with items := (uniqAdj vec).map Value.integer, epoch := buf.epoch+1}
        (wk + (vec.length + vec.length)) t.frame ∧
      Cq SPB TPB (W+3) t := by
  have hs : S.vectorSlot 0 = some 0 := vectorSlot_zero qs.slots
  have fbind : S.frame.bindings[0]? = some (flatBinding c.R c.ty c.vsc) := by
    rw [fw.bindings, hwr]; rfl
  have hints : buf.items.mapM Value.intOf = some vec := by
    rw [fw.items]; exact mapM_integer vec
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := dedup_flat_stmtE S 0 0 c.R c.vsc c.ty buf vec
    hs fbind fw.valid fw.vtag fw.vfound fw.lengths (by rw [fw.flagR, hfl]) hints
  have fw' := FW.dedup fw
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+(buf.capacity+2-(buf.capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega


def WrV (w : Bool) : Command → Bool
  | .primitive (.declare _ _ e) => true
  | .primitive (.assign _ _ e) => true
  | .primitive (.ret e) => true
  | .primitive (.check e) => true
  | .primitive (.write (.local 0) _ _ _) => w
  | .primitive (.sortVec (.local 0) _) => w
  | .primitive (.dedupVec (.local 0) _) => w
  | .primitive .skip => true
  | .sequence a b => WrV w a && WrV w b
  | .scope body => WrV w body
  | .branch c y n => WrV w y && WrV w n
  | .whileLoop c b => WrV w b
  | _ => false

structure PRW where
  ps : PS
  vec : List Int
  ret : Option Int
  cost : Nat
  need : Nat
  wk : Nat

def pstmtW (ty0 : Ty) : NStmt → PS → List Int → Option PRW
  | .declare ty w e, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) e
      let v' ← ty.convert v
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+4,0⟩
  | .assign (slot+1) ty e, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) e
      let b ← ps.bs[slot]?
      let c ← ps.mem[b.address]?
      if c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true then do
        let v' ← ty.convert v
        some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩
      else none
  | .ret e, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) e
      some ⟨ps,vec,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩
  | .check e, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) e
      if v ≠ 0 then some ⟨ps,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ else none
  | .write (.local 0) ty iE vE, ps, vec => do
      let x ← vdenL ty0 vec (penv1 ps) vE
      let p ← vdenL ty0 vec (penv1 ps) iE
      if ty = ty0 ∧ 0 ≤ p ∧ p.toNat < vec.length ∧ ty0.valid x = true then
        some ⟨ps,vec.set p.toNat x,none,(vwp vE).1+(vwp iE).1+3,
          ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5,1⟩
      else none
  | .sortVec (.local 0) ty, ps, vec =>
      if ty = ty0 then
        some ⟨ps,vec.mergeSort (fun x y => decide (x ≤ y)),none,3,ps.mem.length+ps.bs.length+3,
          Proofs.StlContracts.sortComparisons vec.length + vec.length⟩
      else none
  | .dedupVec (.local 0) ty, ps, vec =>
      if ty = ty0 then
        some ⟨ps,uniqAdj vec,none,3,ps.mem.length+ps.bs.length+3,vec.length+vec.length⟩
      else none
  | .skip, ps, vec => some ⟨ps,vec,none,0,ps.mem.length+ps.bs.length,0⟩
  | _, _, _ => none

theorem pstmtW_write_inv (ty0 : Ty) (container : Container) (ty : Ty) (iE vE : NExpr) (ps : PS) (vec : List Int) (r : PRW)
    (h : pstmtW ty0 (.write container ty iE vE) ps vec = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5 := by
  cases container with
  | «local» k =>
    cases k with
    | zero =>
      simp only [pstmtW, Bind.bind, Option.bind] at h
      cases h1 : vdenL ty0 vec (penv1 ps) vE with
      | none => simp [h1] at h
      | some x =>
        simp only [h1] at h
        cases h2 : vdenL ty0 vec (penv1 ps) iE with
        | none => simp [h2] at h
        | some p =>
          simp only [h2] at h
          by_cases ok : ty = ty0 ∧ 0 ≤ p ∧ p.toNat < vec.length ∧ ty0.valid x = true
          · rw [if_pos ok] at h
            cases h
            exact ⟨rfl,rfl⟩
          · rw [if_neg ok] at h; simp at h
    | succ k => simp [pstmtW] at h
  | row _ _ _ => simp [pstmtW] at h


theorem pstmtW_sort_inv (ty0 : Ty) (container : Container) (ty : Ty) (ps : PS) (vec : List Int) (r : PRW)
    (h : pstmtW ty0 (.sortVec container ty) ps vec = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+3 := by
  cases container with
  | «local» k =>
    cases k with
    | zero =>
      simp only [pstmtW] at h
      by_cases ok : ty = ty0
      · rw [if_pos ok] at h; cases h; exact ⟨rfl,rfl⟩
      · rw [if_neg ok] at h; simp at h
    | succ k => simp [pstmtW] at h
  | row _ _ _ => simp [pstmtW] at h

theorem pstmtW_dedup_inv (ty0 : Ty) (container : Container) (ty : Ty) (ps : PS) (vec : List Int) (r : PRW)
    (h : pstmtW ty0 (.dedupVec container ty) ps vec = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+3 := by
  cases container with
  | «local» k =>
    cases k with
    | zero =>
      simp only [pstmtW] at h
      by_cases ok : ty = ty0
      · rw [if_pos ok] at h; cases h; exact ⟨rfl,rfl⟩
      · rw [if_neg ok] at h; simp at h
    | succ k => simp [pstmtW] at h
  | row _ _ _ => simp [pstmtW] at h

def pexecW (ty0 : Ty) : Nat → Command → PS → List Int → Option PRW
  | _, .primitive st, ps, vec => pstmtW ty0 st ps vec
  | fu, .sequence a b, ps, vec => do
      let r ← pexecW ty0 fu a ps vec
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecW ty0 fu b r.ps r.vec
          some ⟨r2.ps,r2.vec,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩
  | fu, .scope body, ps, vec => do
      let r ← pexecW ty0 fu body ps vec
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.vec,r.ret,r.cost+1,r.need,r.wk⟩
  | fu, .branch c y n, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) c
      if v = 0 then do
        let r ← pexecW ty0 fu n ps vec
        some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩
      else do
        let r ← pexecW ty0 fu y ps vec
        some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩
  | 0, .whileLoop _ _, _, _ => none
  | fu+1, .whileLoop c b, ps, vec => do
      let v ← vdenL ty0 vec (penv1 ps) c
      if v = 0 then some ⟨ps,vec,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2,0⟩
      else do
        let r ← pexecW ty0 (fu+1) b ps vec
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecW ty0 fu (.whileLoop c b) r.ps r.vec
            some ⟨r2.ps,r2.vec,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need),r.wk+r2.wk⟩
  | _, _, _, _ => none
termination_by fu c => (fu, c)


theorem pexecW_ext (vc : VCtx) (w : Bool) : ∀ (c : Command), WrV w c = true → ∀ (fu : Nat) (ps : PS) (vec : List Int) (r : PRW), pexecW vc.ty fu c ps vec = some r → Ext ps r.ps := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vec r hr
    cases st with
    | declare ty w e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' =>
          simp only [h2] at hr
          cases hr
          refine ⟨by simp,?_,by simp,?_⟩
          · simp [List.take_left']
          · simp [List.take_left']
    | assign slot0 ty e =>
      rcases slot0 with _ | slot
      · simp [pexecW,pstmtW] at hr
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[slot]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' =>
                simp only [h4] at hr
                cases hr
                refine ⟨Nat.le_refl _,List.take_length,by simp,?_⟩
                have hl : (ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length = ps.mem.set b.address ⟨ty,v'⟩ :=
                  List.take_of_length_le (by simp)
                show ((ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length).map Cell.type = ps.mem.map Cell.type
                rw [hl]
                exact map_type_set_gen ps.mem b.address c ty v' h3 ok.1
            · simp [ok] at hr
    | ret e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; exact Ext.refl _
    | check e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; exact Ext.refl _
        · simp [nz] at hr
    | skip => simp only [pexecW,pstmtW] at hr; cases hr; exact Ext.refl _
    | write container ty iE vE =>
      rw [pexecW] at hr
      obtain ⟨h1,_⟩ := pstmtW_write_inv _ _ _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | sortVec container ty =>
      rw [pexecW] at hr
      obtain ⟨h1,_⟩ := pstmtW_sort_inv _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | dedupVec container ty =>
      rw [pexecW] at hr
      obtain ⟨h1,_⟩ := pstmtW_dedup_inv _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | _ => simp [pexecW,pstmtW] at hr
  | sequence a b iha ihb =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu a ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps vec r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecW vc.ty fu b r1.ps r1.vec with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          exact (iha hs.1 fu ps vec r1 h1).trans (ihb hs.2 fu r1.ps r1.vec r2 h2)
  | scope body ih =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu body ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      obtain ⟨l1,t1,m1,y1⟩ := ih hs fu ps vec r1 h1
      refine ⟨by simp; omega,?_,by simp; omega,?_⟩
      · simp [List.take_take,t1]
      · simp [List.take_take,y1]
  | branch c y n ihy ihn =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecW vc.ty fu n ps vec with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihn hs.2 fu ps vec r1 h2
      · simp only [z,if_false] at hr
        cases h2 : pexecW vc.ty fu y ps vec with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihy hs.1 fu ps vec r1 h2
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [WrV,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps vec r hr; simp [pexecW] at hr
    | succ fu ihf =>
      intro ps vec r hr
      simp only [pexecW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; exact Ext.refl _
        · simp only [z,if_false] at hr
          cases h2 : pexecW vc.ty (fu+1) b ps vec with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecW vc.ty fu (.whileLoop cnd b) r1.ps r1.vec with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                exact (ih hs (fu+1) ps vec r1 h2).trans (ihf r1.ps r1.vec r2 h3)
  | _ => intro hs; simp [WrV] at hs





theorem pexecW_need (vc : VCtx) (w : Bool) : ∀ (c : Command), WrV w c = true → ∀ (fu : Nat) (ps : PS) (vec : List Int) (r : PRW), pexecW vc.ty fu c ps vec = some r →
    r.ps.mem.length+r.ps.bs.length ≤ r.need := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vec r hr
    cases st with
    | declare ty w e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' => simp only [h2] at hr; cases hr; simp; omega
    | assign slot0 ty e =>
      rcases slot0 with _ | slot
      · simp [pexecW,pstmtW] at hr
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[slot]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' => simp only [h4] at hr; cases hr; simp; omega
            · simp [ok] at hr
    | ret e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; simp; omega
    | check e =>
      simp only [pexecW,pstmtW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; simp; omega
        · simp [nz] at hr
    | skip => simp only [pexecW,pstmtW] at hr; cases hr; simp
    | write container ty iE vE =>
      rw [pexecW] at hr
      obtain ⟨h1,h2⟩ := pstmtW_write_inv _ _ _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | sortVec container ty =>
      rw [pexecW] at hr
      obtain ⟨h1,h2⟩ := pstmtW_sort_inv _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | dedupVec container ty =>
      rw [pexecW] at hr
      obtain ⟨h1,h2⟩ := pstmtW_dedup_inv _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | _ => simp [pexecW,pstmtW] at hr
  | sequence a b iha ihb =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu a ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps vec r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecW vc.ty fu b r1.ps r1.vec with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have := ihb hs.2 fu r1.ps r1.vec r2 h2
          simp; omega
  | scope body ih =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu body ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have := ih hs fu ps vec r1 h1
      simp; omega
  | branch c y n ihy ihn =>
    intro hs fu ps vec r hr
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecW vc.ty fu n ps vec with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihn hs.2 fu ps vec r1 h2; simp; omega
      · simp only [z,if_false] at hr
        cases h2 : pexecW vc.ty fu y ps vec with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihy hs.1 fu ps vec r1 h2; simp; omega
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [WrV,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps vec r hr; simp [pexecW] at hr
    | succ fu ihf =>
      intro ps vec r hr
      simp only [pexecW,Bind.bind,Option.bind] at hr
      cases h1 : vdenL vc.ty vec (penv1 ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; simp; omega
        · simp only [z,if_false] at hr
          cases h2 : pexecW vc.ty (fu+1) b ps vec with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecW vc.ty fu (.whileLoop cnd b) r1.ps r1.vec with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                have := ihf r1.ps r1.vec r2 h3
                simp; omega
  | _ => intro hs; simp [WrV] at hs




abbrev QpostW (vc : VCtx) (r : PRW) (B sc : Nat) (SPB TPB W wk : Nat) (step : NStep) : Prop :=
  step.returned = r.ret.map Ret.scalar ∧ step.breaking = false ∧
  QS step.state [] B sc r.ps.mem r.ps.bs (sl1 r.ps.bs.length) ∧
  (∃ buf', FW vc r.vec buf' (wk+r.wk) step.state.frame) ∧
  Cq SPB TPB (W+r.cost) step.state

theorem soundW_prim (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) (st : NStmt) (hs : WrV w (.primitive st) = true) (ps : PS) (vec : List Int) (r : PRW)
    (hr : pstmtW vc.ty st ps vec = some r) {B sc SPB TPB W wk : Nat} {buf : Buffer Value} (S : NState)
    (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) (fw : FW vc vec buf wk S.frame) (cq : Cq SPB TPB W S)
    (hB : B ≤ ps.mem.length) (hneed : r.need ≤ SPB+B) (space : vc.L0+1 ≤ TPB) :
    RunsTo (.primitive st) S (QpostW vc r B sc SPB TPB W wk) := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have live := live_psV qs
  cases st with
  | declare ty w e =>
    simp only [pstmtW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ty.convert v with
      | none => simp [h2] at hr
      | some v' =>
        simp only [h2] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vdenL vc e S ps v qs rfl fw h1
        have good := Ev.good ev
        obtain ⟨t,run,fr,qs',cq'⟩ := decl_stepG S t0 e ty w v v' _ _ qs cq (by simp at hneed; omega) ev.1 good
          (vwp_pos e) h2
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs'.of_eq (by simp) (by simp) ?_,⟨buf,fw.of_eq fr⟩,cq'⟩
        simp [sl1_succ]
  | assign slot0 ty e =>
    rcases slot0 with _ | slot
    · simp [pstmtW] at hr
    simp only [pstmtW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ps.bs[slot]? with
      | none => simp [h2] at hr
      | some b =>
        simp only [h2] at hr
        cases h3 : ps.mem[b.address]? with
        | none => simp [h3] at hr
        | some c =>
          simp only [h3] at hr
          by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
          · simp only [ok,and_self,if_true] at hr
            cases h4 : ty.convert v with
            | none => simp [h4] at hr
            | some v' =>
              simp only [h4] at hr
              cases hr
              have lt : slot < ps.bs.length := (List.getElem?_eq_some_iff.mp h2).1
              obtain ⟨t0,ev⟩ := ev_vdenL vc e S ps v qs rfl fw h1
              have good := Ev.good ev
              obtain ⟨t,run,fr,qs',cq'⟩ := assign_stepG S t0 e (slot+1) slot ty v v' _ _ b c qs cq (by simp at hneed; omega)
                ev.1 good h4 (by simp [qs.slots,sl1_get _ _ lt]) h2 (by simpa using h3) ok.1 ok.2.1 ok.2.2
                (cells' := ps.mem.set b.address ⟨ty,v'⟩) (by simp)
              apply RunsTo.primitive run
              exact ⟨rfl,rfl,qs',⟨buf,fw.of_eq fr⟩,cq'⟩
          · simp [ok] at hr
  | ret e =>
    simp only [pstmtW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases hr
      obtain ⟨u,ev⟩ := ev_vdenL vc e S ps v qs rfl fw h1
      have good := Ev.good ev
      have self := release_self good.1.1
      have run : (NStmt.ret e).run S = some ⟨u.charge 1 0,some (.scalar v),false⟩ := by
        simp [NStmt.run,ev.1,self]
      have cqU : Cq SPB TPB (W+(vwp e).1) u := cq.good good (by simp at hneed; omega)
      have cqC : Cq SPB TPB (W+(vwp e).1+1) (u.charge 1 0) :=
        cqU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
      apply RunsTo.primitive run
      exact ⟨rfl,rfl,qs.core (good.1.trans (core_charge u 1 0)),⟨buf,fw.of_eq (by simpa using good.1.1)⟩,cqC⟩
  | check e =>
    simp only [pstmtW,Bind.bind,Option.bind] at hr
    cases h1 : vdenL vc.ty vec (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases nz : v ≠ 0
      · simp only [nz,ne_eq,not_false_eq_true,if_true] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vdenL vc e S ps v qs rfl fw h1
        obtain ⟨t,run,good⟩ := check_good_g e S t0 v _ _ ev.1 (Ev.good ev) nz
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs.core good.1,⟨buf,fw.of_eq good.1.1⟩,?_⟩
        exact cq.good good (by simp at hneed; omega)
      · simp [nz] at hr
  | skip =>
    simp only [pstmtW] at hr
    cases hr
    apply RunsTo.skip
    exact ⟨rfl,rfl,qs,⟨buf,fw⟩,cq.mono (by omega)⟩
  | write container ty iE vE =>
    cases container with
    | «local» k =>
      cases k with
      | zero =>
        simp only [pstmtW, Bind.bind, Option.bind] at hr
        cases h1 : vdenL vc.ty vec (penv1 ps) vE with
        | none => simp [h1] at hr
        | some x =>
          simp only [h1] at hr
          cases h2 : vdenL vc.ty vec (penv1 ps) iE with
          | none => simp [h2] at hr
          | some p =>
            simp only [h2] at hr
            by_cases ok : ty = vc.ty ∧ 0 ≤ p ∧ p.toNat < vec.length ∧ vc.ty.valid x = true
            · rw [if_pos ok] at hr
              cases hr
              obtain ⟨hty, hp0, hp1, hxv⟩ := ok
              subst hty
              have hpn : ((p.toNat : Nat) : Int) = p := Int.toNat_of_nonneg hp0
              have vEv : ∀ u : NState, Core S u → ∃ t, Ev u vE t x [] (vwp vE).1 (vwp vE).2 :=
                fun u core => ev_vdenL vc vE u ps x (qs.core core) core.1 fw h1
              have idx : ∀ u : NState, Core S u → ∃ t, Ev u iE t ((p.toNat : Nat) : Int) [] (vwp iE).1 (vwp iE).2 := by
                intro u core
                rw [hpn]
                exact ev_vdenL vc iE u ps p (qs.core core) core.1 fw h2
              have cap : liveS S+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5 ≤ SPB := by
                rw [live_psV qs]; simp at hneed; omega
              obtain ⟨hwv, hfl⟩ := hw (by simpa [WrV] using hs)
              obtain ⟨t,run,qs',fw',cq'⟩ := write_stepW vc hwv hfl S ps qs fw cq iE vE p.toNat x (vwp vE).1 (vwp vE).2 (vwp iE).1
                (vwp iE).2 vEv idx hp1 hxv cap space
              apply RunsTo.primitive run
              exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
            · rw [if_neg ok] at hr; simp at hr
      | succ k => simp [pstmtW] at hr
    | row _ _ _ => simp [pstmtW] at hr
  | sortVec container ty =>
    cases container with
    | «local» k =>
      cases k with
      | zero =>
        simp only [pstmtW] at hr
        by_cases ok : ty = vc.ty
        · rw [if_pos ok] at hr
          cases hr
          subst ok
          have cap : liveS S+3 ≤ SPB := by
            rw [live_psV qs]; simp at hneed; omega
          obtain ⟨hwv, hfl⟩ := hw (by simpa [WrV] using hs)
          obtain ⟨t,run,qs',fw',cq'⟩ := sort_stepW vc hwv hfl S ps qs fw cq cap space
          apply RunsTo.primitive run
          exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
        · rw [if_neg ok] at hr; simp at hr
      | succ k => simp [pstmtW] at hr
    | row _ _ _ => simp [pstmtW] at hr
  | dedupVec container ty =>
    cases container with
    | «local» k =>
      cases k with
      | zero =>
        simp only [pstmtW] at hr
        by_cases ok : ty = vc.ty
        · rw [if_pos ok] at hr
          cases hr
          subst ok
          have cap : liveS S+3 ≤ SPB := by
            rw [live_psV qs]; simp at hneed; omega
          obtain ⟨hwv, hfl⟩ := hw (by simpa [WrV] using hs)
          obtain ⟨t,run,qs',fw',cq'⟩ := dedup_stepW vc hwv hfl S ps qs fw cq cap space
          apply RunsTo.primitive run
          exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
        · rw [if_neg ok] at hr; simp at hr
      | succ k => simp [pstmtW] at hr
    | row _ _ _ => simp [pstmtW] at hr
  | _ => simp [WrV] at hs



theorem soundW (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) : ∀ (c : Command), WrV w c = true → ∀ (fu : Nat) (ps : PS) (vec : List Int) (r : PRW), pexecW vc.ty fu c ps vec = some r →
    ∀ {B sc SPB TPB W wk : Nat} {buf : Buffer Value} (S : NState), QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length) →
      FW vc vec buf wk S.frame → Cq SPB TPB W S → B ≤ ps.mem.length → ps.mem.length+ps.bs.length ≤ SPB+B →
      r.need ≤ SPB+B → vc.sc ≤ sc → vc.L0+1 ≤ TPB →
      RunsTo c S (QpostW vc r B sc SPB TPB W wk) := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vec r hr B sc SPB TPB W wk buf S qs fw cq hB hlive hneed hsc hL
    exact soundW_prim vc w hw st hs ps vec r (by simpa [pexecW] using hr) S qs fw cq hB hneed hL
  | sequence a b iha ihb =>
    intro hs fu ps vec r hr B sc SPB TPB W wk buf S qs fw cq hB hlive hneed hsc hL
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu a ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v =>
        simp only [hret] at hr
        have e := Option.some.inj hr
        rw [← e] at hneed ⊢
        apply RunsTo.sequence
        refine (iha hs.1 fu ps vec r1 h1 S qs fw cq hB hlive hneed hsc hL).mono ?_
        intro step post
        left
        exact ⟨Or.inl (by rw [post.1,hret]; rfl),post⟩
      | none =>
        simp only [hret] at hr
        cases h2 : pexecW vc.ty fu b r1.ps r1.vec with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have ext := pexecW_ext vc w a hs.1 fu ps vec r1 h1
          have nd := pexecW_need vc w a hs.1 fu ps vec r1 h1
          apply RunsTo.sequence
          refine (iha hs.1 fu ps vec r1 h1 S qs fw cq hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro step ⟨ret,brk,qs1,⟨buf1,fw1⟩,cq1⟩
          right
          refine ⟨by simpa [hret] using ret,brk,?_⟩
          have := ihb hs.2 fu r1.ps r1.vec r2 h2 step.state qs1 fw1 cq1 (Nat.le_trans hB ext.2.2.1)
            (by simp at hneed; omega) (by simp at hneed; omega) hsc hL
          refine this.mono ?_
          intro st2 ⟨a1,a2,a3,⟨bf,a4⟩,a5⟩
          exact ⟨a1,a2,a3,⟨bf,a4.wk_eq (by simp; omega)⟩,a5.mono (by simp; omega)⟩
  | scope body ih =>
    intro hs fu ps vec r hr B sc SPB TPB W wk buf S qs fw cq hB hlive hneed hsc hL
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    cases h1 : pexecW vc.ty fu body ps vec with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have ext := pexecW_ext vc w body hs fu ps vec r1 h1
      obtain ⟨l1,t1,m1,y1⟩ := ext
      have eS : (fx SPB TPB).SPB = SPB := rfl
      have eT : (fx SPB TPB).TPB = TPB := rfl
      apply RunsTo.scope
      have qs' : QS (scopeUp S) [] B (sc+1) ps.mem ps.bs (sl1 ps.bs.length) := qs.enter
      refine (ih hs fu ps vec r1 h1 (scopeUp S) qs' fw cq.enter hB hlive (by simp at hneed; omega) (by omega) hL).mono ?_
      intro inner ⟨ret,brk,qsI,⟨bufI,fwI⟩,cqI⟩
      have hscope : S.scope = sc := qs.scope
      have fits : S.scalars.memory.length ≤ inner.state.scalars.memory.length := by
        rw [qsI.memory,qs.memory]; simpa using m1
      have takeEq : inner.state.scalars.memory.take S.scalars.memory.length = r1.ps.mem.take ps.mem.length := by
        rw [qsI.memory,qs.memory]; simp
      have types : (inner.state.scalars.memory.take S.scalars.memory.length).map Cell.type =
          S.scalars.memory.map Cell.type := by
        rw [takeEq,qs.memory]; simpa using y1
      have notVec : ∀ owner element, inner.returned ≠ some (.vector owner element) := by
        intro owner element h
        rw [ret] at h
        cases hv : r1.ret <;> simp [hv] at h
      have leaveEq := leave_scalar S inner.state inner.returned notVec fits types fwI.valid
        (by rw [hscope]; exact fwI.fresh (by omega))
      refine ⟨S.left inner.state,leaveEq,ret,brk,?_,?_,?_⟩
      · refine ⟨?_,?_,?_,?_,?_⟩
        · rw [left_slots,qs.slots]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_memory,takeEq]; simp
        · rw [left_bindings,qs.bindings]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_baseMemory]; exact qs.base
        · rw [left_scope]; exact qs.scope
      · refine ⟨bufI, fwI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_⟩
        · rw [left_state]; rfl
        · rw [left_frameBindings,fwI.bindings,fw.bindings]; rfl
      · have lengthTake : (inner.state.scalars.memory.take S.scalars.memory.length).length =
            S.scalars.memory.length := by
          rw [takeEq,qs.memory]; simp; omega
        have hl : inner.state.frame.state.liveSpace-inner.state.frame.state.storage.baseSpace ≤ TPB := by
          rw [fwI.live]; omega
        have := Cb.left cq cqI lengthTake (by rw [live_psV qs]; omega) hl
        exact this
  | branch cnd y n ihy ihn =>
    intro hs fu ps vec r hr B sc SPB TPB W wk buf S qs fw cq hB hlive hneed hsc hL
    simp only [WrV,Bool.and_eq_true] at hs
    simp only [pexecW,Bind.bind,Option.bind] at hr
    have eS : (fx SPB TPB).SPB = SPB := rfl
    cases h1 : vdenL vc.ty vec (penv1 ps) cnd with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      obtain ⟨u,ev⟩ := ev_vdenL vc cnd S ps v qs rfl fw h1
      have good := Ev.good ev
      have hu := ev.1
      have self := release_self good.1.1
      have qsU : QS (u.charge 1 0) [] B sc ps.mem ps.bs (sl1 ps.bs.length) :=
        qs.core (good.1.trans (core_charge u 1 0))
      have fwU : FW vc vec buf wk (u.charge 1 0).frame := fw.of_eq (by simpa using good.1.1)
      have live := live_psV qs
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecW vc.ty fu n ps vec with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [z,if_pos rfl,self]
          refine (ihn hs.2 fu ps vec r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
      · simp only [z,if_false] at hr
        cases h2 : pexecW vc.ty fu y ps vec with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [if_neg z,self]
          refine (ihy hs.1 fu ps vec r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | whileLoop cnd b ih =>
    intro hs fu ps vec r hr B sc SPB TPB W wk buf S qs fw cq hB hlive hneed hsc hL
    simp only [WrV] at hs
    have eS : (fx SPB TPB).SPB = SPB := rfl
    refine RunsTo.whileGhost (fun g t => ∃ (ps1 : PS) (vec1 : List Int) (r1 : PRW) (k j : Nat) (buf1 : Buffer Value),
        pexecW vc.ty g (.whileLoop cnd b) ps1 vec1 = some r1 ∧
        r.ps = r1.ps ∧ r.vec = r1.vec ∧ r.ret = r1.ret ∧ r.cost = k + r1.cost ∧ r.wk = j + r1.wk ∧ r1.need ≤ r.need ∧
        QS t [] B sc ps1.mem ps1.bs (sl1 ps1.bs.length) ∧ FW vc vec1 buf1 (wk+j) t.frame ∧ Cq SPB TPB (W+k) t ∧
        B ≤ ps1.mem.length ∧ ps1.mem.length+ps1.bs.length ≤ SPB+B) _ ?_ fu fu S (Nat.le_refl _)
      ⟨ps,vec,r,0,0,buf,hr,rfl,rfl,rfl,by omega,by omega,Nat.le_refl _,qs,fw,cq,hB,hlive⟩
    intro g t ⟨ps1,vec1,r1,k,j,buf1,hr1,hrps,hrvec,hrret,hrcost,hrwk,hrneed,qs1,fw1,cq1,hB1,hsz⟩
    cases g with
    | zero => simp [pexecW] at hr1
    | succ g' =>
      simp only [pexecW,Bind.bind,Option.bind] at hr1
      cases h1 : vdenL vc.ty vec1 (penv1 ps1) cnd with
      | none => simp [h1] at hr1
      | some v =>
        simp only [h1] at hr1
        obtain ⟨u,ev⟩ := ev_vdenL vc cnd t ps1 v qs1 rfl fw1 h1
        have good := Ev.good ev
        have hu := ev.1
        have self := release_self good.1.1
        have qsU : QS (u.charge 1 0) [] B sc ps1.mem ps1.bs (sl1 ps1.bs.length) :=
          qs1.core (good.1.trans (core_charge u 1 0))
        have fwU : FW vc vec1 buf1 (wk+j) (u.charge 1 0).frame := fw1.of_eq (by simpa using good.1.1)
        have live := live_psV qs1
        refine ⟨u,v,hu,?_,?_⟩
        · intro z
          simp only [z,if_true] at hr1
          cases hr1
          rw [self]
          simp at hrneed hrps hrvec hrret hrcost hrwk
          have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq1.good good (by omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
          refine ⟨by rw [hrret]; rfl,rfl,?_,⟨buf1,?_⟩,?_⟩
          · rw [hrps]; exact qsU
          · rw [hrvec]
            exact fwU.wk_eq (by omega)
          · rw [hrcost]; exact cqC.mono (by omega)
        · intro z
          simp only [z,if_false] at hr1
          cases h2 : pexecW vc.ty (g'+1) b ps1 vec1 with
          | none => simp [h2] at hr1
          | some rb =>
            simp only [h2] at hr1
            cases hret : rb.ret with
            | some _ => simp [hret] at hr1
            | none =>
              simp only [hret] at hr1
              cases h3 : pexecW vc.ty g' (.whileLoop cnd b) rb.ps rb.vec with
              | none => simp [h3] at hr1
              | some r2 =>
                simp only [h3] at hr1
                cases hr1
                have ext := pexecW_ext vc w b hs (g'+1) ps1 vec1 rb h2
                have nd := pexecW_need vc w b hs (g'+1) ps1 vec1 rb h2
                simp at hrneed hrps hrvec hrret hrcost hrwk
                have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
                  have c1 := cq1.good good (by omega)
                  exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
                rw [self]
                refine (ih hs (g'+1) ps1 vec1 rb h2 (u.charge 1 0) qsU fwU cqC hB1 hsz (by omega) hsc hL).mono ?_
                intro inner ⟨ret,brk,qsI,⟨bufI,fwI⟩,cqI⟩
                refine ⟨by rw [ret,hret]; rfl,brk,g',Nat.lt_succ_self _,rb.ps,rb.vec,r2,k+(vwp cnd).1+1+rb.cost,j+rb.wk,bufI,h3,?_,?_,?_,?_,?_,?_,qsI,?_,?_,?_,?_⟩
                · exact hrps
                · exact hrvec
                · exact hrret
                · omega
                · omega
                · omega
                · exact fwI.wk_eq (by omega)
                · have : W+k+(vwp cnd).1+1+rb.cost = W+(k+(vwp cnd).1+1+rb.cost) := by omega
                  rw [this] at cqI; exact cqI
                · exact Nat.le_trans hB1 ext.2.2.1
                · omega
  | _ => intro hs; simp [WrV] at hs


end Proofs.VecWrite
