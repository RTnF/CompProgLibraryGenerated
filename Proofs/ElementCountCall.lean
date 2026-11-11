import Proofs.ElementCountExec
import Proofs.DoublingCall
import Proofs.DynamicTransfer
import Proofs.Generated.ElementCount

/-!
Call theorems of the original `element_count` (`library/array/element_count.hpp`) for the verified instances
`T = std::vector<long long>` and `T = std::vector<int>`.

The result `std::vector<std::pair<value_type, int>>` is modelled as a nested vector with two rows
(row 0 the values, row 1 the counts; see `verifier/nested_ir.py`). Both rows have the element type
(`long long` stores the `int` counts widened).
-/

namespace Proofs.ElementCountCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt Proofs.CppNestedHoare Proofs.CppNestedScope
open Proofs.CppNestedConstruct Proofs.CppNestedCall Proofs.CppNestedRows Proofs.CppNestedFacts
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicContents
open Proofs.RunLengthMath Proofs.ElementCountExec
open Proofs.CppState (Cell)
open Proofs.CppMixedInvoke (Location)

/-- What the caller provides: a bound root vector `v` of element type `ty`. -/
structure CallerOK (caller : NState) (ty : Ty) (vslot vb V vsc : Nat) (wV m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  perm : wV = true → m = true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

def vbind (ty : Ty) (V vsc : Nat) : Binding := ⟨V,.integer ty,false,.root vsc⟩

theorem resolve_vec (caller : NState) {ty : Ty} {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller ty vslot vb V vsc wV m vbuf) :
    resolve caller (.vector ty false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc ty false) := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc ty wV m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag ok.perm
  simp [resolve,ok.slot,ok.binding,resolved]

theorem bindRoot_v (state : Proofs.CppNestedVectorStore.State) (rw : List Bool) {ty : Ty} {V vsc : Nat} {m : Bool}
    {vbuf : Buffer Value} (valid : state.wellFormed = true)
    (vtag : state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : state.storage.lookup V = some vbuf) (lengths : rw.length = state.forest.objects.length)
    (flag : rw[V]? = some m) :
    (⟨state,rw,[]⟩ : Frame).bindRoot V (.integer ty) vsc false = some (⟨state,rw,[vbind ty V vsc]⟩,0) := by
  have vobject : (⟨state,rw,[]⟩ : Frame).object V (.integer ty) = some (vbuf,⟨.integer ty,none,some vsc,[]⟩) :=
    object_runs _ V _ vbuf _ valid vfound vtag rfl
  have vrooted : state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ vtag rfl
  have vmax : (⟨state,rw,[]⟩ : Frame).maximum V = some m := maximum_runs _ V V m lengths vrooted flag
  simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
  simp [Frame.addBinding,vbind]

theorem prepare_one (caller : NState) {ty : Ty} {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller ty vslot vb V vsc wV m vbuf) :
    ∃ Sinit, prepare caller [.vector ty false] [.vectorReference vslot] = some Sinit ∧
      Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = Proofs.DoublingCall.callerP caller ∧
      Sinit.scalars.bindings = [] ∧ Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧
      Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[vbind ty V vsc]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak ∧
      caller.peak ≤ Sinit.peak := by
  have rvec := resolve_vec caller ok
  have bound := bindRoot_v caller.frame.state caller.frame.rootWritable ok.valid ok.vtag ok.vfound ok.lengths ok.flag
  simp [prepare,ok.valid,resolveAll,rvec,bindAll,bindOne,bound,Proofs.DoublingCall.callerP,
    NState.observe,CppState.State.observe,vbind,NState.release,NState.charge]
  exact ⟨Nat.le_max_left _ _,Nat.le_max_left _ _⟩

/-! ## Returning `ret` to the caller -/

/-- The rows of the result. -/
def resultView (ty : Ty) (scope R : Nat) (X : List Int) : View :=
  .rows ty scope (rowIds R 2) 0 [firsts (rle X),seconds (rle X)]

def finished (caller D : NState) (ty : Ty) (sc R : Nat) (X : List Int) : NState :=
  let moved := DynamicTransfer.movedFrame D.frame R caller.scope (resultView ty sc R X)
  let scalars : CppState.State := {caller.scalars with
    memory := D.scalars.memory.take caller.scalars.memory.length,
    work := D.scalars.work+1,peak := max caller.scalars.peak D.scalars.peak}
  let frame : Frame := {noopRetired moved with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak D.peak⟩ : NState).observe

theorem construct_run (s : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope : Nat) (valid : s.wellFormed = true)
    (supported : CppVectorBindings.supported ty) :
    ∃ next, s.constructRows ty scope 2 = some next ∧ next.forest = s.forest.constructRows ty scope 2 := by
  have h : s.constructRows ty scope 2 ≠ none := by
    simp [Proofs.CppNestedVectorStore.State.constructRows,valid,supported,rowLimit_two]
  obtain ⟨next,hn⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨next,hn,constructRows_forest s ty scope 2 next hn⟩

theorem finish_ok (F : Fix) (ok : FixOK F) (caller D : NState) (W : Nat)
    (final : Final F W ⟨D,some (.vector F.R (.vector (.integer F.ty))),false⟩)
    (hP : F.P = Proofs.DoublingCall.callerP caller) (hsc : F.sc = caller.scope+1)
    (hforest : F.forest = caller.frame.state.forest.constructRows F.ty F.sc 2)
    (hR : F.R = caller.frame.state.storage.objects.length) (valid : caller.frame.state.wellFormed = true)
    (strict : ∀ o c, caller.frame.state.forest.context o = some c → c ≤ caller.scope) :
    finish caller D (.vector (.vector (.integer F.ty))) (some (.vector F.R (.vector (.integer F.ty)))) =
      some (finished caller D F.ty F.sc F.R F.X,.vector F.R (.vector (.integer F.ty))) ∧
      Models (finished caller D F.ty F.sc F.R F.X).frame.state F.R (resultView F.ty caller.scope F.R F.X) ∧
      (∀ o, (finished caller D F.ty F.sc F.R F.X).frame.state.storage.lookup o = D.frame.state.storage.lookup o) := by
  obtain ⟨_,_,st,cb,scope,⟨cells,memory,_⟩,_,_,_⟩ := final
  simp only [] at st cb scope memory
  have lookup : F.heap (rle F.X) F.R = some (resultView F.ty F.sc F.R F.X) := by
    simp [Fix.heap,heapOf,put,resultView]
  have model := st.family.models F.R _ lookup
  have ran := DynamicTransfer.frame_runs D.frame F.R caller.scope _ model
  simp only [resultView,View.element,View.scope] at ran
  have tag := DynamicTransfer.Models.tag model
  obtain ⟨next,constructed,nextForest⟩ := construct_run caller.frame.state F.ty F.sc valid ok.supported
  have lengths := (Proofs.CppNestedVectorStore.wellFormed_parts caller.frame.state valid).1
  have fresh : ∀ owner, (DynamicTransfer.movedFrame D.frame F.R caller.scope (resultView F.ty F.sc F.R F.X)).state.forest.context owner ≠
      some F.sc := by
    intro owner bad
    simp only [DynamicTransfer.movedFrame] at bad
    rw [context_transferred _ F.R caller.scope _ tag (by simp [resultView,DynamicTransfer.tagOf,CppRowsGraph.tag]) owner]
      at bad
    have dF : D.frame.state.forest = next.forest := by rw [st.forest,hforest,nextForest]
    rw [dF] at bad
    by_cases tree : next.forest.rootOwner owner = some F.R
    · simp [tree] at bad; omega
    · simp only [tree,if_false] at bad
      rcases Proofs.DoublingPrologue.construct_ctx _ next F.ty F.sc 2 constructed owner F.sc bad with old | ⟨root,_⟩
      · have := strict owner _ old; omega
      · apply tree
        rw [root,lengths,hR]
  have movedModel := DynamicTransfer.Models.moved model caller.scope
  have movedValid : (DynamicTransfer.movedFrame D.frame F.R caller.scope (resultView F.ty F.sc F.R F.X)).state.wellFormed = true :=
    movedModel.valid
  have retire := retireScope_fresh _ F.sc movedValid fresh
  have take : D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [memory,hP]; simp only [Proofs.DoublingCall.callerP,List.append_assoc]; exact List.take_left
  have fits : caller.scalars.memory.length ≤ D.scalars.memory.length := by
    rw [memory,hP]; simp [Proofs.DoublingCall.callerP]
  have same := Proofs.DoublingNested.noopRetired_same
    (DynamicTransfer.movedFrame D.frame F.R caller.scope (resultView F.ty F.sc F.R F.X))
  refine ⟨?_,?_,?_⟩
  · simp only [resultView] at retire
    unfold finish
    rw [if_pos ⟨fits,by rw [take]⟩]
    simp only [ite_true,scope,← hsc,ran,Bind.bind,Option.bind,retire]
    rfl
  · exact MultiVecDynamicScope.Models.same_objects same _ _ movedModel
  · intro o
    exact same.lookup o

theorem moved_live (f : Frame) (R scope : Nat) (tag : Tag) (found : f.state.forest.lookup R = some tag) :
    ({f.state with forest := f.state.forest.transferred R scope tag} : Proofs.CppNestedVectorStore.State).liveSpace =
      f.state.liveSpace := by
  unfold Proofs.CppNestedVectorStore.State.liveSpace
  congr 1
  apply List.map_congr_left
  intro o _
  simp only [Proofs.CppNestedVectorStore.State.nodeSpace]
  by_cases same : o = R
  · subst same
    rw [transferred_lookup_root f.state.forest o scope tag found,found]
    cases f.state.storage.lookup o <;> rfl
  · rw [transferred_lookup_other f.state.forest R o scope tag same]

theorem tp_bound (tp live base Lc c0 c1 k n TPB : Nat) (h1 : tp ≤ TPB) (h2 : live = Lc+c0+c1)
    (h3 : c0 ≤ 2*k+1) (h4 : c1 ≤ 2*k+1) (h5 : k ≤ n) (h6 : Lc+8*n+10-base ≤ TPB) : max tp (live-base) ≤ TPB := by
  omega

theorem sp_bound (a b c memLen base binds frameBinds SPB : Nat) (ha : a ≤ c) (hc : c ≤ SPB) (hb : b ≤ SPB)
    (hs : memLen+(binds+frameBinds)+8-base+40 ≤ SPB) (hbase : base ≤ memLen) :
    max (max a b) (memLen-base+binds+0) ≤ SPB := by omega

theorem peak_bound (cp dp sp tp SPB TPB : Nat) (hd : dp ≤ SPB+TPB) (hs : sp ≤ SPB) (ht : tp ≤ TPB) :
    max (max cp dp) (sp+tp) ≤ max cp (SPB+TPB) := by omega

/-! ## The call -/

def heap0 (ty : Ty) (V vsc : Nat) (X : List Int) : Heap := fun o => if o = V then some (.flat ty vsc X) else none

def mkFix (caller Sinit : NState) (ty : Ty) (cv : NExpr) (X : List Int) (V vsc : Nat) (m : Bool) (vbuf : Buffer Value) :
    Fix where
  ty := ty
  cv := cv
  X := X
  P := Proofs.DoublingCall.callerP caller
  B := caller.scalars.baseMemory
  V := V
  vsc := vsc
  mV := m
  sc := caller.scope+1
  R := caller.frame.state.storage.objects.length
  h0 := heap0 ty V vsc X
  Lc := caller.frame.state.liveSpace+3
  Tc := caller.frame.state.storage.work+3
  base := caller.frame.state.storage.baseSpace
  SPB := max (max Sinit.scalars.peak Sinit.peak)
    ((Proofs.DoublingCall.callerP caller).length+8-caller.scalars.baseMemory+40)
  TPB := max (max caller.frame.state.storage.peak
      (caller.frame.state.liveSpace+4-caller.frame.state.storage.baseSpace))
    (caller.frame.state.liveSpace+3+8*X.length+10-caller.frame.state.storage.baseSpace)
  forest := caller.frame.state.forest.constructRows ty (caller.scope+1) 2
  vbuf := vbuf

/-- What the call guarantees: `ret`'s two rows are the values and the counts of the maximal runs of `v`,
`v` is untouched, the caller's scalars and bindings are restored, and the work and the space are linear. -/
structure Post (caller Sinit res : NState) (ty : Ty) (X : List Int) (V : Nat) (vbuf : Buffer Value) : Prop where
  result : Models res.frame.state caller.frame.state.storage.objects.length
    (resultView ty caller.scope caller.frame.state.storage.objects.length X)
  input : res.frame.state.storage.lookup V = some vbuf
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  scalarWork : res.scalars.work ≤ caller.scalars.work+90*X.length+74
  storageWork : res.frame.state.storage.work ≤ caller.frame.state.storage.work+10*X.length+3
  storagePeak : res.frame.state.storage.peak ≤ max (max caller.frame.state.storage.peak
      (caller.frame.state.liveSpace+4-caller.frame.state.storage.baseSpace))
    (caller.frame.state.liveSpace+3+8*X.length+10-caller.frame.state.storage.baseSpace)
  peak : res.peak ≤ max caller.peak ((max (max Sinit.scalars.peak Sinit.peak)
      ((Proofs.DoublingCall.callerP caller).length+8-caller.scalars.baseMemory+40)) +
    (max (max caller.frame.state.storage.peak
      (caller.frame.state.liveSpace+4-caller.frame.state.storage.baseSpace))
    (caller.frame.state.liveSpace+3+8*X.length+10-caller.frame.state.storage.baseSpace)))

theorem call_correct (prog : NProgram) (ty : Ty) (cv : NExpr)
    (hparams : prog.parameters = [.vector ty false]) (hres : prog.result = .vector (.vector (.integer ty)))
    (hbody : prog.body = body ty cv)
    (counts : ∀ c : Int, ti.valid c = true → ty.valid c = true) (supported : CppVectorBindings.supported ty)
    (cvScalar : cv.scalarOnly = true)
    (cvValue : ∀ (env : Nat → Ty → Option Int) (c : Int), env 4 ti = some c → ti.valid c = true → cv.denote env = some c)
    (cvNodes : cv.nodes ≤ 2) (room : 2147483648 ≤ CppVectorBindings.sizeLimit ty)
    (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller ty vslot vb V vsc wV m vbuf) (X : List Int) (hv : vbuf.items = X.map Value.integer)
    (hX : ∀ x ∈ X, ty.valid x = true) (hn : X.length < 2147483647) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.vectorReference vslot] = some Sinit ∧
      prog.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.vector caller.frame.state.storage.objects.length (.vector (.integer ty))) ∧
      Post caller Sinit res ty X V vbuf := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sOuter⟩ := prepare_one caller ok
  let F := mkFix caller Sinit ty cv X V vsc m vbuf
  have bound : V < caller.frame.state.storage.objects.length := CppVectorStore.lookup_bound _ V vbuf ok.vfound
  have fok : FixOK F := by
    refine ⟨by simp [F,mkFix,heap0],bound,hn,hX,counts,supported,cvScalar,cvValue,cvNodes,room,?_,
      Nat.le_max_right _ _,Nat.le_max_right _ _,?_⟩
    · show caller.scalars.baseMemory ≤ (Proofs.DoublingCall.callerP caller).length
      have := ok.base; simp [Proofs.DoublingCall.callerP]; omega
    · intro o c h
      obtain ⟨next,constructed,nextForest⟩ := construct_run caller.frame.state ty (caller.scope+1) ok.valid supported
      show c ≤ caller.scope+1
      have h' : next.forest.context o = some c := by rw [nextForest]; exact h
      rcases Proofs.DoublingPrologue.construct_ctx _ next ty (caller.scope+1) 2 constructed o c h' with old | ⟨_,eq⟩
      · have := ok.strict o c old; omega
      · omega
  have sh0 : Sh Sinit F.P F.B [.vector 0] [] [] F.sc :=
    ⟨sSlots,by rw [sMem]; simp [F,mkFix],sBind,sBase,sScope⟩
  have fam0 : Family [pv F.ty F.V F.vsc F.mV] F.h0 Sinit.frame (resources Sinit.frame) := by
    rw [sFrame]
    refine ⟨ok.valid,?_,ok.lengths,?_,?_,?_,?_,measured_resources _⟩
    · intro o v h
      by_cases e : o = V
      · subst e
        simp [F,mkFix,heap0] at h
        subst h
        exact ⟨ok.valid,ok.vtag,vbuf,ok.vfound,hv⟩
      · simp [F,mkFix,heap0,e] at h
    · intro p hp; simp at hp; subst hp; simp [pv,vbind,Parameter.binding,F,mkFix]
    · intro p hp; simp at hp; subst hp; simpa [pv,F,mkFix] using ok.flag
    · intro p hp; simp at hp; subst hp; simp [pv]
    · intro p hp; simp at hp; subst hp
      exact ⟨.flat ty vsc X,by simp [F,mkFix,heap0,pv],rfl,rfl⟩
  have cb0 : Cb F Sinit :=
    ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_add_right _ _)⟩
  have run := body_run F fok Sinit sh0 fam0 (by rw [sFrame]; rfl)
    (by intro o c h; rw [sFrame] at h; have := ok.strict o c h; show c < caller.scope+1; omega)
    (by rw [sFrame]; rfl) (by rw [sFrame]; rfl) (by rw [sFrame]; rfl) (by rw [sFrame]; rfl) (by rw [sFrame]; rfl)
    (by rw [sFrame]; exact ok.vfound)
    (by rw [sFrame]; exact Nat.le_max_left _ _) cb0
  obtain ⟨fuel,step,hrun,ret,brk,st,cb,stScope,⟨cells,memory,cellsLen⟩,bindLen,stBase,stWork⟩ := run
  have stepEq : step = ⟨step.state,some (.vector F.R (.vector (.integer F.ty))),false⟩ := by
    cases step; simp_all
  have final : Final F (Sinit.scalars.work+90*F.X.length+70)
      ⟨step.state,some (.vector F.R (.vector (.integer F.ty))),false⟩ :=
    ⟨rfl,rfl,st,cb,stScope,⟨cells,memory,cellsLen⟩,bindLen,stBase,stWork⟩
  obtain ⟨fin,model,lookups⟩ := finish_ok F fok caller step.state _ final rfl rfl rfl rfl ok.valid ok.strict
  refine ⟨Sinit,fuel,finished caller step.state F.ty F.sc F.R F.X,by rw [hparams]; exact hprep,?_,?_⟩
  · unfold NProgram.callFuel
    rw [hparams,hprep]
    simp only [Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind,Bind.bind]
    have hrun' : runFuel fuel (body ty cv) Sinit = .finished step := hrun
    rw [hbody,hrun',stepEq]
    simp only [Bool.false_eq_true,if_false,hres]
    have fin' : finish caller step.state (ResultKind.vector (Element.integer ty).vector)
        (some (Ret.vector F.R (Element.integer F.ty).vector)) =
        some (finished caller step.state F.ty F.sc F.R F.X,.vector F.R (.vector (.integer F.ty))) := fin
    rw [fin']
    rfl
  · obtain ⟨b0,b1,f0,f1,i0,i1,c0,c1,l0,l1,lv,wk⟩ := st.bufs
    have stP := st.storagePeak
    have lenR := rle_length_le F.X
    have take : step.state.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [memory]; simp only [F,mkFix,Proofs.DoublingCall.callerP,List.append_assoc]; exact List.take_left
    have lookupR : step.state.frame.state.forest.lookup F.R = some (DynamicTransfer.tagOf (resultView F.ty F.sc F.R F.X)) :=
      DynamicTransfer.Models.tag (st.family.models F.R _ (by simp [Fix.heap,heapOf,put,resultView]))
    have liveEq : (DynamicTransfer.movedFrame step.state.frame F.R caller.scope
        (resultView F.ty F.sc F.R F.X)).state.liveSpace = step.state.frame.state.liveSpace :=
      moved_live step.state.frame F.R caller.scope _ lookupR
    have hLc : F.Lc = caller.frame.state.liveSpace+3 := rfl
    have hTc : F.Tc = caller.frame.state.storage.work+3 := rfl
    have hbase : F.base = caller.frame.state.storage.baseSpace := rfl
    have stBaseT := st.base
    have spb : F.SPB = max (max Sinit.scalars.peak Sinit.peak)
      ((Proofs.DoublingCall.callerP caller).length+8-caller.scalars.baseMemory+40) := rfl
    have tpb : F.TPB = max (max caller.frame.state.storage.peak
        (caller.frame.state.liveSpace+4-caller.frame.state.storage.baseSpace))
      (caller.frame.state.liveSpace+3+8*X.length+10-caller.frame.state.storage.baseSpace) := rfl
    have lenX : F.X = X := rfl
    have hV : F.V = V := rfl
    have hvb : F.vbuf = vbuf := rfl
    have hR : F.R = caller.frame.state.storage.objects.length := rfl
    have hP : F.P = Proofs.DoublingCall.callerP caller := rfl
    have hB : F.B = caller.scalars.baseMemory := rfl
    have hsc : F.sc = caller.scope+1 := rfl
    have hty : F.ty = ty := rfl
    have tpbOK := fok.tpb
    clear_value F
    subst lenX hV hvb hty
    have cbS := cb.scalarPeak
    have cbP := cb.peak
    have resSp : (finished caller step.state F.ty F.sc F.R F.X).scalars.peak =
        max (max caller.scalars.peak step.state.scalars.peak)
          ((step.state.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
    have resTp : (finished caller step.state F.ty F.sc F.R F.X).frame.state.storage.peak =
        max step.state.frame.state.storage.peak
          ((DynamicTransfer.movedFrame step.state.frame F.R caller.scope (resultView F.ty F.sc F.R F.X)).state.liveSpace-
            step.state.frame.state.storage.baseSpace) := rfl
    have resPeak : (finished caller step.state F.ty F.sc F.R F.X).peak =
        max (max caller.peak step.state.peak)
          ((finished caller step.state F.ty F.sc F.R F.X).scalars.peak+
            (finished caller step.state F.ty F.sc F.R F.X).frame.state.storage.peak) := rfl
    have lenP : (Proofs.DoublingCall.callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [Proofs.DoublingCall.callerP]
    have slotsRes : (finished caller step.state F.ty F.sc F.R F.X).slots = caller.slots := rfl
    have scopeRes : (finished caller step.state F.ty F.sc F.R F.X).scope = caller.scope := rfl
    have bindRes : (finished caller step.state F.ty F.sc F.R F.X).frame.bindings = caller.frame.bindings := rfl
    have memRes : (finished caller step.state F.ty F.sc F.R F.X).scalars.memory = caller.scalars.memory := take
    have workRes : (finished caller step.state F.ty F.sc F.R F.X).scalars.work = step.state.scalars.work+1 := rfl
    have storeRes : (finished caller step.state F.ty F.sc F.R F.X).frame.state.storage.work =
        step.state.frame.state.storage.work := rfl
    have takeLen : (step.state.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      rw [take]
    rw [takeLen] at resSp
    rw [liveEq] at resTp
    generalize finished caller step.state F.ty F.sc F.R F.X = res at *
    have tpRes : res.frame.state.storage.peak ≤ F.TPB := by
      rw [resTp,lv,stBaseT]
      exact tp_bound _ _ _ _ _ _ (rle F.X).length F.X.length _ stP rfl c0 c1 lenR tpbOK
    have spRes : res.scalars.peak ≤ F.SPB := by
      rw [resSp]
      refine sp_bound _ _ _ _ _ _ caller.frame.bindings.length _ sPeak (by rw [spb]; exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        cbS ?_ ok.base
      rw [← lenP,spb]; exact Nat.le_max_right _ _
    rw [hR] at model
    refine ⟨model,?_,slotsRes,scopeRes,bindRes,memRes,?_,?_,?_,?_⟩
    · exact (lookups F.V).trans st.input
    · rw [workRes]; rw [sWork] at stWork
      have : step.state.scalars.work+1 ≤ caller.scalars.work+3+90*F.X.length+70+1 := Nat.add_le_add_right stWork 1
      exact Nat.le_trans this (by omega)
    · rw [storeRes]
      have := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) wk)
      have l10 : 10*(rle F.X).length ≤ 10*F.X.length := Nat.mul_le_mul_left 10 lenR
      exact Nat.le_trans this (by rw [hTc]; omega)
    · rw [← tpb]; exact tpRes
    · rw [resPeak,← spb,← tpb]
      have : caller.peak ≤ caller.peak := Nat.le_refl _
      omega

/-! ## The verified instances -/

abbrev s64 : Ty := ⟨64,true,false⟩

theorem sizeLimit_s64 : 2147483648 ≤ CppVectorBindings.sizeLimit s64 := by
  have : CppVectorBindings.sizeLimit s64 = 1152921504606846975 := by simp [CppVectorBindings.sizeLimit]
  omega

theorem sizeLimit_i32 : 2147483648 ≤ CppVectorBindings.sizeLimit ti := by
  have : CppVectorBindings.sizeLimit ti = 2305843009213693951 := by simp [CppVectorBindings.sizeLimit]
  omega

theorem i32_in_s64 (c : Int) (h : ti.valid c = true) : s64.valid c = true := by
  simp [Ty.valid] at h ⊢; omega

theorem body_ll : Proofs.ElementCountInstance.element_count_std_vector_long_long.body =
    body s64 (.cast s64 (.variable ti 4)) := rfl

theorem body_int : Proofs.ElementCountInstance.element_count_std_vector_int.body = body ti (.variable ti 4) := rfl

/-- `cp::element_count(v)` for `v : std::vector<long long>`: the result's row 0 is the value and row 1 the
length of each maximal run of equal elements of `v`, in order (`rle`); the runs decode to `v`, have positive
lengths and adjacent runs differ. `v` is unchanged; time and extra space are linear in `v.size()`. -/
theorem element_count_ll_correct (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller s64 vslot vb V vsc wV m vbuf) (X : List Int) (hv : vbuf.items = X.map Value.integer)
    (hX : ∀ x ∈ X, s64.valid x = true) (hn : X.length < 2147483647) :
    ∃ Sinit fuel res,
      prepare caller Proofs.ElementCountInstance.element_count_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.ElementCountInstance.element_count_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.vector caller.frame.state.storage.objects.length (.vector (.integer s64))) ∧
      Post caller Sinit res s64 X V vbuf ∧
      rleFlat (rle X) = X ∧ (∀ p ∈ rle X, 0 < p.2) ∧ AdjOK (rle X) := by
  obtain ⟨Sinit,fuel,res,hprep,hrun,post⟩ := call_correct _ s64 (.cast s64 (.variable ti 4)) rfl rfl body_ll
    i32_in_s64 (by simp [CppVectorBindings.supported]) (by simp [NExpr.scalarOnly])
    (by intro env c h valid; simp [NExpr.denote,h,Ty.convert_of_valid _ _ (i32_in_s64 c valid)])
    (by simp [NExpr.nodes]) sizeLimit_s64 caller ok X hv hX hn
  exact ⟨Sinit,fuel,res,hprep,hrun,post,rle_spec X⟩

/-- `cp::element_count(v)` for `v : std::vector<int>`, with the same guarantees. -/
theorem element_count_int_correct (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller ti vslot vb V vsc wV m vbuf) (X : List Int) (hv : vbuf.items = X.map Value.integer)
    (hX : ∀ x ∈ X, ti.valid x = true) (hn : X.length < 2147483647) :
    ∃ Sinit fuel res,
      prepare caller Proofs.ElementCountInstance.element_count_std_vector_int.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.ElementCountInstance.element_count_std_vector_int.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.vector caller.frame.state.storage.objects.length (.vector (.integer ti))) ∧
      Post caller Sinit res ti X V vbuf ∧
      rleFlat (rle X) = X ∧ (∀ p ∈ rle X, 0 < p.2) ∧ AdjOK (rle X) := by
  obtain ⟨Sinit,fuel,res,hprep,hrun,post⟩ := call_correct _ ti (.variable ti 4) rfl rfl body_int
    (fun _ h => h) (by simp [CppVectorBindings.supported]) (by simp [NExpr.scalarOnly])
    (by intro env c h _; simp [NExpr.denote,h])
    (by simp [NExpr.nodes]) sizeLimit_i32 caller ok X hv hX hn
  exact ⟨Sinit,fuel,res,hprep,hrun,post,rle_spec X⟩

end Proofs.ElementCountCall
