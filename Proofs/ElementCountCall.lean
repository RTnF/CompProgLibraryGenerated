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

end Proofs.ElementCountCall
