import Proofs.UfCopyFields
import Proofs.UfBalancedReceiver
import Proofs.UfTraceWork

namespace Proofs.UfCopyReceiver
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppNestedConstruct
open Proofs.CppFrameCopy Proofs.CppNestedCopy Proofs.CppFrameExtension
open Proofs.UfCopyFields Proofs.UfReceiverState Proofs.UfBalancedReceiver Proofs.UfFindCall
open Proofs.DoublingNested (i32)

def state (s : NState) (buf : Buffer Value) (count n : Int) : NState :=
  fields s (copiedFrame s.frame buf i32 s.scope true) count n

theorem context_bound (s : NState) (buf : Buffer Value)
    (valid : s.frame.state.wellFormed = true)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope) :
    ∀ owner c, (cloned s.frame.state buf i32 s.scope).forest.context owner = some c → c ≤ s.scope := by
  intro owner c found
  have inside := Proofs.UfConstructedReceiver.context_inside _ owner c found
  have grown := declareRoot_length s.frame.state.forest i32 s.scope
  have sf := (wellFormed_parts s.frame.state valid).1
  by_cases old : owner < s.frame.state.forest.objects.length
  · have kept := Proofs.CppConstructionRetire.context_prefix s.frame.state.forest
      (cloned s.frame.state buf i32 s.scope).forest s.frame.state.forest.objects.length
      (fun i h => declareRoot_old s.frame.state.forest i32 s.scope i h) owner old
    rw [kept] at found
    exact strict owner c found
  · have same : owner = s.frame.state.storage.objects.length := by
      change owner < (s.frame.state.forest.declareRoot i32 s.scope).objects.length at inside
      rw [grown] at inside
      omega
    have tag := declareRoot_new s.frame.state.forest i32 s.scope
    rw [sf] at tag
    change (cloned s.frame.state buf i32 s.scope).forest.lookup s.frame.state.storage.objects.length = some (flatTag i32 s.scope) at tag
    have root := Proofs.CppVectorOwnership.root_runs
      (cloned s.frame.state buf i32 s.scope).forest s.frame.state.storage.objects.length
      (flatTag i32 s.scope) tag rfl
    have context : (cloned s.frame.state buf i32 s.scope).forest.context
        s.frame.state.storage.objects.length = some s.scope := by
      simp [Forest.context,root,tag,flatTag]
    rw [same,context] at found
    cases found
    exact Nat.le_refl _

theorem new_ok (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Buffer Value) (cb nb : Proofs.CppState.Binding)
    (inv : Inv s layout ps count rank buf cb nb) :
    VOKWF (state s buf count ps.length) (layoutOf s).vectorSlot (layoutOf s).vectorBinding
      (layoutOf s).owner (layoutOf s).scope (Proofs.CppVectorCopy.copied buf s.frame.state.storage.objects.length) := by
  have extension := copied_frame_extends s.frame buf i32 s.scope true inv.ok.valid inv.ok.lengths
    (by decide +kernel) inv.bufferValid
  have sf := (wellFormed_parts s.frame.state inv.ok.valid).1
  refine ⟨extension.newValid,fields_vector s _ count ps.length,?_,?_,
    clone_storage_new s.frame.state buf i32 s.scope,extension.newLengths,?_,?_,?_⟩
  · simp [state,fields,NState.observe,copiedFrame,layoutOf,copyBinding]
  · have tag := declareRoot_new s.frame.state.forest i32 s.scope
    rw [sf] at tag
    exact tag
  · simp [state,fields,NState.observe,copiedFrame,layoutOf,inv.ok.lengths,sf]
  · exact context_bound s buf inv.ok.valid inv.ok.strict
  · have base := inv.ok.base
    simp only [state,fields,NState.observe,Proofs.CppState.State.observe,List.length_append,
      List.length_cons,List.length_nil]
    omega

theorem new_represents (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Buffer Value) (cb nb : Proofs.CppState.Binding)
    (inv : Inv s layout ps count rank buf cb nb) :
    Represents (state s buf count ps.length) (layoutOf s) ps count rank := by
  refine ⟨Proofs.CppVectorCopy.copied buf s.frame.state.storage.objects.length,
    ⟨s.scalars.memory.length,true⟩,⟨s.scalars.memory.length+1,true⟩,
    new_ok s layout ps count rank buf cb nb inv,?_,
    Proofs.CppVectorCopy.copied_valid buf _ _ inv.bufferValid,inv.limit,rfl,inv.math,?_,rfl,?_,by dsimp; omega⟩
  · exact inv.items
  · exact fields_count s _ count ps.length (scalar_valid s layout.countSlot i32 cb ⟨i32,count⟩ inv.countCell)
  · exact fields_n s _ count ps.length (scalar_valid s layout.nSlot i32 nb ⟨i32,ps.length⟩ inv.nCell)

theorem old_ok (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Buffer Value) (cb nb : Proofs.CppState.Binding)
    (inv : Inv s layout ps count rank buf cb nb) :
    VOKWF (state s buf count ps.length) layout.vectorSlot layout.vectorBinding layout.owner layout.scope buf := by
  have extension := copied_frame_extends s.frame buf i32 s.scope true inv.ok.valid inv.ok.lengths
    (by decide +kernel) inv.bufferValid
  have ownerBound := Proofs.CppVectorStore.lookup_bound s.frame.state.storage layout.owner buf inv.ok.vfound
  have sf := (wellFormed_parts s.frame.state inv.ok.valid).1
  have bindingBound := (List.getElem?_eq_some_iff.mp inv.ok.binding).1
  refine ⟨extension.newValid,fields_old_vector s _ count ps.length _ _ inv.ok.slot,?_,?_,?_,
    extension.newLengths,?_,?_,?_⟩
  · change (copiedFrame s.frame buf i32 s.scope true).bindings[layout.vectorBinding]? = _
    rw [extension.bindings layout.vectorBinding bindingBound]
    exact inv.ok.binding
  · change (copiedFrame s.frame buf i32 s.scope true).state.forest.lookup layout.owner = _
    rw [extension.forest layout.owner (by omega)]
    exact inv.ok.vtag
  · change (copiedFrame s.frame buf i32 s.scope true).state.storage.lookup layout.owner = _
    rw [extension.storage layout.owner ownerBound]
    exact inv.ok.vfound
  · change (copiedFrame s.frame buf i32 s.scope true).rootWritable[layout.owner]? = _
    rw [extension.flags layout.owner (by rw [inv.ok.lengths,sf]; exact ownerBound)]
    exact inv.ok.flag
  · exact context_bound s buf inv.ok.valid inv.ok.strict
  · have base := inv.ok.base
    simp only [state,fields,NState.observe,Proofs.CppState.State.observe,List.length_append,
      List.length_cons,List.length_nil]
    omega

theorem old_represents (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Buffer Value) (cb nb : Proofs.CppState.Binding)
    (inv : Inv s layout ps count rank buf cb nb) :
    Represents (state s buf count ps.length) layout ps count rank := by
  exact ⟨buf,cb,nb,old_ok s layout ps count rank buf cb nb inv,inv.items,inv.bufferValid,inv.limit,
    inv.owner,inv.math,fields_old_scalar s _ count ps.length _ _ cb _ inv.countCell,
    inv.writable,fields_old_scalar s _ count ps.length _ _ nb _ inv.nCell,inv.different⟩

theorem copy_strong (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (strong : Strong s layout ps count rank) :
    ∃ out, copyReceiver s layout = some (out,layoutOf s) ∧
      Strong out layout ps count rank ∧ Strong out (layoutOf s) ps count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := strong.1
  obtain ⟨resolved,_,_⟩ := Proofs.CppNestedRows.resolve_vroot s.frame layout.vectorBinding layout.owner layout.scope
    i32 true true buf inv.ok.binding inv.ok.valid inv.ok.vtag inv.ok.vfound inv.ok.lengths inv.ok.flag (fun _ => rfl)
  refine ⟨state s buf count ps.length,?_,⟨old_represents s layout ps count rank buf cb nb inv,strong.2⟩,
    ⟨new_represents s layout ps count rank buf cb nb inv,strong.2⟩⟩
  exact copy_receiver_runs s layout count ps.length cb nb _ buf inv.ok.slot inv.ok.lengths resolved
    inv.countCell inv.nCell

theorem actual_copy_strong (s out : NState) (layout nextLayout : Layout) (ps : List Int) (count : Int)
    (rank : Nat → Nat) (strong : Strong s layout ps count rank)
    (actual : copyReceiver s layout = some (out,nextLayout)) :
    nextLayout = layoutOf s ∧ Strong out layout ps count rank ∧ Strong out nextLayout ps count rank := by
  obtain ⟨expected,ran,old,new⟩ := copy_strong s layout ps count rank strong
  rw [actual] at ran
  obtain ⟨same,layoutSame⟩ := Prod.mk.inj (Option.some.inj ran)
  subst expected
  subst nextLayout
  exact ⟨rfl,old,new⟩

theorem state_cost (s : NState) (buf : Buffer Value) (count n : Int)
    (lengths : s.frame.state.forest.objects.length = s.frame.state.storage.objects.length) :
    (state s buf count n).work = s.work+buf.items.length+4 ∧
    (state s buf count n).frame.state.liveSpace = s.frame.state.liveSpace+buf.items.length+1 ∧
    (state s buf count n).scalars.memory.length = s.scalars.memory.length+2 ∧
    (state s buf count n).scalars.bindings.length = s.scalars.bindings.length+2 ∧
    (state s buf count n).scalars.baseMemory = s.scalars.baseMemory ∧
    (state s buf count n).frame.state.storage.peak =
      max s.frame.state.storage.peak (s.frame.state.liveSpace+buf.items.length+2-s.frame.state.storage.baseSpace) := by
  have cost := clone_cost s.frame.state buf i32 s.scope lengths
  refine ⟨?_,cost.2.1,?_,?_,rfl,cost.2.2⟩
  · simp [state,fields,NState.work,NState.observe,Proofs.CppState.State.observe,copiedFrame,cloned]
    omega
  · simp [state,fields,NState.observe,Proofs.CppState.State.observe]
  · simp [state,fields,NState.observe,Proofs.CppState.State.observe]

theorem copy_calls (ops : List Proofs.UfReceiverTrace.Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (strong : Strong s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ initial fuels out vec nextCount nextRank answers,
      copyReceiver s layout = some (initial,layoutOf s) ∧
      Strong initial layout ps count rank ∧
      Proofs.UfReceiverTrace.runCalls fuels ops initial (layoutOf s) = .finished (out,answers) ∧
      Strong out (layoutOf s) vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ps.length+4+ops.length*Proofs.UfTraceWork.budget ps.length := by
  obtain ⟨buf,cb,nb,inv⟩ := strong.1
  let initial := state s buf count ps.length
  have newStrong : Strong initial (layoutOf s) ps count rank :=
    ⟨new_represents s layout ps count rank buf cb nb inv,strong.2⟩
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,post,len,fl,al,work⟩ :=
    Proofs.UfTraceWork.calls_work ops initial (layoutOf s) ps count rank newStrong allowed
  obtain ⟨resolved,_,_⟩ := Proofs.CppNestedRows.resolve_vroot s.frame layout.vectorBinding layout.owner layout.scope
    i32 true true buf inv.ok.binding inv.ok.valid inv.ok.vtag inv.ok.vfound inv.ok.lengths inv.ok.flag (fun _ => rfl)
  have cost := (state_cost s buf count ps.length (wellFormed_parts s.frame.state inv.ok.valid).1).1
  have size : buf.items.length = ps.length := by rw [inv.items,List.length_map]
  rw [size] at cost
  refine ⟨initial,fuels,out,vec,nextCount,nextRank,answers,
    copy_receiver_runs s layout count ps.length cb nb _ buf inv.ok.slot inv.ok.lengths resolved inv.countCell inv.nCell,
    ⟨old_represents s layout ps count rank buf cb nb inv,strong.2⟩,ran,post,len,fl,al,?_⟩
  change out.work ≤ (state s buf count ps.length).work+_ at work
  rw [cost] at work
  exact work

end Proofs.UfCopyReceiver
