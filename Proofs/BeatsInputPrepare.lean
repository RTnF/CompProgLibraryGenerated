import Proofs.BeatsInlineExec
import Proofs.DynamicPrepare

namespace Proofs.BeatsInputPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppVectorOwnership
open Proofs.MultiVecDynamic Proofs.CppRootModel Proofs.DynamicExpr Proofs.DynamicContents
open Proofs.BeatsAllocation Proofs.BeatsInlineFrame Proofs.IntSim Proofs.BeatsPrepare
open Proofs.CppRowsFrame

def parameters : List Proofs.CppVectorBindings.Parameter := [.vector s64 false]
def argument (owner scope : Nat) (maximum : Bool) : Parameter := ⟨0,owner,.integer s64,scope,false,maximum⟩

def prepared (caller : NState) (owner scope : Nat) : NState :=
  bstep (fun _ => s64) (fun _ => owner) (fun _ => scope) (fun _ => false)
    (Proofs.DynamicPrepare.initial caller (caller.charge 1 1) parameters) 0

theorem layout (caller : NState) (owner scope : Nat) :
    (prepared caller owner scope).frame.state = caller.frame.state ∧
    (prepared caller owner scope).frame.rootWritable = caller.frame.rootWritable ∧
    (prepared caller owner scope).frame.bindings = [⟨owner,.integer s64,false,.root scope⟩] ∧
    (prepared caller owner scope).slots = [.vector 0] ∧
    (prepared caller owner scope).scalars.bindings = [] ∧
    (prepared caller owner scope).scalars.baseMemory = caller.scalars.baseMemory ∧
    (prepared caller owner scope).scalars.memory = Proofs.DoublingCall.callerP caller ∧
    (prepared caller owner scope).scope = caller.scope+1 := by
  simp [prepared,bstep,Proofs.DynamicPrepare.initial,Frame.addBinding,NState.release,NState.charge,
    NState.observe,Proofs.CppState.State.observe,Proofs.DoublingCall.callerP]

theorem prepare_actual (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf) :
    prepare caller parameters [.vectorReference slot] = some (prepared caller owner scope) := by
  have resolved := Proofs.MatMulPrepare.resolve_vref caller s64 false ok.slot ok.binding ok.valid ok.vtag
    ok.vfound ok.lengths ok.flag ok.perm (fun wrong => False.elim (Bool.noConfusion wrong))
  have all : resolveAll caller parameters [.vectorReference slot] =
      some (caller.charge 1 1,[.vector owner scope s64 false]) := by
    simp only [parameters,resolveAll,resolved,Bind.bind,Option.bind_some]
  rw [Proofs.DynamicPrepare.prepare_eq caller (caller.charge 1 1) parameters [.vectorReference slot]
    [.vector owner scope s64 false] ok.valid all]
  let start := Proofs.DynamicPrepare.initial caller (caller.charge 1 1) parameters
  have bound := Proofs.MatMulPrepare.bindRoot_g start.frame (V := owner) (vsc := scope) (m := maximum)
    (vbuf := buf) s64 false ok.valid ok.vtag ok.vfound ok.lengths ok.flag
    (fun wrong => False.elim (Bool.noConfusion wrong))
  dsimp only [start] at bound
  simp only [bindAll,bindOne,bound,Bind.bind,Option.bind_some]
  rfl

def heap (owner scope : Nat) (a : List Int) : Heap :=
  fun i => if i = owner then some (.flat s64 scope a) else none

def logical (caller : NState) (owner scope : Nat) (maximum : Bool) (a : List Int) : Proofs.DynamicOwnedState.State :=
  ⟨⟨snapshot (prepared caller owner scope),eraseHeap (heap owner scope a)⟩,
    [argument owner scope maximum],caller.frame.state.storage.objects.length,1,caller.scope+1⟩

theorem prepared_family (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer) :
    Family [argument owner scope maximum] (heap owner scope a) (prepared caller owner scope).frame
      (resources (prepared caller owner scope).frame) := by
  obtain ⟨state,flags,bindings,_,_,_,_,_⟩ := layout caller owner scope
  have model : Flat (prepared caller owner scope).frame.state owner s64 scope a :=
    ⟨by rw [state]; exact ok.valid,by rw [state]; exact ok.vtag,buf,by rw [state]; exact ok.vfound,items⟩
  refine ⟨model.valid,?_,?_,?_,?_,?_,?_,measured_resources _⟩
  · intro root view found
    by_cases same : root = owner
    · subst root
      simp only [heap,ite_true,Option.some.injEq] at found
      subst view
      exact model
    · simp only [heap,ite_eq_right same] at found
      contradiction
  · rw [flags,state]
    exact ok.lengths
  · intro p member
    have same := List.mem_singleton.mp member
    subst p
    simp only [argument,Parameter.binding,bindings,List.getElem?_cons_zero]
  · intro p member
    have same := List.mem_singleton.mp member
    subst p
    exact (congrArg (fun xs => xs[owner]?) flags).trans ok.flag
  · intro p member impossible
    have same := List.mem_singleton.mp member
    subst p
    exact False.elim (Bool.noConfusion impossible)
  · intro p member
    have same := List.mem_singleton.mp member
    subst p
    exact ⟨.flat s64 scope a,by simp only [heap,argument,ite_true],rfl,rfl⟩

theorem prepared_real (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer) :
    Proofs.DynamicOwnedState.Realizes (logical caller owner scope maximum a) (prepared caller owner scope) := by
  have shape := layout caller owner scope
  exact ⟨⟨rfl,heap owner scope a,resources _,prepared_family caller slot vb owner scope wb maximum buf a ok items,rfl⟩,
    congrArg (fun state => state.storage.objects.length) shape.1,by rw [shape.2.2.1]; rfl,shape.2.2.2.2.2.2.2⟩

theorem prepared_input (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (_items : buf.items = a.map Value.integer) :
    Input (logical caller owner scope maximum a) (argument owner scope maximum) a := by
  refine ⟨?_,rfl,?_,?_,rfl⟩
  · exact (congrArg (fun xs => xs[0]?) (layout caller owner scope).2.2.2.1)
  · simp only [logical,argument,eraseHeap,heap,ite_true,Option.map_some,erase]
  · exact Proofs.CppVectorStore.lookup_bound caller.frame.state.storage owner buf ok.vfound

theorem prepared_entry (caller : NState) (owner scope : Nat) (maximum : Bool) (a : List Int) :
    Entry (logical caller owner scope maximum a) (argument owner scope maximum) := by
  have shape := layout caller owner scope
  exact ⟨rfl,rfl,by change (prepared caller owner scope).slots.length = 1; rw [shape.2.2.2.1]; rfl,shape.2.2.2.2.1⟩

theorem prepared_strict (caller : NState) (owner scope : Nat)
    (strict : ∀ root c, caller.frame.state.forest.context root = some c → c ≤ caller.scope) :
    ∀ root c, (prepared caller owner scope).frame.state.forest.context root = some c →
      c ≤ (prepared caller owner scope).scope := by
  obtain ⟨state,_,_,_,_,_,_,scopeEq⟩ := layout caller owner scope
  intro root c found
  rw [state] at found
  rw [scopeEq]
  have bound := strict root c found
  omega

theorem prepared_base (caller : NState) (owner scope : Nat)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    (prepared caller owner scope).scalars.baseMemory ≤ (prepared caller owner scope).scalars.memory.length := by
  obtain ⟨_,_,_,_,_,baseEq,memory,_⟩ := layout caller owner scope
  rw [baseEq,memory]
  unfold Proofs.DoublingCall.callerP
  simp only [List.length_append,List.length_replicate]
  omega

theorem prepared_work (caller : NState) (owner scope : Nat) :
    (prepared caller owner scope).scalars.work = caller.scalars.work+3 := by
  simp only [prepared,bstep,Proofs.DynamicPrepare.initial,parameters,NState.release,NState.charge,
    NState.observe,Proofs.CppState.State.observe,List.length_singleton]

-- The original root grant may be mutable or const. Only the callee's new
-- reference is readonly; the input allocation and maximum grant are retained.
theorem prepare_stage (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ callee fuel step bf h,
      prepare caller parameters [.vectorReference slot] = some callee ∧
      runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) callee = .finished step ∧
      step.returned = none ∧ step.breaking = false ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) h ∧
      (∀ i, i < 15 → ∃ field, step.state.frame.state.storage.lookup (caller.frame.state.storage.objects.length+i) = some field ∧
        field.items = (Proofs.BeatsExec.VVB bf i).map Value.integer) ∧
      ∃ input, step.state.frame.state.storage.lookup owner = some input ∧ input.items = a.map Value.integer := by
  let callee := prepared caller owner scope
  have real := prepared_real caller slot vb owner scope wb maximum buf a ok items
  have input := prepared_input caller slot vb owner scope wb maximum buf a ok items
  have entry := prepared_entry caller owner scope maximum a
  have stored : callee.frame.state.storage.lookup owner = some buf := by
    rw [(layout caller owner scope).1]
    exact ok.vfound
  obtain ⟨out,fuel,step,bf,h,_,ran,returned,breaking,rep,_,_,_,_,_,_,vectors⟩ :=
    Proofs.BeatsInlineExec.stage_exec input entry n positive range length values callee real
      (prepared_strict caller owner scope ok.strict) (prepared_base caller owner scope ok.base) buf stored rfl limit
  refine ⟨callee,fuel,step,bf,h,prepare_actual caller slot vb owner scope wb maximum buf ok,
    ran,returned,breaking,rep,?_,?_⟩
  · intro i bound
    simpa only [Proofs.BeatsAllocationArgs.owner,logical,ite_eq_left bound,Proofs.BeatsExec.VVA,
      ite_eq_right (show i ≠ 15 by omega)] using vectors i (by omega)
  · simpa only [Proofs.BeatsAllocationArgs.owner,argument,ite_eq_right (by decide : ¬15 < 15),
      Proofs.BeatsExec.VVA_get15] using vectors 15 (by decide)

end Proofs.BeatsInputPrepare
