import Proofs.BeatsConstructCall

namespace Proofs.BeatsConstructReceiver
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppVectorOwnership
open Proofs.CppRootModel Proofs.CppNestedVectorStore Proofs.CppVector Proofs.CppNestedFacts
open Proofs.BeatsConstructorFields Proofs.CppConstructorMultiFinish Proofs.BeatsConstructCall
open Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec Proofs.IntSim

-- A field returned by the actual object is a live writable root grant, not
-- just a logical payload disconnected from its caller slot.
theorem resolve_field {caller result : NState} {V : Nat → Nat} {n : Nat}
    {prefixCells : List Proofs.CppState.Cell} {vv : Nat → List Int}
    (layout : ExportLayout caller result V n prefixCells)
    (models : ∀ i, i < 15 → Models result.frame.state (V i) (.flat (cty i) caller.scope (vv i)))
    (i : Nat) (bound : i < 15) :
    ∃ buffer, result.vectorSlot (caller.slots.length+i) = some (caller.frame.bindings.length+i) ∧
      result.frame.resolve (caller.frame.bindings.length+i) (.integer (cty i)) =
        some (memberBinding caller V i,buffer) ∧ buffer.items = (vv i).map Value.integer := by
  have model : Flat result.frame.state (V i) (cty i) caller.scope (vv i) := models i bound
  obtain ⟨buffer,found,items⟩ := model.buffer
  have object := object_runs result.frame (V i) (.integer (cty i)) buffer
    ⟨.integer (cty i),none,some caller.scope,[]⟩ model.valid found model.tag rfl
  have maximum := maximum_runs result.frame (V i) (V i) true layout.lengths
    (Proofs.CppVectorOwnership.root_runs _ (V i) _ model.tag rfl) (layout.flags i bound)
  have resolved := resolve_root result.frame (caller.frame.bindings.length+i) (.integer (cty i))
    (memberBinding caller V i) caller.scope buffer ⟨.integer (cty i),none,some caller.scope,[]⟩ true
    (layout.vector i bound).2 rfl rfl object rfl rfl maximum (by intro _; rfl)
  exact ⟨buffer,(layout.vector i bound).1,resolved,items⟩

-- Every previously usable scalar reference (including aliases and readonly
-- grants) still sees the same cell. Invalid old addresses are not assumed live.
theorem old_scalar_kept {caller result : NState} {V : Nat → Nat} {n : Nat}
    (layout : ExportLayout caller result V n caller.scalars.memory)
    (slot : Nat) (bound : slot < caller.slots.length) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : caller.scalarCell slot ty = some (binding,cell)) :
    result.scalarCell slot ty = some (binding,cell) := by
  have sl : result.scalarSlot slot = caller.scalarSlot slot := by
    simp only [NState.scalarSlot,layout.slots,List.append_assoc,List.getElem?_append_left bound]
  simp only [NState.scalarCell,Bind.bind,Option.bind_eq_some_iff] at found
  obtain ⟨index,indexRun,oldBinding,bindingRun,oldCell,cellRun,checked⟩ := found
  have bindingBound := (List.getElem?_eq_some_iff.mp bindingRun).1
  have cellBound := (List.getElem?_eq_some_iff.mp cellRun).1
  have newBinding : result.scalars.bindings[index]? = some oldBinding := by
    rw [layout.scalarBindings,List.getElem?_append_left bindingBound]
    exact bindingRun
  have newCell : result.scalars.memory[oldBinding.address]? = some oldCell := by
    rw [layout.memory,List.getElem?_append_left cellBound]
    exact cellRun
  simp only [NState.scalarCell,Bind.bind,sl,indexRun,Option.bind_some,newBinding,newCell]
  exact checked

theorem construct_fields (caller : NState) (slot vb inputOwner inputScope : Nat) (wb maximum : Bool)
    (buf : Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a) :
    ∃ fuel result bf heap,
      program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
        .finished (result,reference caller 15 2) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      Models result.frame.state inputOwner (.flat s64 inputScope a) ∧
      ExportLayout caller result (fun i => caller.frame.state.storage.objects.length+i) n caller.scalars.memory ∧
      ∀ i, i < 15 → ∃ buffer,
        result.vectorSlot (caller.slots.length+i) = some (caller.frame.bindings.length+i) ∧
        result.frame.resolve (caller.frame.bindings.length+i) (.integer (cty i)) =
          some (memberBinding caller (fun j => caller.frame.state.storage.objects.length+j) i,buffer) ∧
        buffer.items = (VVB bf i).map Value.integer := by
  obtain ⟨fuel,result,bf,heap,ran,rep,models,input,layout⟩ :=
    construct_full caller slot vb inputOwner inputScope wb maximum buf a ok items limit n positive range length values
  refine ⟨fuel,result,bf,heap,ran,rep,input,layout,?_⟩
  apply resolve_field layout
  intro i bound
  simpa only [Proofs.BeatsAllocationArgs.field_type i bound] using models i bound


def fieldBuffer (result : NState) (V : Nat → Nat) (i : Nat) : Buffer Value :=
  (result.frame.state.storage.lookup (V i)).getD ⟨V i,[],0,0,0⟩

theorem field_buffer_facts {caller result : NState} {V : Nat → Nat} {n : Nat}
    {prefixCells : List Proofs.CppState.Cell} {vv : Nat → List Int}
    (layout : ExportLayout caller result V n prefixCells)
    (models : ∀ i, i < 15 → Models result.frame.state (V i) (.flat (cty i) caller.scope (vv i)))
    (i : Nat) (bound : i < 15) :
    result.frame.state.storage.lookup (V i) = some (fieldBuffer result V i) ∧
    (fieldBuffer result V i).items = (vv i).map Value.integer ∧
    (fieldBuffer result V i).Valid (accepts (.integer (cty i))) ∧
    (fieldBuffer result V i).limit = Proofs.CppVectorBindings.sizeLimit (cty i) ∧
    (fieldBuffer result V i).owner = V i ∧ (vv i).length < 18446744073709551616 := by
  obtain ⟨buffer,found,valid,limit,owner,small⟩ := layout.buffers i bound
  have chosen : fieldBuffer result V i = buffer := by simp only [fieldBuffer,found,Option.getD_some]
  have model : Flat result.frame.state (V i) (cty i) caller.scope (vv i) := models i bound
  obtain ⟨other,otherFound,items⟩ := model.buffer
  have same : other = buffer := Option.some.inj (otherFound.symm.trans found)
  subst other
  rw [chosen]
  refine ⟨found,items,valid,limit,owner,?_⟩
  simpa only [items,List.length_map] using small

theorem cty_eq_bty (i : Nat) (bound : i < 15) : cty i = bty i := by
  simp only [cty,bty,show i ≠ 15 by omega,or_false]

-- All fifteen vector conditions required by the six existing operations are
-- derived from the returned object, including buffer contracts and all scopes.
theorem receiver_bvecs {caller result : NState} {V : Nat → Nat} {n : Nat} {vv : Nat → List Int}
    (layout : ExportLayout caller result V n caller.scalars.memory)
    (models : ∀ i, i < 15 → Models result.frame.state (V i) (.flat (cty i) caller.scope (vv i)))
    (distinct : ∀ j k, j < 15 → k < 15 → j ≠ k → V j ≠ V k)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    BVecs result (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
      V (fun _ => caller.scope) (fieldBuffer result V) vv := by
  have facts := field_buffer_facts layout models
  refine ⟨?_,distinct,?_,?_,?_,?_,?_⟩
  · intro i bound
    have model : Flat result.frame.state (V i) (cty i) caller.scope (vv i) := models i bound
    have ok : Proofs.MatMulPrepare.VOKG result (cty i) (caller.slots.length+i)
        (caller.frame.bindings.length+i) (V i) caller.scope true true (fieldBuffer result V i) := by
      refine ⟨model.valid,(layout.vector i bound).1,(layout.vector i bound).2,model.tag,
        (facts i bound).1,layout.lengths,layout.flags i bound,?_,layout.strict,?_⟩
      · intro _; rfl
      · rw [layout.base,layout.memory,List.length_append]
        omega
    simpa only [cty_eq_bty i bound] using ok
  · intro i bound; exact (facts i bound).2.1
  · intro i bound; simpa only [cty_eq_bty i bound] using (facts i bound).2.2.1
  · intro i bound; simpa only [cty_eq_bty i bound] using (facts i bound).2.2.2.1
  · intro i bound; exact (facts i bound).2.2.2.2.1
  · intro i bound; exact (facts i bound).2.2.2.2.2

theorem construct_ready (caller : NState) (slot vb inputOwner inputScope : Nat) (wb maximum : Bool)
    (buf : Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a) :
    ∃ fuel result bf heap,
      program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
        .finished (result,reference caller 15 2) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      Models result.frame.state inputOwner (.flat s64 inputScope a) ∧
      ExportLayout caller result (fun i => caller.frame.state.storage.objects.length+i) n caller.scalars.memory ∧
      BVecs result (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
        (fun i => caller.frame.state.storage.objects.length+i) (fun _ => caller.scope)
        (fieldBuffer result (fun i => caller.frame.state.storage.objects.length+i)) (VVB bf) := by
  obtain ⟨fuel,result,bf,heap,ran,rep,models,input,layout⟩ :=
    construct_full caller slot vb inputOwner inputScope wb maximum buf a ok items limit n positive range length values
  refine ⟨fuel,result,bf,heap,ran,rep,input,layout,?_⟩
  apply receiver_bvecs layout (base := ok.base)
  · intro i bound
    simpa only [Proofs.BeatsAllocationArgs.field_type i bound] using models i bound
  · intro j k _ _ different equal
    exact different (by omega)

end Proofs.BeatsConstructReceiver
