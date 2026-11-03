import Proofs.BeatsConstructorFields
import Proofs.BeatsInputPrepare

namespace Proofs.BeatsConstructCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppVectorOwnership
open Proofs.CppRootModel Proofs.BeatsInputPrepare Proofs.BeatsConstructorFields
open Proofs.CppConstructorMultiFinish Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec
open Proofs.BeatsAllocationArgs Proofs.IntSim

-- This is the wide candidate's source-matched inline constructor, including
-- all fifteen allocations. The candidate source is checked against this value.
def program : NProgram := ⟨parameters,.unit,Proofs.BeatsInlineExec.stage 0 15⟩

theorem initial_prefix (caller : NState) (owner scope : Nat) (maximum : Bool) (a : List Int) :
    caller.scalars.memory.length ≤ (logical caller owner scope maximum a).core.locals.memory.length ∧
    (logical caller owner scope maximum a).core.locals.memory.take caller.scalars.memory.length = caller.scalars.memory := by
  change caller.scalars.memory.length ≤ (prepared caller owner scope).scalars.memory.length ∧
    (prepared caller owner scope).scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
  rw [(layout caller owner scope).2.2.2.2.2.2.1]
  simp [Proofs.DoublingCall.callerP]

-- Root input grants may be mutable or readonly, with arbitrary caller slot,
-- binding, owner, scalar aliases and older objects. Only the prepared input
-- reference becomes readonly. No successful constructor/export is a premise.
theorem construct_full (caller : NState) (slot vb inputOwner inputScope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a) :
    ∃ fuel result bf heap,
      program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
        .finished (result,reference caller 15 2) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      (∀ i, i < 15 → Models result.frame.state (caller.frame.state.storage.objects.length+i)
        (.flat (Proofs.BeatsAllocation.fieldTy i) caller.scope (VVB bf i))) ∧
      Models result.frame.state inputOwner (.flat s64 inputScope a) ∧
      ExportLayout caller result (fun i => caller.frame.state.storage.objects.length+i) n caller.scalars.memory := by
  let init := prepared caller inputOwner inputScope
  let st := logical caller inputOwner inputScope maximum a
  let p := argument inputOwner inputScope maximum
  have real := prepared_real caller slot vb inputOwner inputScope wb maximum buf a ok items
  have input := prepared_input caller slot vb inputOwner inputScope wb maximum buf a ok items
  have entry := prepared_entry caller inputOwner inputScope maximum a
  have stored : init.frame.state.storage.lookup inputOwner = some buf := by
    rw [(layout caller inputOwner inputScope).1]
    exact ok.vfound
  have prefixFacts := initial_prefix caller inputOwner inputScope maximum a
  obtain ⟨fuel,step,bf,heap,result,ran,returned,breaking,rep,finished,members,facts⟩ :=
    stage_export_full caller input entry n positive range length values init real
      (prepared_strict caller inputOwner inputScope ok.strict)
      (prepared_base caller inputOwner inputScope ok.base) buf stored rfl limit rfl prefixFacts.1
      (congrArg (List.map Proofs.CppState.Cell.type) prefixFacts.2)
  have stepEq : step = ⟨step.state,none,false⟩ := by cases step; simp_all
  have body : runFuel fuel program.body init = .finished ⟨step.state,none,false⟩ := by
    rw [stepEq] at ran
    exact ran
  refine ⟨fuel,result,bf,heap,?_,rep,?_,?_,?_⟩
  · exact construct_of_steps program fuel caller init step.state result [.vectorReference slot]
      vectorFields scalarFields (reference caller 15 2) rfl
      (prepare_actual caller slot vb inputOwner inputScope wb maximum buf ok) body finished
  · intro i bound
    have member : (owner st p i,View.flat (cty i) (Proofs.BeatsAllocationArgs.scope st p i) (VVA a bf i)) ∈
        roots (owner st p) (Proofs.BeatsAllocationArgs.scope st p) (VVA a bf) :=
      List.mem_map.mpr ⟨i,List.mem_range.mpr bound,rfl⟩
    have model := members _ member
    simpa only [owner,st,logical,ite_eq_left bound,Proofs.DynamicTransfer.inScope,
      field_type i bound,VVA,ite_eq_right (show i ≠ 15 by omega)] using model

  · have inputModel : Models step.state.frame.state inputOwner (.flat s64 inputScope a) := by
      simpa only [owner,st,p,logical,argument,ite_eq_right (by decide : ¬15 < 15),
        Proofs.BeatsAllocationArgs.scope,cty,or_true,ite_true,VVA_get15] using facts.models 15 (by decide)
    have absent : inputOwner ∉ (roots (owner st p) (Proofs.BeatsAllocationArgs.scope st p) (VVA a bf)).map Prod.fst := by
      intro member
      change inputOwner ∈ (List.range 15).map (fun i => owner st p i) at member
      obtain ⟨i,inRange,equal⟩ := List.mem_map.mp member
      have bound := List.mem_range.mp inRange
      have earlier := Proofs.CppVectorStore.lookup_bound caller.frame.state.storage inputOwner buf ok.vfound
      simp only [owner,st,logical,ite_eq_left bound] at equal
      omega
    have oldModel : Models caller.frame.state inputOwner (.flat s64 inputScope a) :=
      ⟨ok.valid,ok.vtag,buf,ok.vfound,items⟩
    have bound := ok.strict inputOwner inputScope (Proofs.DynamicRetire.Models.context oldModel)
    exact facts.kept inputOwner (.flat s64 inputScope a) inputModel absent (by
      change inputScope ≠ step.state.scope
      rw [facts.scope]
      change inputScope ≠ caller.scope+1
      omega)
  · have converted := facts.layout.congr_fields (W := fun i => caller.frame.state.storage.objects.length+i) (by
      intro i bound
      simp only [owner,logical,ite_eq_left bound])
    simpa only [prefixFacts.2] using converted

theorem construct (caller : NState) (slot vb inputOwner inputScope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a) :
    ∃ fuel result bf heap,
      program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
        .finished (result,reference caller 15 2) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      (∀ i, i < 15 → Models result.frame.state (caller.frame.state.storage.objects.length+i)
        (.flat (Proofs.BeatsAllocation.fieldTy i) caller.scope (VVB bf i))) ∧
      Models result.frame.state inputOwner (.flat s64 inputScope a) := by
  obtain ⟨fuel,result,bf,heap,ran,rep,members,input,_⟩ :=
    construct_full caller slot vb inputOwner inputScope wb maximum buf a ok items limit n positive range length values
  exact ⟨fuel,result,bf,heap,ran,rep,members,input⟩

end Proofs.BeatsConstructCall
