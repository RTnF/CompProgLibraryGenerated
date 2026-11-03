namespace UfReadValuesExamples
open UfReadCallExamples Proofs.UfReadValues Proofs.UfReadPrograms
open Proofs.CppMoveContext Proofs.CppMoveReadReceiver Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverPermissions Proofs.CppMoveFrame Proofs.DoublingNested
open Proofs.CppMoveCallBindings Proofs.CppScalar

def Preserved (w : Bool) (out : Context) : Prop :=
  (∀ owner, (project out i32).frame.state.storage.lookup owner = (project (input w) i32).frame.state.storage.lookup owner) ∧
  (∀ reference, (project out i32).frame.read reference = (project (input w) i32).frame.read reference) ∧
  ∃ next : ReadReceiver out object i32,
    next.counter.value = (receiver w).counter.value ∧ next.size.value = (receiver w).size.value

theorem world (w : Bool) (out : Context) (program : NProgram) (expressions : List (NExpr × Int))
    (ready : Ready (input w) i32 expressions)
    (params : program.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true :: parameters i32 expressions)
    (retType : Ty) (scalar : program.result = .scalar retType) (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (fuel : Nat) (result : Ret)
    (actual : callFuel program fuel (input w) i32 (readArguments (input w) object (receiver w) expressions) = .finished (out,result))
    (payload : ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Proofs.CppNestedVectorStore.Value.integer)
    (memory : out.scalars.memory = (input w).scalars.memory) : Preserved w out := by
  have all := all_payload (input w) out object (receiver w) program expressions ready params retType scalar allowed data rfl
    (readable w) (unique w) (covered w) (allocations w) rfl (contexts w) fuel result actual payload
  have oldValid := materialize_ready (input w).objects i32 (by decide +kernel) (allocations w)
  have reads := reads (input w) out program fuel _ result (covered w) oldValid actual all
  let after := receiver_after (input w) out object (receiver w)
    (Proofs.CppMoveCallLayout.call_layout program fuel (input w) out i32 _ result actual) memory
  exact ⟨all,reads,after,rfl,rfl⟩

example (w : Bool) : ∃ fuel out weight,
    callFuel sizeProgram fuel (input w) i32 (readArguments (input w) object (receiver w) [(.variable i32 3,1)]) =
      .finished (out,.scalar (-weight)) ∧ Preserved w out := by
  obtain ⟨fuel,out,root,weight,call,_,_,_,_,_,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.size_call (input w) object (receiver w) data rfl id forest (by decide +kernel) weights 1
      (by decide +kernel) (.variable i32 3) rfl rfl rfl (readable w) (unique w) (covered w) (allocations w) rfl
      (by change 0 ≤ _; omega) (contexts w)
  exact ⟨fuel,out,weight,call,world w out sizeProgram [(.variable i32 3,1)] (oneArg w) rfl i32 rfl
    (by decide +kernel) fuel (.scalar (-weight)) call payload memory⟩

example (w : Bool) : ∃ fuel out answer,
    callFuel sameProgram fuel (input w) i32
      (readArguments (input w) object (receiver w) [(.variable i32 3,1),(.variable i32 4,3)]) =
      .finished (out,.scalar answer) ∧ Preserved w out := by
  obtain ⟨fuel,out,r1,r2,call,_,_,_,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.same_call (input w) object (receiver w) data rfl id forest (by decide +kernel) 1 3
      (by decide +kernel) (by decide +kernel) (.variable i32 3) (.variable i32 4) (twoArgs w)
      (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
  exact ⟨fuel,out,_,call,world w out sameProgram [(.variable i32 3,1),(.variable i32 4,3)] (twoArgs w) rfl
    Proofs.PrefixSumsCall.bT rfl (by decide +kernel) fuel _ call payload memory⟩

example (w : Bool) : ∃ fuel out,
    callFuel counterProgram fuel (input w) i32 (readArguments (input w) object (receiver w) []) =
      .finished (out,.scalar (receiver w).counter.value) ∧ Preserved w out := by
  obtain ⟨actualData,fuel,out,current,call,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.counter_call (input w) object (receiver w) (readable w) (unique w) (covered w)
      (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
  have same : actualData = data := Option.some.inj (current.symm.trans (show _ = some data from rfl))
  subst actualData
  exact ⟨fuel,out,call,world w out counterProgram [] (by intro e value member; simp at member) rfl i32 rfl
    (by decide +kernel) fuel _ call payload memory⟩
end UfReadValuesExamples
