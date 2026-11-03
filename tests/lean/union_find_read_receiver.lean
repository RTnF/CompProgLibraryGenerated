namespace ReadReceiverPermissionExamples
open Proofs.CppMoveContext Proofs.CppMoveReceiverPermissions Proofs.CppMoveReadReceiver
open Proofs.CppMoveReceiverResolve Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppScalar
abbrev ty : Ty := ⟨32,true,false⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit ty

def input : Context := ⟨⟨⟨[some ⟨none,0,false,limit⟩],[],[],0,0,0⟩,[⟨0,false⟩]⟩,
  ⟨[⟨ty,1⟩,⟨ty,4⟩,⟨ty,0⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.scalar 2],0,0⟩
def object : ObjectRef := ⟨0,[1,2]⟩
def receiver : ReadReceiver input object ty :=
  ⟨⟨1,0,0,false,1,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨2,1,1,false,4,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,0,⟨0,false⟩,⟨none,0,false,limit⟩,rfl,rfl⟩

theorem noArgs : Ready input ty [] := by
  intro e v member
  simp at member

theorem oneArg : Ready input ty [(.variable ty 3,0)] := by
  intro e v member
  have equal := List.mem_singleton.mp member
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,rfl⟩

example := prepare_read input object ty receiver [] noArgs
example := prepare_read input object ty receiver [(.variable ty 3,0)] oneArg
#guard (captureBorrow input 0 false).isSome
#guard (captureBorrow input 0 true).isNone
#guard (captureScalarReference input ty 1 false).isSome
#guard (captureScalarReference input ty 1 true).isNone
#guard (match prepareArguments input ty
    [.vector ty false,.scalar ty true false,.scalar ty false true,.scalar ty false true]
    [.vectorReference 0,.scalarReference 1,.value (.variable ty 2),.value (.variable ty 3)] with
  | some out => out.scalars.bindings.map (·.writable) == [false,true,true] &&
      out.objects.views.map (·.writable) == [false,false] && out.scalars.memory.take 3 == input.scalars.memory
  | none => false)
#guard (prepareArguments input ty
    [.vector ty false,.scalar ty true true,.scalar ty false true,.scalar ty false true]
    [.vectorReference 0,.scalarReference 1,.value (.variable ty 2),.value (.variable ty 3)]).isNone
end ReadReceiverPermissionExamples

namespace ReadReceiverMovedGetterExamples
open ReadReceiverPermissionExamples Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveContext
open Proofs.UfReadCall Proofs.UfReadPrograms Proofs.CppNestedProgram Proofs.CppNestedCall

theorem header (id : Nat) (h : Header) (found : input.objects.heap.header id = some h) :
    id=0 ∧ h=⟨none,0,false,limit⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup _ _ _ found)).1
  change id < 1 at inside
  have zero : id=0 := by omega
  subst id
  have atZero : input.objects.heap.header 0 = some ⟨none,0,false,limit⟩ := rfl
  rw [atZero] at found
  exact ⟨rfl,(Option.some.inj found).symm⟩
theorem unique : Unique input.objects.heap := by
  intro i j hi hj owner fi fj oi oj
  exact (header i hi fi).1.trans (header j hj fj).1.symm
theorem covered : OwnsAll input.objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside input.objects.heap owner tracked found
  change owner < 0 at inside
  omega
theorem allocations : AllocationsValid input.objects.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside input.objects.heap owner tracked found
  change owner < 0 at inside
  omega
theorem contexts : ∀ owner scope, (project input ty).frame.state.forest.context owner = some scope → scope ≤ input.scope := by
  apply Proofs.CppMoveFrameScopes.contexts_of_headers input.objects ty input.scope
  intro id h found
  obtain ⟨_,rfl⟩ := header id h found
  exact Nat.le_refl _
example := counter_call input object receiver (by decide +kernel) unique covered allocations rfl
  (by change 0 ≤ _; omega) contexts
#guard (match Proofs.CppMoveCallBindings.callFuel counterProgram 2 input ty
    [.vectorReference 0,.scalarReference 1,.value (.variable ty 2)] with
  | .finished (out,result) => result == .scalar 1 && out.scalars.memory == input.scalars.memory &&
      out.objects.heap.headers == input.objects.heap.headers && out.objects.views == input.objects.views
  | _ => false)
end ReadReceiverMovedGetterExamples

namespace ReadReceiverMovedGetterBudgetExamples
open ReadReceiverPermissionExamples ReadReceiverMovedGetterExamples
example := Proofs.UfReadPrepareBudget.counter_call input object receiver (by decide +kernel) unique covered allocations rfl
  (by change 0 ≤ _; omega) contexts
end ReadReceiverMovedGetterBudgetExamples
