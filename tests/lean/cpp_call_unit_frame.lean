namespace CallUnitFrameExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppCallFrame
abbrev i32 : Ty := ⟨32,true,false⟩
def caller : NState := ⟨⟨[⟨i32,7⟩],[⟨0,true⟩,⟨0,false⟩],3,0,4⟩,
  ⟨⟨⟨[some ⟨.integer i32,none,some 0,[]⟩]⟩,
    {objects := [some ⟨0,[.integer 2,.integer 3],2,64,4⟩],work := 2,baseSpace := 1,peak := 3}⟩,
    [true],[⟨0,.integer i32,true,.root 0⟩]⟩,[.scalar 0,.scalar 1,.vector 0],0,7⟩
def program : NProgram := ⟨[.scalar i32 true true,.vector i32 true],.unit,
  .sequence (.primitive (.write (.local 1) i32 (.literal i32 0) (.literal i32 11)))
    (.sequence (.primitive (.assign 0 i32 (.literal i32 9))) (.primitive .skip))⟩
def args : List NArgument := [.scalarReference 0,.vectorReference 2]
def outcome := program.callFuel 16 caller args
def after : NState := match outcome with | .finished (s,_) => s | _ => caller
#guard outcome == .finished (after,.unit)
#guard after.scalarCell 0 i32 == some (⟨0,true⟩,⟨i32,9⟩)
#guard after.scalarCell 1 i32 == some (⟨0,false⟩,⟨i32,9⟩)
#guard after.scalars.memory != caller.scalars.memory
#guard after.scalars.bindings == caller.scalars.bindings
#guard after.scalars.baseMemory == caller.scalars.baseMemory
#guard after.slots == caller.slots
#guard (after.frame.state.storage.lookup 0).map (·.items) == some [.integer 11,.integer 3]
#guard (after.frame.state.storage.lookup 0).map (·.epoch) == some 4
#guard (after.frame.state.storage.lookup 0).map (·.limit) == some 64

theorem contexts (owner c : Nat) (found : caller.frame.state.forest.context owner = some c) : c ≤ caller.scope := by
  by_cases zero : owner = 0
  · subst owner
    have known : caller.frame.state.forest.context 0 = some 0 := by decide +kernel
    rw [known] at found
    cases found
    exact Nat.zero_le _
  · have gone : caller.frame.state.forest.lookup owner = none :=
      lookup_past_end _ _ (by change 1 ≤ owner; omega)
    have root : caller.frame.state.forest.rootOwner owner = none := by
      rw [Forest.rootOwner]; simp only [gone,Bind.bind,Option.bind_none]
    simp only [Forest.context,root,Bind.bind,Option.bind_none] at found
    contradiction

example : CallEffects caller after :=
  Proofs.CppCallUnitFrame.call_headers program 16 caller after args .unit rfl (by decide) contexts (by decide +kernel)

def callee : NState := {caller with scope := 1}
def unitFinish := finish caller callee .unit (some .unit)
def final : NState := (unitFinish.getD (caller,.unit)).1
#guard unitFinish.isSome
#guard unitFinish == finish caller callee .unit none
#guard finish caller callee .unit (some (.scalar 9)) == none
example : CallEffects caller final := Proofs.CppCallUnitFrame.finish_unit_frame caller callee final (some .unit) .unit
  (Proofs.CppBufferHeaders.SameHeaders.refl _) rfl rfl contexts (by decide +kernel)
end CallUnitFrameExamples
