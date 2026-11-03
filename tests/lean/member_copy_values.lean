namespace MemberCopyValuesRegression
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppLoop MemberCopy
abbrev i32 : Ty := ⟨32,true,false⟩
def before : NState := ⟨⟨[⟨i32,11⟩,⟨i32,22⟩],[⟨0,false⟩,⟨1,false⟩],7,0,2⟩,
  ⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[.scalar 0,.scalar 1],3,2⟩
def fields : List Field := [.scalar 0 i32 true,.scalar 1 i32 false]
def after : NState := Proofs.CppClassCopyCommands.scalarStep
  (Proofs.CppClassCopyCommands.scalarStep before i32 true 11) i32 false 22

theorem scalar_work_exact : after.work = before.work + copyWork before fields ∧ copyWork before fields = 4 := by
  decide +kernel

theorem ordered_copy : ObjectCopies before after fields ⟨[],[2,3]⟩ := by
  have good : Good before := by constructor <;> decide +kernel
  have sources : Sources before fields := by
    intro field member
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨0,false⟩,⟨i32,11⟩,by decide +kernel⟩
    · exact ⟨⟨1,false⟩,⟨i32,22⟩,by decide +kernel⟩
  obtain ⟨result,ran,_,_,_,_,values⟩ := source_copy_values before fields good sources
  have actual : runCopyFuel 3 before fields = .finished ⟨after,none,false⟩ := by decide +kernel
  change runCopyFuel 3 before fields = _ at ran
  rw [actual] at ran
  have same := congrArg NStep.state (Outcome.finished.inj ran)
  change after = result at same
  subst result
  have size : before.slots.length = 2 := rfl
  simpa [reference,fields,size] using values

theorem wrong_order_rejected : ¬ ObjectCopies before after fields ⟨[],[3,2]⟩ := by
  intro copied
  cases copied.2 with
  | cons head tail =>
    obtain ⟨binding,cell,found,value,_⟩ := head ⟨0,false⟩ ⟨i32,11⟩ (by decide +kernel)
    have actual : after.scalarCell 3 i32 = some (⟨3,false⟩,⟨i32,22⟩) := by decide +kernel
    have cells := (Prod.mk.inj (Option.some.inj (found.symm.trans actual))).2
    rw [cells] at value
    have bad : (22 : Int) ≠ 11 := by decide +kernel
    exact bad value

def denied : NState := {after with scalars := {after.scalars with
  bindings := after.scalars.bindings.set 2 ⟨2,false⟩}}

theorem wrong_permission_rejected : ¬ ObjectCopies before denied fields ⟨[],[2,3]⟩ := by
  intro copied
  cases copied.2 with
  | cons head tail =>
    obtain ⟨binding,cell,found,_,permission⟩ := head ⟨0,false⟩ ⟨i32,11⟩ (by decide +kernel)
    have actual : denied.scalarCell 2 i32 = some (⟨2,false⟩,⟨i32,11⟩) := by decide +kernel
    have bindings := (Prod.mk.inj (Option.some.inj (found.symm.trans actual))).1
    rw [bindings] at permission
    contradiction

end MemberCopyValuesRegression
