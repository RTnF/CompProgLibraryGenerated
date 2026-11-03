import Proofs.UfConstructionReferences

namespace Proofs.UfConstructedReceiver
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppRootModel
open Proofs.CppConstructorFinish Proofs.UfConstructionExport Proofs.DynamicResultValid
open Proofs.CppLoop (Outcome liftChecked)
open Proofs.DoublingNested (i32)

theorem finish_base (caller callee out : NState) (vslot : Nat) (element : Element)
    (fields : List ScalarField) (object : ObjectRef)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fields = some (out,object)) :
    out.scalars.baseMemory = caller.scalars.baseMemory := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
    split at rest
    · obtain ⟨values,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨moved,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := bind_some _ _ _ rest
      have eq := (Prod.mk.inj (Option.some.inj same)).1
      subst out
      rfl
    · simp at rest
  · simp at actual

theorem construct_base (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument)
    (vslot : Nat) (element : Element) (fields : List ScalarField) (object : ObjectRef)
    (unit : program.result = .unit)
    (actual : program.constructFuel fuel caller args vslot element fields = .finished (out,object)) :
    out.scalars.baseMemory = caller.scalars.baseMemory := by
  simp only [NProgram.constructFuel,unit,ite_true] at actual
  cases prep : prepare caller program.parameters args with
  | none => simp [prep,liftChecked,bind,Outcome.bind] at actual
  | some init =>
    simp only [prep,liftChecked,bind,Outcome.bind] at actual
    cases ran : CppNestedProgram.runFuel fuel program.body init with
    | fault => simp [ran,bind,Outcome.bind] at actual
    | exhausted => simp [ran,bind,Outcome.bind] at actual
    | finished step =>
      simp only [ran,bind,Outcome.bind] at actual
      split at actual
      · contradiction
      · cases exported : Proofs.CppConstructorFinish.finish caller step.state vslot element fields with
        | none => simp [exported,liftChecked] at actual
        | some pair =>
          simp only [exported,liftChecked,Outcome.finished.injEq] at actual
          subst pair
          exact finish_base caller step.state out vslot element fields object exported

theorem context_inside (f : Forest) (owner scope : Nat) (context : f.context owner = some scope) :
    owner < f.objects.length := by
  by_contra outside
  have missing := lookup_past_end f owner (by omega)
  have rootMissing : f.rootOwner owner = none := by rw [Forest.rootOwner]; simp [missing]
  simp [Forest.context,rootMissing] at context

theorem scope_bound (caller out : NState) (ps : List Int) (count n : Int)
    (initialized : Initialized caller out ps count n)
    (extension : Proofs.CppFrameExtension.Extends caller.frame out.frame)
    (grown : out.frame.state.forest.objects.length = caller.frame.state.forest.objects.length+1)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope) :
    ∀ owner scope, out.frame.state.forest.context owner = some scope → scope ≤ out.scope := by
  intro owner scope found
  have inside := context_inside out.frame.state.forest owner scope found
  have lens := (wellFormed_parts caller.frame.state extension.oldValid).1
  have rootContext := Proofs.DynamicRetire.Models.context initialized.1
  by_cases old : owner < caller.frame.state.forest.objects.length
  · have kept := Proofs.CppConstructionRetire.context_prefix caller.frame.state.forest out.frame.state.forest
      caller.frame.state.forest.objects.length extension.forest owner old
    rw [kept] at found
    rw [initialized.2.2.2.2.2.2.2]
    exact strict owner scope found
  · have same : owner = caller.frame.state.storage.objects.length := by omega
    rw [same,rootContext] at found
    have eq : caller.scope = scope := Option.some.inj found
    rw [← eq,initialized.2.2.2.2.2.2.2]

theorem receiver_ok (caller out : NState) (ps : List Int) (count n : Int)
    (vbuf : Proofs.CppVector.Buffer Value)
    (initialized : Initialized caller out ps count n)
    (extension : Proofs.CppFrameExtension.Extends caller.frame out.frame)
    (grown : out.frame.state.forest.objects.length = caller.frame.state.forest.objects.length+1)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : out.scalars.baseMemory = caller.scalars.baseMemory)
    (baseBound : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (buffer : out.frame.state.storage.lookup caller.frame.state.storage.objects.length = some vbuf) :
    Proofs.UfFindCall.VOKWF out caller.slots.length caller.frame.bindings.length
      caller.frame.state.storage.objects.length caller.scope vbuf := by
  have flat : Flat out.frame.state caller.frame.state.storage.objects.length i32 caller.scope ps := initialized.1
  refine ⟨flat.valid,initialized.2.2.2.2.1,initialized.2.2.2.2.2.1,flat.tag,buffer,
    extension.newLengths,initialized.2.2.2.2.2.2.1,
    scope_bound caller out ps count n initialized extension grown strict,?_⟩
  rw [base,initialized.2.1]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

def buffer (owner n : Nat) : Proofs.CppVector.Buffer Value :=
  ⟨owner,List.replicate n (.integer (-1)),n,Proofs.CppVectorBindings.sizeLimit i32,0⟩

theorem sized_ready (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (baseBound : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Initialized caller out (List.replicate n (-1)) n n ∧
      Proofs.UfFindCall.VOKWF out caller.slots.length caller.frame.bindings.length
        caller.frame.state.storage.objects.length caller.scope (buffer caller.frame.state.storage.objects.length n) ∧
      Proofs.UfClassInvariant.Valid (List.replicate n (-1)) n (fun _ => 0) := by
  have scopes := Proofs.UfConstructionReferences.oldScopes_of_bound caller strict
  obtain ⟨out,ran,initialized,kept,newBuffer,flags,bindings,grown⟩ :=
    Proofs.UfConstructionPreserve.construct_sized caller heap valid models lengths scopes en n small scalar type value
  have extension := Proofs.UfConstructionReferences.extension_of_added caller.frame out.frame _
    valid initialized.1.valid lengths kept flags bindings grown
  have base := construct_base Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 caller out
    [.value en] (vectorField true) (.integer i32) (fields true) (reference caller 2) rfl ran
  have ok := receiver_ok caller out (List.replicate n (-1)) n n _ initialized extension grown strict base baseBound newBuffer
  exact ⟨out,ran,initialized,ok,Proofs.UfClassInvariant.initial_valid n small⟩

theorem default_ready (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (baseBound : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Initialized caller out [] 0 0 ∧
      Proofs.UfFindCall.VOKWF out caller.slots.length caller.frame.bindings.length
        caller.frame.state.storage.objects.length caller.scope (buffer caller.frame.state.storage.objects.length 0) ∧
      Proofs.UfClassInvariant.Valid [] 0 (fun _ => 0) := by
  have scopes := Proofs.UfConstructionReferences.oldScopes_of_bound caller strict
  obtain ⟨out,ran,initialized,kept,newBuffer,flags,bindings,grown⟩ :=
    Proofs.UfConstructionPreserve.construct_default caller heap valid models lengths scopes
  have extension := Proofs.UfConstructionReferences.extension_of_added caller.frame out.frame _
    valid initialized.1.valid lengths kept flags bindings grown
  have base := construct_base Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 caller out
    [] (vectorField false) (.integer i32) (fields false) (reference caller 2) rfl ran
  have ok := receiver_ok caller out [] 0 0 _ initialized extension grown strict base baseBound newBuffer
  exact ⟨out,ran,initialized,ok,Proofs.UfClassInvariant.initial_valid 0 (by omega)⟩

-- Use the stored _n field, rather than assuming a successful argument expression.
theorem n_expression (caller out : NState) (ps : List Int) (count n : Int)
    (initialized : Initialized caller out ps count n) :
    (NExpr.variable i32 (caller.slots.length+2)).denote (Proofs.CppNestedEval.envOf out) = some n := by
  simp [NExpr.denote,Proofs.CppNestedEval.envOf,initialized.2.2.2.1]

theorem getter_from_ready (caller receiver : NState) (n : Nat)
    (initialized : Initialized caller receiver (List.replicate n (-1)) n n)
    (ok : Proofs.UfFindCall.VOKWF receiver caller.slots.length caller.frame.bindings.length
      caller.frame.state.storage.objects.length caller.scope (buffer caller.frame.state.storage.objects.length n))
    (invariant : Proofs.UfClassInvariant.Valid (List.replicate n (-1)) n (fun _ => 0)) :
    ∃ fuel out, Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel receiver
      [.vectorReference caller.slots.length,.scalarReference (caller.slots.length+1),
       .value (.variable i32 (caller.slots.length+2))] = .finished (out,.scalar (n : Int)) := by
  obtain ⟨tag,tagFound,owner,payload⟩ := wellFormed_buffer receiver.frame.state
    caller.frame.state.storage.objects.length (buffer caller.frame.state.storage.objects.length n) ok.valid ok.vfound
  have tagEq : tag = ⟨.integer i32,none,some caller.scope,[]⟩ := Option.some.inj (tagFound.symm.trans ok.vtag)
  subst tag
  have bvalid : (buffer caller.frame.state.storage.objects.length n).Valid (accepts (.integer i32)) := payload.1
  have value := n_expression caller receiver (List.replicate n (-1)) n n initialized
  obtain ⟨init,fuel,out,prepared,called,_⟩ := Proofs.UfFieldsCounter.num_groups_call receiver ok
    ⟨caller.scalars.memory.length,true⟩ n initialized.2.2.1 rfl (List.replicate n (-1)) (fun _ => 0)
    invariant (by simp [buffer,List.map_replicate]) bvalid rfl rfl
    (.variable i32 (caller.slots.length+2)) rfl rfl (by simpa using value)
  rw [← invariant.count] at called
  exact ⟨fuel,out,called⟩

theorem sized_getter (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (baseBound : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ receiver fuel out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (receiver,reference caller 2) ∧
      Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel receiver
        [.vectorReference caller.slots.length,.scalarReference (caller.slots.length+1),
         .value (.variable i32 (caller.slots.length+2))] = .finished (out,.scalar (n : Int)) := by
  obtain ⟨receiver,constructed,initialized,ok,invariant⟩ := sized_ready caller heap valid models lengths strict baseBound en n small scalar type value
  obtain ⟨fuel,out,called⟩ := getter_from_ready caller receiver n initialized ok invariant
  exact ⟨receiver,fuel,out,constructed,called⟩

theorem default_getter (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (baseBound : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ receiver fuel out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (vectorField false) (.integer i32) (fields false) = .finished (receiver,reference caller 2) ∧
      Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel receiver
        [.vectorReference caller.slots.length,.scalarReference (caller.slots.length+1),
         .value (.variable i32 (caller.slots.length+2))] = .finished (out,.scalar 0) := by
  obtain ⟨receiver,constructed,initialized,ok,invariant⟩ := default_ready caller heap valid models lengths strict baseBound
  obtain ⟨fuel,out,called⟩ := getter_from_ready caller receiver 0 initialized ok invariant
  exact ⟨receiver,fuel,out,constructed,called⟩

end Proofs.UfConstructedReceiver
