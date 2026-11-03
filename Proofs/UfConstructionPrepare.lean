import Proofs.UfConstructionStage

namespace Proofs.UfConstructionPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.DoublingNested Proofs.DoublingCall
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.MultiVecDynamic Proofs.CppRootModel
open Proofs.UfConstructionStage

-- Argument values are copied after caller locals have been reserved. No
-- successful prepare/run is assumed, and existing caller aliases stay outside.
theorem prepare_sized (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (en : NExpr) (n : Int) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some n) (nvalid : i32.valid n = true) :
    ∃ init, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters [.value en] = some init ∧
      snapshot init = ⟨callerP caller++[⟨i32,n⟩],[⟨(callerP caller).length,true⟩],[.scalar 0]⟩ ∧
      init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧ init.scope = caller.scope+1 ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧
      init.scalars.work ≤ caller.scalars.work+en.nodes+2 := by
  obtain ⟨q,ran,good⟩ := scalar_eval en caller n scalar value
  obtain ⟨frame,slots,scope,memory,bindings,base⟩ := good.1
  have fs : q.frame.state = caller.frame.state := by rw [frame]
  have fr : q.frame.rootWritable = caller.frame.rootWritable := by rw [frame]
  have fb : q.frame.bindings = caller.frame.bindings := by rw [frame]
  have resolved : resolve caller (.scalar i32 false true) (.value en) = some (q,.scalar i32 true n) := by
    simp [resolve,type,ran]
  have hp : Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters = [.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,valid,resolveAll,resolved,bindAll,bindOne,CppState.bindArgument,nvalid,
    snapshot,NState.release,NState.observe,CppState.State.observe,fs,fr,fb,memory,bindings,base,callerP]
  exact good.2.2.1

theorem prepare_default (caller : NState) (valid : caller.frame.state.wellFormed = true) :
    ∃ init, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters [] = some init ∧
      snapshot init = ⟨callerP caller,[],[]⟩ ∧
      init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧ init.scope = caller.scope+1 ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧ init.scalars.work = caller.scalars.work+1 := by
  have hp : Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters = [] := rfl
  rw [hp]
  simp [prepare,valid,resolveAll,bindAll,snapshot,NState.release,NState.observe,callerP]


theorem sized_real (caller init : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) (n : Nat)
    (locals : snapshot init = ⟨callerP caller++[⟨i32,n⟩],[⟨(callerP caller).length,true⟩],[.scalar 0]⟩)
    (frame : init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩) (scope : init.scope = caller.scope+1) :
    Proofs.DynamicOwnedState.Realizes
      (entry (callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1) n) init := by
  have family := Proofs.DynamicFamilyInit.empty heap init.frame
    (by rw [frame]; exact valid) (by rw [frame]; exact models) (by rw [frame]; exact lengths)
  refine ⟨⟨locals,heap,_,family,rfl⟩,?_,?_,scope⟩
  · rw [frame]
    rfl
  · rw [frame]
    rfl

theorem default_real (caller init : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (locals : snapshot init = ⟨callerP caller,[],[]⟩)
    (frame : init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩) (scope : init.scope = caller.scope+1) :
    Proofs.DynamicOwnedState.Realizes
      (defaultEntry (callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1)) init := by
  have family := Proofs.DynamicFamilyInit.empty heap init.frame
    (by rw [frame]; exact valid) (by rw [frame]; exact models) (by rw [frame]; exact lengths)
  refine ⟨⟨locals,heap,_,family,rfl⟩,?_,?_,scope⟩
  · rw [frame]
    rfl
  · rw [frame]
    rfl

theorem sized_from_caller (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648)
    (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ init out, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters [.value en] = some init ∧
      CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct1.body init = .finished out ∧
      Proofs.DynamicOwnedState.Realizes
        (final (callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1) n) out.state ∧
      out.returned = none ∧ out.breaking = false ∧
      Proofs.UfClassInvariant.Valid (List.replicate n (-1)) n (fun _ => 0) ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧ init.scalars.work ≤ caller.scalars.work+en.nodes+2 := by
  obtain ⟨init,prepared,locals,frame,scope,base,work⟩ := prepare_sized caller valid en n scalar type value (nat_i32 n small)
  have real := sized_real caller init heap valid models lengths n locals frame scope
  obtain ⟨out,ran,after,ret,br,initialValid⟩ := sized_stage (callerP caller) (eraseHeap heap) []
    caller.frame.state.storage.objects.length 0 (caller.scope+1) n small init real
  exact ⟨init,out,prepared,ran,after,ret,br,initialValid,base,work⟩

theorem default_from_caller (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    ∃ init out, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters [] = some init ∧
      CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct0.body init = .finished out ∧
      Proofs.DynamicOwnedState.Realizes
        (defaultFinal (callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1)) out.state ∧
      out.returned = none ∧ out.breaking = false ∧ Proofs.UfClassInvariant.Valid [] 0 (fun _ => 0) ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧ init.scalars.work = caller.scalars.work+1 := by
  obtain ⟨init,prepared,locals,frame,scope,base,work⟩ := prepare_default caller valid
  have real := default_real caller init heap valid models lengths locals frame scope
  obtain ⟨out,ran,after,ret,br,initialValid⟩ := default_stage (callerP caller) (eraseHeap heap) []
    caller.frame.state.storage.objects.length 0 (caller.scope+1) init real
  exact ⟨init,out,prepared,ran,after,ret,br,initialValid,base,work⟩

end Proofs.UfConstructionPrepare
