import Proofs.UfObjectRootScalarPeak

namespace Proofs.UfObjectMethodScalarPeak
open Proofs.CppNestedProgram Proofs.VecExpr Proofs.VecWrite Proofs.StraightLine Proofs.QuotientFrame
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.DoublingNested Proofs.CppState
open Proofs.CppCompactScalarPeak Proofs.UfRootCall

def budget (s : NState) (prefixLength allowance : Nat) : Nat :=
  max s.scalars.peak (prefixLength+allowance-s.scalars.baseMemory)

theorem actual_prefix_peak (s : NState) (vc : VCtx) (w : Bool)
    (permission : w = true → vc.wV = true ∧ vc.flag = true) (body : Command) (allowed : WrV w body = true)
    (logicalFuel : Nat) (locals : PS) (vec : List Int) (res : PRW)
    (executed : pexecW vc.ty logicalFuel body locals vec = some res) (buffer : Buffer Value) (prefixLength allowance : Nat)
    (qs : QS s [] s.scalars.baseMemory s.scope locals.mem locals.bs (sl1 locals.bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ locals.mem.length)
    (resident : locals.mem.length+locals.bs.length ≤ prefixLength+allowance)
    (need : res.need ≤ prefixLength+allowance) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep) (actual : Proofs.CppNestedProgram.runFuel fuel body s = .finished step) :
    step.state.scalars.peak ≤ budget s prefixLength allowance := by
  have room : prefixLength+allowance ≤ budget s prefixLength allowance+s.scalars.baseMemory := by
    have bound := Nat.le_max_right s.scalars.peak (prefixLength+allowance-s.scalars.baseMemory)
    change prefixLength+allowance-s.scalars.baseMemory ≤ budget s prefixLength allowance at bound
    omega
  exact actual_body_peak s vc w permission body allowed logicalFuel locals vec res executed buffer _ qs frame
    (Nat.le_max_left _ _) base (by omega) (by omega) scope fuel step actual

theorem same_body_peak (s : NState) (vc : VCtx) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (P : List Cell) (counter : Binding)
    (buffer : Buffer Value) (ty : vc.ty = i32) (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope (Proofs.UfFieldsSame.fields P counter vec.length a b).mem (Proofs.UfFieldsSame.fields P counter vec.length a b).bs
      (sl1 (Proofs.UfFieldsSame.fields P counter vec.length a b).bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep)
    (actual : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_same.body s = .finished step) :
    step.state.scalars.peak ≤ budget s P.length 80 := by
  obtain ⟨res,r1,r2,middle,executed,returned,c1,c2,newForest,reach1,reach2,oldRoot2,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsSame.body_correct P counter vec rank forest length a b ha hb (max (rank a) (rank b)+2) (by omega) (by omega)
  have run : pexecW vc.ty (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_same.body
      (Proofs.UfFieldsSame.fields P counter vec.length a b) vec = some res := by rw [ty]; exact executed
  apply actual_prefix_peak s vc true (fun _ => permission) _ (by decide) (max (rank a) (rank b)+2) _ vec res run buffer P.length 80
    qs frame _ _ (need) scope fuel step actual
  · simp only [Proofs.UfFieldsSame.fields,List.length_append,List.length_cons,List.length_nil]
    omega
  · simp only [Proofs.UfFieldsSame.fields,List.length_append,List.length_cons,List.length_nil]
    omega

theorem size_body_peak (s : NState) (vc : VCtx) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights vec) (a : Nat) (inside : a < vec.length) (P : List Cell) (counter : Binding)
    (buffer : Buffer Value) (ty : vc.ty = i32) (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope (Proofs.UfFieldsRoot.fields P counter vec.length a).mem (Proofs.UfFieldsRoot.fields P counter vec.length a).bs
      (sl1 (Proofs.UfFieldsRoot.fields P counter vec.length a).bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep)
    (actual : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_size.body s = .finished step) :
    step.state.scalars.peak ≤ budget s P.length 80 := by
  obtain ⟨res,r,weight,executed,returned,atRoot,negative,resultValid,compressed,newForest,newWeights,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsSize.body_correct P counter vec rank forest length weights a inside (rank a+2) (by omega)
  have run : pexecW vc.ty (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_size.body
      (Proofs.UfFieldsRoot.fields P counter vec.length a) vec = some res := by rw [ty]; exact executed
  apply actual_prefix_peak s vc true (fun _ => permission) _ (by decide) (rank a+2) _ vec res run buffer P.length 80
    qs frame _ _ (need) scope fuel step actual
  · simp only [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI,List.length_append,List.length_cons,List.length_nil]
    omega
  · simp only [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI,List.length_append,List.length_cons,List.length_nil]
    omega

theorem unite_body_peak (s : NState) (vc : VCtx) (vec : List Int)
    (rank : Nat → Nat) (groups : Int) (valid : Proofs.UfClassInvariant.Valid vec groups rank)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (P : List Cell) (counter : Nat) (countFound : P[counter]? = some ⟨i32,groups⟩)
    (buffer : Buffer Value) (ty : vc.ty = i32) (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).mem (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs
      (sl1 (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep)
    (actual : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body s = .finished step) :
    step.state.scalars.peak ≤ budget s P.length 100 := by
  obtain ⟨res,r1,r2,middle,two,executed,returned,c1,c2,finalEq,newValid,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsUnite.body_correct P counter groups vec rank valid countFound a b ha hb
      (max (rank a) (rank b)+2) (by omega) (by omega)
  have run : pexecW vc.ty (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_unite.body
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b) vec = some res := by rw [ty]; exact executed
  apply actual_prefix_peak s vc true (fun _ => permission) _ (by decide) (max (rank a) (rank b)+2) _ vec res run buffer P.length 100
    qs frame _ _ (need) scope fuel step actual
  · simp only [Proofs.UfFieldsSame.fields,List.length_append,List.length_cons,List.length_nil]
    omega
  · simp only [Proofs.UfFieldsSame.fields,List.length_append,List.length_cons,List.length_nil]
    omega

theorem counter_body_peak (s : NState) (vc : VCtx) (vec : List Int)
    (n groups : Int) (P : List Cell) (counter : Nat) (countFound : P[counter]? = some ⟨i32,groups⟩) (valueValid : i32.valid groups = true)
    (buffer : Buffer Value) (ty : vc.ty = i32)
    (qs : QS s [] s.scalars.baseMemory s.scope (Proofs.UfFieldsCounter.fields P counter n).mem (Proofs.UfFieldsCounter.fields P counter n).bs
      (sl1 (Proofs.UfFieldsCounter.fields P counter n).bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep)
    (actual : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body s = .finished step) :
    step.state.scalars.peak ≤ budget s P.length 6 := by
  let res : PRW := ⟨Proofs.UfFieldsCounter.fields P counter n,vec,some groups,2,P.length+6,0⟩
  have executed := Proofs.UfFieldsCounter.body_correct P counter n groups vec countFound valueValid 0
  have run : pexecW vc.ty (0) Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
      (Proofs.UfFieldsCounter.fields P counter n) vec = some res := by rw [ty]; exact executed
  apply actual_prefix_peak s vc false (by intro impossible; contradiction) _ (by decide) (0) _ vec res run buffer P.length 6
    qs frame _ _ (Nat.le_refl (P.length+6)) scope fuel step actual
  · simp only [Proofs.UfFieldsCounter.fields,List.length_append,List.length_cons,List.length_nil]
    omega
  · simp only [Proofs.UfFieldsCounter.fields,List.length_append,List.length_cons,List.length_nil]
    omega

open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppMoveReceiverResolve
open Proofs.UfObjectTrace Proofs.CppMoveCallBindings Proofs.UfReceiverLayout Proofs.CppMoveReceiverLayout

-- Each external expression in this trace is a valid i32 index literal.
theorem expressions_ready (s : Context) (object : ObjectRef) (state : Proofs.UfObjectState.State s object)
    (op : Operation) (ready : op.Valid state.data.items.length) : Ready s i32 op.expressions := by
  have one : ∀ a : Nat, a < state.data.items.length → Ready s i32 [(.literal i32 (a : Int),(a : Int))] := by
    intro a inside expression value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,by simp [NExpr.denote,literal_valid s object state a inside]⟩
  cases op with
  | root a | size a => exact one a ready
  | same a b | unite a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    intro expression value member
    rcases List.mem_cons.mp member with head | tail
    · exact one a ready.1 expression value (List.mem_singleton.mpr head)
    · exact one b ready.2 expression value tail
  | groups => intro expression value member; cases member

-- A single prepare/finish path for all five original source methods.
theorem call_peak (s out : Context) (object : ObjectRef) (state : Proofs.UfObjectState.State s object)
    (op : Operation) (ready : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    ∃ prepared, prepareArguments s i32 op.program.parameters
      (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) = some prepared ∧
      out.scalars.peak ≤ max (max s.scalars.peak
        (max prepared.scalars.peak ((receiverPrefix s).length+100-s.scalars.baseMemory)))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,frame,ty,writable,flag,sc,current,base,scope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver op.program op.expressions
      (expressions_ready s object state op ready) (by cases op <;> rfl) state.readable state.unique state.covered
      state.allocations state.limit state.contexts
  have sameBuffer := Option.some.inj (current.symm.trans state.current)
  subst buffer
  rw [invoke_state fuel s object state op] at actual
  obtain ⟨prepared2,initial2,step,after,prep2,compact2,body,breaking,finished,restored⟩ :=
    call_parts op.program fuel s out i32 _ result actual
  have samePrepared := Option.some.inj (prep.symm.trans prep2)
  subst prepared2
  have sameInitial := Option.some.inj (compacted.symm.trans compact2)
  subst initial2
  have sharp : step.state.scalars.peak ≤ budget initial (receiverPrefix s).length 100 := by
    cases op with
    | root a =>
      have fields := qs_two initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) qs
      rw [state.size] at fields
      have bound := Proofs.UfObjectRootScalarPeak.root_body_peak initial vc state.data.items state.rank state.math.forest
        state.math.length a ready (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ (Proofs.CppMoveFrame.box state.data)
        ty ⟨writable,flag⟩ fields frame (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
      unfold Proofs.UfObjectRootScalarPeak.budget at bound
      unfold budget
      clear * - bound
      omega
    | same a b =>
      have fields := qs_three initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) (b : Int) qs
      rw [state.size] at fields
      have bound := same_body_peak initial vc state.data.items state.rank state.math.forest state.math.length a b ready.1 ready.2
        (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ (Proofs.CppMoveFrame.box state.data) ty ⟨writable,flag⟩ fields frame
        (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
      unfold budget at bound ⊢
      clear * - bound
      omega
    | size a =>
      have fields := qs_two initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) qs
      rw [state.size] at fields
      have bound := size_body_peak initial vc state.data.items state.rank state.math.forest state.math.length state.math.weights a ready
        (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ (Proofs.CppMoveFrame.box state.data) ty ⟨writable,flag⟩ fields frame
        (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
      unfold budget at bound ⊢
      clear * - bound
      omega
    | unite a b =>
      have fields := qs_three initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) (b : Int) qs
      rw [state.size] at fields
      exact unite_body_peak initial vc state.data.items state.rank state.receiver.counter.value state.math a b ready.1 ready.2
        (receiverPrefix s) state.receiver.counter.address (prefix_cell s _ _ state.receiver.counter.found)
        (Proofs.CppMoveFrame.box state.data) ty ⟨writable,flag⟩ fields frame
        (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
    | groups =>
      have fields := qs_one initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value qs
      have bound := counter_body_peak initial vc state.data.items state.receiver.size.value state.receiver.counter.value
        (receiverPrefix s) state.receiver.counter.address (prefix_cell s _ _ state.receiver.counter.found) state.receiver.counter.valid
        (Proofs.CppMoveFrame.box state.data) ty fields frame (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
      unfold budget at bound ⊢
      clear * - bound
      omega
  have scalarResult : ∃ retType : Proofs.CppScalar.Ty, op.program.result = .scalar retType := by
    cases op <;> exact ⟨_,rfl⟩
  obtain ⟨retType,retEq⟩ := scalarResult
  rw [retEq] at finished
  have counters := Proofs.CppMovePreparedCall.restored_finish_counters s out i32 retType step.state after
    step.returned result finished restored state.covered
  have metadata := (compact_metadata (project prepared i32) initial compacted).2.2.1
  unfold budget at sharp
  rw [base,metadata] at sharp
  change step.state.scalars.peak ≤ max prepared.scalars.peak ((receiverPrefix s).length+100-s.scalars.baseMemory) at sharp
  refine ⟨prepared,prep,?_⟩
  rw [counters.1]
  clear * - sharp
  omega

end Proofs.UfObjectMethodScalarPeak
