import Proofs.BeatsAllocation
import Proofs.MatMulPrepare

namespace Proofs.BeatsAllocationLayout
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedConstruct Proofs.CppNestedEval Proofs.CppNestedStmt
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicContents Proofs.MultiVecDynamic
open Proofs.DynamicResultValid

theorem fill_layout (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (s out : NState) (real : Realizes params l h s) (ty : Ty) (wr : Bool)
    (count value : NExpr) (n x : Int)
    (countPure : denote params l h count = some n)
    (valuePure : denote params l h value = some x)
    (actual : (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩) :
    out.frame.state.storage.objects = s.frame.state.storage.objects ++
      [some ⟨s.frame.state.storage.objects.length,List.replicate n.toNat (Value.integer x),
        n.toNat,Proofs.CppVectorBindings.sizeLimit ty,0⟩] ∧
    out.frame.state.forest = s.frame.state.forest.declareRoot ty s.scope ∧
    out.frame.state.storage.work = s.frame.state.storage.work+n.toNat+1 ∧
    out.scalars.memory = s.scalars.memory ∧ out.scalars.bindings = s.scalars.bindings ∧ out.scope = s.scope ∧
    out.scalars.baseMemory = s.scalars.baseMemory := by
  obtain ⟨_,t1,extra1,ev1⟩ := Proofs.DynamicExprCertified.sound
    (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready _ _ _ _) n countPure) s real
  have real1 := Proofs.DynamicExprCompose.in_extension params l h s t1 real (Ext.of_goodF ev1.2.1 ev1.2.2)
  obtain ⟨_,t2,extra2,ev2⟩ := Proofs.DynamicExprCertified.sound
    (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready _ _ _ _) x valuePure) t1 real1
  have good := ev1.2.1.trans ev2.2.1
  let released := t2.release s
  simp only [NStmt.run,ev1.1,Bind.bind,Option.bind,ev2.1] at actual
  split at actual
  · change (released.frame.state.fillVector ty released.scope n.toNat x).bind _ = _ at actual
    obtain ⟨next,allocated,tail⟩ := bind_some _ _ _ actual
    obtain ⟨pair,bound,final⟩ := bind_some _ _ _ tail
    obtain ⟨frame,binding⟩ := pair
    have defined : out = ({released with frame := frame,slots := released.slots++[.vector binding]} : NState).charge 3 0 := by
      exact (congrArg NStep.state (Option.some.inj final)).symm
    have frameState := (Proofs.DynamicOwnedLayout.bind_root _ frame _ _ _ wr binding bound).1
    have outState : out.frame.state = next := by rw [defined]; exact frameState
    obtain ⟨_,_,_,_,nextEq⟩ := fillVector_inv released.frame.state ty released.scope n.toNat x next allocated
    obtain ⟨state,rights,slots,scope,memory,bindings,base,rest⟩ := good
    have rs : released.frame.state = s.frame.state := state
    have sc : released.scope = s.scope := scope
    rw [rs,sc] at nextEq
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [outState,nextEq]
    · rw [outState,nextEq]
    · rw [outState,nextEq]
      dsimp only
      omega
    · rw [defined]
      exact memory
    · rw [defined]
      exact bindings
    · rw [defined]
      exact scope
    · rw [defined]
      exact base
  · simp at actual

open Proofs.BeatsAllocation

-- Classify the final root, rather than recursively unfolding context through
-- every ancestor. This also covers old descendants and missing owners.
theorem declareRoot_strict (f : Forest) (ty : Ty) (scope : Nat)
    (strict : ∀ owner c, f.context owner = some c → c ≤ scope) :
    ∀ owner c, (f.declareRoot ty scope).context owner = some c → c ≤ scope := by
  intro owner c context
  unfold Forest.context at context
  obtain ⟨root,rooted,tail⟩ := bind_some _ _ _ context
  obtain ⟨tag,found,last⟩ := bind_some _ _ _ tail
  have parent := (rootOwner_is_root _ owner root rooted)
  obtain ⟨origin,originFound,originParent⟩ := parent
  have same : origin = tag := Option.some.inj (originFound.symm.trans found)
  subst origin
  by_cases old : root < f.objects.length
  · have oldFound : f.lookup root = some tag := by
      rw [declareRoot_old f ty scope root old] at found
      exact found
    exact strict root c (by simp only [Forest.context,root_runs f root tag oldFound originParent,
      Bind.bind,Option.bind_some,oldFound,last])
  · by_cases fresh : root = f.objects.length
    · subst root
      rw [declareRoot_new] at found
      cases found
      exact Nat.le_of_eq (Option.some.inj last).symm
    · have past : (f.declareRoot ty scope).objects.length ≤ root := by
        rw [declareRoot_length]
        omega
      rw [lookup_past_end _ root past] at found
      contradiction

def fieldBuffer (st : Proofs.DynamicOwnedState.State) (n i : Nat) : Proofs.CppVector.Buffer Value :=
  ⟨st.nextOwner+i,List.replicate (fieldCount n i) (Value.integer (fieldValue i)),
    fieldCount n i,Proofs.CppVectorBindings.sizeLimit (fieldTy i),0⟩

def bufferList (st : Proofs.DynamicOwnedState.State) (n i : Nat) : Nat → List (Option (Proofs.CppVector.Buffer Value))
  | 0 => []
  | count+1 => some (fieldBuffer st n i)::bufferList st n (i+1) count

def storageWork (n i : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => fieldCount n i+1+storageWork n (i+1) count

theorem prefix_layout {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) :
    ∀ count i (s : NState), Proofs.DynamicOwnedState.Realizes (states st n i) s →
      ∃ out, CppNestedProgram.runFuel (count+1) (fillPrefix i count) s = .finished ⟨out,none,false⟩ ∧
        Proofs.DynamicOwnedState.Realizes (states st n (i+count)) out ∧
        out.frame.state.storage.objects = s.frame.state.storage.objects++bufferList st n i count ∧
        out.frame.state.storage.work = s.frame.state.storage.work+storageWork n i count := by
  intro count
  induction count with
  | zero =>
    intro i s real
    exact ⟨s,rfl,real,by simp [bufferList],by simp [storageWork]⟩
  | succ count ih =>
    intro i s real
    have input := states_input h n i
    have construct := field_construct input n length small i
    obtain ⟨mid,head,after⟩ := Proofs.DynamicOwnedConstruct.sound (states st n i) s real (fieldStmt i)
      (states st n (i+1)) construct
    have layout := fill_layout _ _ _ s mid real.data (fieldTy i) true (countCode i) (valueCode i)
      (fieldCount n i) (fieldValue i) (input_count input n length small i) (input_value _ i) head
    have objects : mid.frame.state.storage.objects = s.frame.state.storage.objects++[some (fieldBuffer st n i)] := by
      simpa only [real.owner,states_owner,Int.toNat_natCast,fieldBuffer] using layout.1
    have work : mid.frame.state.storage.work = s.frame.state.storage.work+fieldCount n i+1 := by
      simpa only [Int.toNat_natCast] using layout.2.2.1
    obtain ⟨out,tail,final,bufferEq,workEq⟩ := ih (i+1) mid after
    refine ⟨out,?_,?_,?_,?_⟩
    · have first : CppNestedProgram.runFuel (count+1) (.primitive (fieldStmt i)) s = .finished ⟨mid,none,false⟩ := by
        simp [CppNestedProgram.runFuel,head,Proofs.CppLoop.liftChecked]
      change (do
        let step ← CppNestedProgram.runFuel (count+1) (.primitive (fieldStmt i)) s
        if step.returned.isSome || step.breaking then pure step
        else CppNestedProgram.runFuel (count+1) (fillPrefix (i+1) count) step.state) = _
      rw [first]
      simpa only [Bind.bind,Proofs.CppLoop.Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false] using tail
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
    · rw [bufferEq,objects]
      simp only [bufferList,List.append_assoc,List.singleton_append]
    · rw [workEq,work]
      simp only [storageWork]
      omega

theorem prefix_conditions {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) :
    ∀ count i (s : NState), Proofs.DynamicOwnedState.Realizes (states st n i) s →
      (∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope) →
      s.scalars.baseMemory ≤ s.scalars.memory.length →
      ∃ out, CppNestedProgram.runFuel (count+1) (fillPrefix i count) s = .finished ⟨out,none,false⟩ ∧
        (∀ owner c, out.frame.state.forest.context owner = some c → c ≤ out.scope) ∧
        out.scalars.baseMemory ≤ out.scalars.memory.length := by
  intro count
  induction count with
  | zero =>
    intro i s _ strict base
    exact ⟨s,rfl,strict,base⟩
  | succ count ih =>
    intro i s real strict base
    have input := states_input h n i
    obtain ⟨mid,head,after⟩ := Proofs.DynamicOwnedConstruct.sound (states st n i) s real (fieldStmt i)
      (states st n (i+1)) (field_construct input n length small i)
    have layout := fill_layout _ _ _ s mid real.data (fieldTy i) true (countCode i) (valueCode i)
      (fieldCount n i) (fieldValue i) (input_count input n length small i) (input_value _ i) head
    obtain ⟨_,forest,_,memory,_,scope,baseMemory⟩ := layout
    have midStrict : ∀ owner c, mid.frame.state.forest.context owner = some c → c ≤ mid.scope := by
      rw [forest,scope]
      exact declareRoot_strict _ _ _ strict
    have midBase : mid.scalars.baseMemory ≤ mid.scalars.memory.length := by
      rw [baseMemory,memory]
      exact base
    obtain ⟨out,tail,outStrict,outBase⟩ := ih (i+1) mid after midStrict midBase
    refine ⟨out,?_,outStrict,outBase⟩
    have first : CppNestedProgram.runFuel (count+1) (.primitive (fieldStmt i)) s = .finished ⟨mid,none,false⟩ := by
      simp [CppNestedProgram.runFuel,head,Proofs.CppLoop.liftChecked]
    change (do
      let step ← CppNestedProgram.runFuel (count+1) (.primitive (fieldStmt i)) s
      if step.returned.isSome || step.breaking then pure step
      else CppNestedProgram.runFuel (count+1) (fillPrefix (i+1) count) step.state) = _
    rw [first]
    simpa only [Bind.bind,Proofs.CppLoop.Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false] using tail

theorem storageWork_fifteen (n : Nat) : storageWork n 0 15 = 12*(8*n+8)+783 := by
  norm_num [storageWork,fieldCount]
  omega

theorem bufferList_get (st : Proofs.DynamicOwnedState.State) (n i count j : Nat) (bound : j < count) :
    (bufferList st n i count)[j]? = some (some (fieldBuffer st n (i+j))) := by
  induction count generalizing i j with
  | zero => omega
  | succ count ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [bufferList,List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using ih (i+1) j (by omega)

theorem buffer_at (st : Proofs.DynamicOwnedState.State) (n : Nat) (s out : NState)
    (owner : s.frame.state.storage.objects.length = st.nextOwner)
    (objects : out.frame.state.storage.objects = s.frame.state.storage.objects++bufferList st n 0 15)
    (j : Nat) (bound : j < 15) :
    out.frame.state.storage.lookup (st.nextOwner+j) = some (fieldBuffer st n j) := by
  change (out.frame.state.storage.objects[st.nextOwner+j]?).join = _
  rw [objects,List.getElem?_append_right (by omega),owner,Nat.add_sub_cancel_left]
  rw [bufferList_get st n 0 15 j bound]
  simp

theorem old_buffer (st : Proofs.DynamicOwnedState.State) (n : Nat) (s out : NState)
    (owner : s.frame.state.storage.objects.length = st.nextOwner)
    (objects : out.frame.state.storage.objects = s.frame.state.storage.objects++bufferList st n 0 15)
    (j : Nat) (bound : j < st.nextOwner) :
    out.frame.state.storage.lookup j = s.frame.state.storage.lookup j := by
  change (out.frame.state.storage.objects[j]?).join = (s.frame.state.storage.objects[j]?).join
  rw [objects,List.getElem?_append_left (by omega)]

theorem field_argument (st : Proofs.DynamicOwnedState.State) (n : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s)
    (buffers : ∀ j, j < 15 → s.frame.state.storage.lookup (st.nextOwner+j) = some (fieldBuffer st n j))
    (strict : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) (j : Nat) (bound : j < 15) :
    Proofs.MatMulPrepare.VOKG s (fieldTy j) (st.core.locals.slots.length+j) (st.nextBinding+j)
      (st.nextOwner+j) st.scope true true (fieldBuffer st n j) ∧
    (fieldBuffer st n j).Valid (accepts (.integer (fieldTy j))) ∧
    (fieldBuffer st n j).limit = Proofs.CppVectorBindings.sizeLimit (fieldTy j) ∧
    (fieldBuffer st n j).owner = st.nextOwner+j := by
  obtain ⟨model,binding,slot,flag⟩ := actual_field st n 15 s real j bound
  obtain ⟨h,m,family,_⟩ := real.data.heap
  have stored := buffers j bound
  have object := Proofs.CppNestedVectorBindings.object_runs s.frame (st.nextOwner+j) (.integer (fieldTy j))
    (fieldBuffer st n j) _ model.valid stored model.tag rfl
  have facts := Proofs.CppNestedRows.buffer_facts s.frame (st.nextOwner+j) (fieldTy j) (fieldBuffer st n j) _ object
  refine ⟨⟨model.valid,?_,binding,model.tag,stored,family.lengths,flag,(fun _ => rfl),strict,base⟩,
    facts.2.2.1,rfl,rfl⟩
  simp [NState.vectorSlot,slot]

theorem input_argument {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n k : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n k) s)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    Proofs.MatMulPrepare.VOKG s Proofs.IntSim.s64 0 p.slot p.owner p.scope p.writable p.maximum buf ∧
    buf.Valid (accepts (.integer Proofs.IntSim.s64)) ∧ buf.items = a.map Value.integer ∧ buf.owner = p.owner := by
  have input := states_input h n k
  have model := actual_input h n k s real
  obtain ⟨heap,m,family,_⟩ := real.data.heap
  have member := List.mem_of_find?_eq_some input.selected
  have object := Proofs.CppNestedVectorBindings.object_runs s.frame p.owner (.integer Proofs.IntSim.s64)
    buf _ model.valid stored model.tag rfl
  have facts := Proofs.CppNestedRows.buffer_facts s.frame p.owner Proofs.IntSim.s64 buf _ object
  obtain ⟨original,found,items⟩ := model.buffer
  have same : original = buf := Option.some.inj (found.symm.trans stored)
  subst original
  refine ⟨⟨model.valid,?_,?_,model.tag,stored,family.lengths,family.flags p member,
    family.permissions p member,strict,base⟩,facts.2.2.1,items,facts.2.1⟩
  · exact Proofs.DynamicSizeSound.vector_slot _ _ _ s real.data 0 p.slot input.location
  · simpa only [Parameter.binding,input.element] using family.bindings p member

-- All caller conditions here are required only before allocation. In
-- particular, no condition on the completed prefix is assumed.
theorem prefix_arguments {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf) :
    ∃ out, CppNestedProgram.runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      Proofs.DynamicOwnedState.Realizes (states st n 15) out ∧
      out.frame.state.storage.objects = s.frame.state.storage.objects++bufferList st n 0 15 ∧
      out.frame.state.storage.work = s.frame.state.storage.work+storageWork n 0 15 ∧
      (∀ j, j < 15 → Proofs.MatMulPrepare.VOKG out (fieldTy j) (st.core.locals.slots.length+j)
        (st.nextBinding+j) (st.nextOwner+j) st.scope true true (fieldBuffer st n j)) ∧
      Proofs.MatMulPrepare.VOKG out Proofs.IntSim.s64 0 p.slot p.owner p.scope p.writable p.maximum buf := by
  obtain ⟨out,ran,after,objects,work⟩ := prefix_layout h n length small 15 0 s real
  obtain ⟨ready,readyRun,readyStrict,readyBase⟩ := prefix_conditions h n length small 15 0 s real strict base
  have same : ready = out := congrArg NStep.state (Proofs.CppLoop.Outcome.finished.inj (readyRun.symm.trans ran))
  subst ready
  refine ⟨out,ran,after,objects,work,?_,?_⟩
  · intro j bound
    exact (field_argument st n out after (fun j bound => buffer_at st n s out real.owner objects j bound)
      readyStrict readyBase j bound).1
  · have preserved := old_buffer st n s out real.owner objects p.owner h.fresh
    exact (input_argument h n 15 out after buf (preserved.trans stored) readyStrict readyBase).1

end Proofs.BeatsAllocationLayout
