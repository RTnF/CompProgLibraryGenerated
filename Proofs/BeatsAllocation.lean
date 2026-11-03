import Proofs.BeatsWideExec
import Proofs.DynamicOwnedControl
import Proofs.DynamicFlatSound

namespace Proofs.BeatsAllocation
open Proofs.CppScalar Proofs.CppNestedProgram
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.MultiVecDynamic Proofs.DynamicOwnedState
open Proofs.DoublingNested (i32 u64)
open Proofs.IntSim (s64)
open Proofs.BeatsExec (wideCount conv_u64 u64_valid_nat)

def fieldTy (i : Nat) : Ty := if i < 9 then s64 else i32
def fieldCount (n i : Nat) : Nat := if 11 ≤ i ∧ i < 14 then 256 else 8*n+8
def fieldValue (i : Nat) : Int := if i=8 then 4000000000000000000 else 0
def countCode (i : Nat) : NExpr :=
  if 11 ≤ i ∧ i < 14 then .cast u64 (.literal i32 256) else wideCount 0
def valueCode (i : Nat) : NExpr :=
  if i < 9 then
    if i=8 then .literal s64 4000000000000000000 else .cast s64 (.literal i32 0)
  else .literal i32 0
def fieldStmt (i : Nat) : NStmt := .fillVector (fieldTy i) true (countCode i) (valueCode i)

def states (initial : State) (n : Nat) : Nat → State
  | 0 => initial
  | i+1 => allocated (states initial n i) (.integer (fieldTy i)) true
      (.flat (fieldTy i) (states initial n i).scope
        (List.replicate (fieldCount n i) (fieldValue i))) 1

theorem states_owner (st : State) (n k : Nat) : (states st n k).nextOwner = st.nextOwner+k := by
  induction k <;> simp [states,allocated, *, Nat.add_assoc]
theorem states_binding (st : State) (n k : Nat) : (states st n k).nextBinding = st.nextBinding+k := by
  induction k <;> simp [states,allocated, *, Nat.add_assoc]
theorem states_scope (st : State) (n k : Nat) : (states st n k).scope = st.scope := by
  induction k <;> simp [states,allocated, *]
theorem states_slots (st : State) (n k : Nat) :
    (states st n k).core.locals.slots.length = st.core.locals.slots.length+k := by
  induction k <;> simp [states,allocated,Proofs.DynamicConstructCore.appended, *, Nat.add_assoc]

structure Input (st : State) (p : Parameter) (a : List Int) : Prop where
  location : st.core.locals.slots[0]? = some (.vector p.slot)
  selected : st.params.find? (fun q => q.slot == p.slot) = some p
  contents : st.core.contents p.owner = some (.flat s64 p.scope a)
  fresh : p.owner < st.nextOwner
  element : p.element = .integer s64

theorem Input.allocated {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (ty : Ty) (count : Nat) (value : Int) :
    Input (allocated st (.integer ty) true (.flat ty st.scope (List.replicate count value)) 1) p a := by
  constructor
  · change (st.core.locals.slots++[_])[0]? = _
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h.location).1]
    exact h.location
  · change (st.params++[_]).find? (fun q => q.slot == p.slot) = some p
    rw [List.find?_append,h.selected]
    rfl
  · change putContents st.core.contents st.nextOwner _ p.owner = _
    have diff : p.owner ≠ st.nextOwner := Nat.ne_of_lt h.fresh
    simp only [putContents,ite_eq_right diff]
    exact h.contents
  · change p.owner < st.nextOwner+1
    have := h.fresh
    omega
  · exact h.element

theorem states_input {st : State} {p : Parameter} {a : List Int} (h : Input st p a) (n k : Nat) :
    Input (states st n k) p a := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.allocated (fieldTy k) (fieldCount n k) (fieldValue k)

theorem count_denote (params : List Parameter) (l : Locals) (h : ContentsHeap) (n : Nat)
    (small : 4*n < 2147483648)
    (size : denote params l h (.size (.integer s64) (.local 0)) = some (n : Int)) :
    denote params l h (wideCount 0) = some ((8*n+8 : Nat) : Int) := by
  have vn := u64_valid_nat n (by omega)
  have vm := u64_valid_nat (8*n) (by omega)
  have va := u64_valid_nat (8*n+8) (by omega)
  have cast : denote params l h (.cast u64 (.size (.integer s64) (.local 0))) = some (n : Int) := by
    change (denote params l h (.size (.integer s64) (.local 0))).bind u64.convert = _
    rw [size]
    exact conv_u64 _ vn
  have literal : denote params l h (.literal u64 8) = some 8 := rfl
  have mul : denote params l h (.binary u64 .mul (.literal u64 8)
      (.cast u64 (.size (.integer s64) (.local 0)))) = some ((8*n : Nat) : Int) := by
    change (denote params l h (.literal u64 8)).bind
      (fun a => (denote params l h (.cast u64 (.size (.integer s64) (.local 0)))).bind
        (fun b => u64.convert (binaryValue .mul a b))) = _
    rw [literal,Option.bind_some,cast,Option.bind_some]
    exact conv_u64 _ vm
  have add : denote params l h (.binary u64 .add
      (.binary u64 .mul (.literal u64 8) (.cast u64 (.size (.integer s64) (.local 0))))
      (.literal u64 8)) = some ((8*n+8 : Nat) : Int) := by
    change (denote params l h (.binary u64 .mul (.literal u64 8)
      (.cast u64 (.size (.integer s64) (.local 0))))).bind
      (fun a => (denote params l h (.literal u64 8)).bind
        (fun b => u64.convert (binaryValue .add a b))) = _
    rw [mul,Option.bind_some,literal,Option.bind_some]
    exact conv_u64 _ va
  change (denote params l h (.binary u64 .add
      (.binary u64 .mul (.literal u64 8) (.cast u64 (.size (.integer s64) (.local 0))))
      (.literal u64 8))).bind u64.convert = _
  rw [add]
  exact conv_u64 _ va

theorem input_count {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) (i : Nat) :
    denote st.params st.core.locals st.core.contents (countCode i) = some (fieldCount n i : Int) := by
  by_cases stack : 11 ≤ i ∧ i < 14
  · simp only [countCode,fieldCount,ite_eq_left stack]
    rfl
  · simp only [countCode,fieldCount,ite_eq_right stack]
    apply count_denote _ _ _ n small
    have size := size_root st.params st.core.locals st.core.contents 0 p (.flat s64 p.scope a)
      h.location h.selected h.contents h.element.symm rfl
    have valid := u64_valid_nat n (by omega)
    simpa only [Contents.element,Contents.length,length,ite_eq_left valid] using size

theorem input_value (st : State) (i : Nat) :
    denote st.params st.core.locals st.core.contents (valueCode i) = some (fieldValue i) := by
  by_cases long : i < 9
  · by_cases inf : i=8
    · simp only [valueCode,fieldValue,ite_eq_left long,ite_eq_left inf]
      rfl
    · simp only [valueCode,fieldValue,ite_eq_left long,ite_eq_right inf]
      rfl
  · have inf : i≠8 := by omega
    simp only [valueCode,fieldValue,ite_eq_right long,ite_eq_right inf]
    rfl

theorem field_supported (i : Nat) : Proofs.CppVectorBindings.supported (fieldTy i) := by
  unfold fieldTy
  split <;> decide
theorem field_valid (i : Nat) : (fieldTy i).valid (fieldValue i) = true := by
  by_cases inf : i=8
  · subst i
    decide
  · simp only [fieldValue,ite_eq_right inf,fieldTy]
    split <;> decide
theorem field_limit (n i : Nat) (small : 4*n < 2147483648) :
    fieldCount n i ≤ Proofs.CppVectorBindings.sizeLimit (fieldTy i) := by
  unfold fieldCount fieldTy
  split <;> split <;> norm_num [Proofs.CppVectorBindings.sizeLimit,s64,i32] <;> omega

theorem field_construct {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) (i : Nat) :
    runConstruct (fieldStmt i) st = some
      (allocated st (.integer (fieldTy i)) true
        (.flat (fieldTy i) st.scope (List.replicate (fieldCount n i) (fieldValue i))) 1) := by
  have count := input_count h n length small i
  have value := input_value st i
  simp [fieldStmt,runConstruct,count,value,field_supported,field_limit n i small,field_valid]

theorem states_field (st : State) (n k j : Nat) (bound : j < k) :
    (states st n k).core.contents (st.nextOwner+j) =
      some (.flat (fieldTy j) st.scope (List.replicate (fieldCount n j) (fieldValue j))) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : j=k
    · subst j
      simp [states,allocated,putContents,states_owner,states_scope]
    · have earlier : j < k := by omega
      have diff : st.nextOwner+j ≠ (states st n k).nextOwner := by rw [states_owner]; omega
      change putContents (states st n k).core.contents (states st n k).nextOwner _ (st.nextOwner+j) = _
      rw [putContents,ite_eq_right diff]
      exact ih earlier

def fillPrefix (i : Nat) : Nat → Command
  | 0 => .primitive .skip
  | count+1 => .sequence (.primitive (fieldStmt i)) (fillPrefix (i+1) count)

theorem prefix_pure {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) :
    ∀ count i, Proofs.DynamicOwnedControl.runFuel (count+1) (fillPrefix i count) (states st n i) =
      .finished ⟨states st n (i+count),none,false⟩ := by
  intro count
  induction count with
  | zero => intro i; rfl
  | succ count ih =>
    intro i
    have step := field_construct (states_input h n i) n length small i
    have head : Proofs.DynamicOwnedControl.runFuel (count+1) (.primitive (fieldStmt i)) (states st n i) =
        .finished ⟨states st n (i+1),none,false⟩ := by
      simp only [Proofs.DynamicOwnedControl.runFuel,Proofs.DynamicOwnedControl.primitive,fieldStmt]
      change Proofs.CppLoop.liftChecked ((runConstruct (fieldStmt i) (states st n i)).bind _) = _
      rw [step]
      rfl
    change (do
      let first ← Proofs.DynamicOwnedControl.runFuel (count+1) (.primitive (fieldStmt i)) (states st n i)
      if first.returned.isSome || first.breaking then pure first
      else Proofs.DynamicOwnedControl.runFuel (count+1) (fillPrefix (i+1) count) first.state) = _
    rw [head]
    simpa only [Bind.bind,Proofs.CppLoop.Outcome.bind,Bool.false_or,Option.isSome_none,Bool.false_eq_true,ite_false,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1)

theorem prefix_actual {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s) :
    ∃ r : NStep, CppNestedProgram.runFuel 16 (fillPrefix 0 15) s = .finished r ∧
      Proofs.DynamicOwnedState.Realizes (states st n 15) r.state ∧
      r.returned = none ∧ r.breaking = false ∧
      r.state.slots.length = st.core.locals.slots.length+15 ∧
      r.state.frame.state.storage.objects.length = st.nextOwner+15 ∧
      r.state.frame.bindings.length = st.nextBinding+15 := by
  obtain ⟨r,ran,matched⟩ := Proofs.DynamicOwnedControl.sound 16 (fillPrefix 0 15) st s real
    ⟨states st n 15,none,false⟩ (prefix_pure h n length small 15 0)
  refine ⟨r,ran,matched.state,matched.returned,matched.breaking,?_,?_,?_⟩
  · have slots := congrArg (fun l : Locals => l.slots.length) matched.state.data.locals
    exact slots.trans (states_slots st n 15)
  · exact matched.state.owner.trans (states_owner st n 15)
  · exact matched.state.binding.trans (states_binding st n 15)

def fieldParameter (st : State) (j : Nat) : Parameter :=
  ⟨st.nextBinding+j,st.nextOwner+j,.integer (fieldTy j),st.scope,true,true⟩

theorem states_param_length (st : State) (n k : Nat) :
    (states st n k).params.length = st.params.length+k := by
  induction k <;> simp [states,allocated, *, Nat.add_assoc]

theorem states_parameter (st : State) (n k j : Nat) (bound : j < k) :
    (states st n k).params[st.params.length+j]? = some (fieldParameter st j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : j=k
    · subst j
      change ((states st n k).params++[_])[st.params.length+k]? = _
      rw [← states_param_length st n k,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      simp only [List.getElem?_cons_zero,newParameter,states_owner,states_binding,states_scope,fieldParameter]
    · have earlier : j < k := by omega
      change ((states st n k).params++[_])[st.params.length+j]? = _
      rw [List.getElem?_append_left (by rw [states_param_length]; omega)]
      exact ih earlier

theorem states_slot (st : State) (n k j : Nat) (bound : j < k) :
    (states st n k).core.locals.slots[st.core.locals.slots.length+j]? =
      some (.vector (st.nextBinding+j)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : j=k
    · subst j
      change ((states st n k).core.locals.slots++[_])[st.core.locals.slots.length+k]? = _
      rw [← states_slots st n k,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      simp only [List.getElem?_cons_zero,states_binding]
    · have earlier : j < k := by omega
      change ((states st n k).core.locals.slots++[_])[st.core.locals.slots.length+j]? = _
      rw [List.getElem?_append_left (by rw [states_slots]; omega)]
      exact ih earlier

theorem actual_field (st : State) (n k : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n k) s) (j : Nat) (bound : j < k) :
    Proofs.CppRootModel.Flat s.frame.state (st.nextOwner+j) (fieldTy j) st.scope
      (List.replicate (fieldCount n j) (fieldValue j)) ∧
    s.frame.bindings[st.nextBinding+j]? = some ⟨st.nextOwner+j,.integer (fieldTy j),true,.root st.scope⟩ ∧
    s.slots[st.core.locals.slots.length+j]? = some (.vector (st.nextBinding+j)) ∧
    s.frame.rootWritable[st.nextOwner+j]? = some true := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have found := states_field st n k j bound
  have hv := Proofs.DynamicFlatSound.flat_lift h (st.nextOwner+j) (fieldTy j) st.scope
    (List.replicate (fieldCount n j) (fieldValue j)) (by rw [erased]; exact found)
  have member := List.mem_of_getElem? (states_parameter st n k j bound)
  refine ⟨family.models _ _ hv,?_,?_,?_⟩
  · simpa only [fieldParameter,Parameter.binding] using family.bindings (fieldParameter st j) member
  · have slots := congrArg Locals.slots real.data.locals
    change s.slots = (states st n k).core.locals.slots at slots
    rw [slots]
    exact states_slot st n k j bound
  · exact family.flags (fieldParameter st j) member

theorem actual_input {st : State} {p : Parameter} {a : List Int} (h : Input st p a)
    (n k : Nat) (s : NState) (real : Proofs.DynamicOwnedState.Realizes (states st n k) s) :
    Proofs.CppRootModel.Flat s.frame.state p.owner s64 p.scope a := by
  obtain ⟨heap,m,family,erased⟩ := real.data.heap
  have hv := Proofs.DynamicFlatSound.flat_lift heap p.owner s64 p.scope a
    (by rw [erased]; exact (states_input h n k).contents)
  exact family.models _ _ hv

theorem input_of_real (st : State) (p : Parameter) (a : List Int) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes st s)
    (location : st.core.locals.slots[0]? = some (.vector p.slot))
    (selected : st.params.find? (fun q => q.slot == p.slot) = some p)
    (contents : st.core.contents p.owner = some (.flat s64 p.scope a))
    (element : p.element = .integer s64) : Input st p a := by
  refine ⟨location,selected,contents,?_,element⟩
  obtain ⟨heap,m,family,erased⟩ := real.data.heap
  have hv := Proofs.DynamicFlatSound.flat_lift heap p.owner s64 p.scope a (by rw [erased]; exact contents)
  have bound := Proofs.CppRootModel.Models.bound (family.models _ _ hv)
  simpa only [real.owner] using bound

end Proofs.BeatsAllocation
