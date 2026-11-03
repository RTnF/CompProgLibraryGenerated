import Proofs.BeatsWideCall
import Proofs.MultiVecOwnedSound

namespace Proofs.BeatsInlineFrame
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppMixedInvoke
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVector
open Proofs.MultiVecDynamic Proofs.MultiVec Proofs.BeatsPrepare Proofs.BeatsRep Proofs.BeatsExec
open Proofs.BeatsAllocation Proofs.BeatsAllocationArgs Proofs.QuotientFrame

-- These are the layout facts of a stage prepared with one vector argument.
-- Allocation owners and the scalar caller-memory prefix remain arbitrary.
structure Entry (st : Proofs.DynamicOwnedState.State) (p : Parameter) : Prop where
  input : p.slot = 0
  binding : st.nextBinding = 1
  slots : st.core.locals.slots.length = 1
  scalars : st.core.locals.bindings = []

def normalize (s : NState) : NState := Proofs.BeatsBindingCycle.view (Proofs.BeatsSlotCycle.permute s)

theorem binding_cycle (st : Proofs.DynamicOwnedState.State) (p : Parameter) (entry : Entry st p)
    (i : Nat) (bound : i < 16) : binding st p i = Proofs.BeatsSlotCycle.cycle i := by
  unfold binding Proofs.BeatsSlotCycle.cycle
  by_cases field : i < 15
  · simp only [ite_eq_left field,entry.binding]
    omega
  · have last : i = 15 := by omega
    subst i
    simp only [entry.input,ite_eq_right (by decide : ¬15 < 15),ite_true]

theorem normalized_frame (s : NState) (sl vb V vsc : Nat → Nat) (m : Bool)
    (buf : Nat → Buffer Value) (vv : Nat → List Int) (hv : CVecs s sl vb V vsc m buf vv)
    (count : s.frame.bindings.length = 16)
    (indices : ∀ i, i < 16 → vb i = Proofs.BeatsSlotCycle.cycle i) :
    (normalize s).frame = ⟨s.frame.state,s.frame.rootWritable,bl cty V vsc cw 0 16⟩ := by
  have table : Proofs.BeatsSlotCycle.rotate s.frame.bindings = bl cty V vsc cw 0 16 := by
    apply List.ext_getElem?
    intro i
    rw [Proofs.BeatsSlotCycle.rotate_lookup _ (by omega)]
    simp only [bl,← List.range_eq_range',List.getElem?_map]
    by_cases inside : i < 16
    · have original := (hv.ok i inside).binding
      rw [indices i inside] at original
      simpa only [List.getElem?_range inside,Option.map_some] using original
    · have fixed := Proofs.BeatsSlotCycle.cycle_ge i (by omega)
      rw [fixed,List.getElem?_eq_none_iff.mpr (by omega)]
      simp only [List.getElem?_eq_none_iff.mpr (show (List.range 16).length ≤ i by simpa only [List.length_range] using Nat.le_of_not_gt inside),Option.map_none]
  change ({s.frame with bindings := Proofs.BeatsSlotCycle.rotate s.frame.bindings} : Frame) = _
  rw [table]

theorem normalized_fwm (s : NState) (sl vb V vsc : Nat → Nat) (m : Bool)
    (buf : Nat → Buffer Value) (vv : Nat → List Int) (hv : CVecs s sl vb V vsc m buf vv)
    (count : s.frame.bindings.length = 16)
    (indices : ∀ i, i < 16 → vb i = Proofs.BeatsSlotCycle.cycle i) :
    FWM (mvCtor s V vsc m hv.dist) vv buf 0 (normalize s).frame := by
  have fw := fw_init s 16 (by decide) cty cw sl vb V vsc
    (fun i => if i < 15 then true else m) buf hv.ok
    (fun k h => by simp [cw] at h; simp [h])
    (fun j k hj hk different writable => hv.dist j k hj (by simpa [cw] using writable) different)
    vv hv.items hv.valid hv.limit hv.owner hv.small
  rw [← normalized_frame s sl vb V vsc m buf vv hv count indices] at fw
  exact fw

theorem allocated_slots {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (entry : Entry st p) (n : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s) :
    s.slots = (List.range 16).map Location.vector := by
  have slots := congrArg Proofs.DynamicExpr.Locals.slots real.data.locals
  change s.slots = (states st n 15).core.locals.slots at slots
  have length : s.slots.length = 16 := by rw [slots,states_slots,entry.slots]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  by_cases inside : i < 16
  · simp only [List.getElem?_range inside,Option.map_some]
    by_cases input : i = 0
    · subst i
      rw [slots]
      simpa only [entry.input] using (states_input h n 15).location
    · have bound : i-1 < 15 := by omega
      have field := (actual_field st n 15 s real (i-1) bound).2.2.1
      simpa only [entry.slots,entry.binding,show 1+(i-1) = i by omega] using field
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    simp only [List.getElem?_eq_none_iff.mpr (show (List.range 16).length ≤ i by simpa only [List.length_range] using Nat.le_of_not_gt inside),Option.map_none]

theorem normalized_slots (s : NState) (slots : s.slots = (List.range 16).map Location.vector) :
    (normalize s).slots = slN 16 0 := by
  change (Proofs.BeatsSlotCycle.rotate s.slots).map Proofs.BeatsBindingCycle.location = _
  rw [slots]
  decide

theorem states_memory (st : Proofs.DynamicOwnedState.State) (n k : Nat) :
    (states st n k).core.locals.memory = st.core.locals.memory := by
  induction k <;> simp only [states,Proofs.DynamicOwnedState.allocated,Proofs.DynamicConstructCore.appended, *]

theorem states_scalar_bindings (st : Proofs.DynamicOwnedState.State) (n k : Nat) :
    (states st n k).core.locals.bindings = st.core.locals.bindings := by
  induction k <;> simp only [states,Proofs.DynamicOwnedState.allocated,Proofs.DynamicConstructCore.appended, *]

theorem normalized_qs {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (entry : Entry st p) (n : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s) :
    QS (normalize s) [] s.scalars.baseMemory s.scope st.core.locals.memory [] (slN 16 0) := by
  have memory := congrArg Proofs.DynamicExpr.Locals.memory real.data.locals
  have bindings := congrArg Proofs.DynamicExpr.Locals.bindings real.data.locals
  change s.scalars.memory = (states st n 15).core.locals.memory at memory
  change s.scalars.bindings = (states st n 15).core.locals.bindings at bindings
  rw [states_memory] at memory
  rw [states_scalar_bindings,entry.scalars] at bindings
  exact ⟨normalized_slots s (allocated_slots h entry n s real),memory,bindings,rfl,rfl⟩

theorem prefix_environment {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (entry : Entry st p) (n : Nat) (length : a.length = n) (range : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ out, runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      Proofs.DynamicOwnedState.Realizes (states st n 15) out ∧
      out.frame.state.storage.work = s.frame.state.storage.work+Proofs.BeatsAllocationLayout.storageWork n 0 15 ∧
      ∃ hv : CVecs out (slot st) (binding st p) (owner st p) (scope st p) p.maximum (buffer st n buf) (VVA a (initial n)),
        FWM (mvCtor out (owner st p) (scope st p) p.maximum hv.dist) (VVA a (initial n)) (buffer st n buf) 0 (normalize out).frame ∧
        QS (normalize out) [] out.scalars.baseMemory out.scope st.core.locals.memory [] (slN 16 0) := by
  obtain ⟨out,ran,after,work,args⟩ := prefix_cvecs h n length range s real strict base buf stored readonly limit
  have count : out.frame.bindings.length = 16 := by rw [after.binding,states_binding,entry.binding]
  exact ⟨out,ran,after,work,args,normalized_fwm out _ _ _ _ _ _ _ args count (binding_cycle st p entry),
    normalized_qs h entry n out after⟩

end Proofs.BeatsInlineFrame
