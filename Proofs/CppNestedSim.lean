import Proofs.CppNestedFacts

namespace Proofs.CppNestedSim
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppLoop

-- Projection lemmas: counters (work / peak) never influence core fields, so
-- state shapes can be stated on core fields only and counters bounded apart.

section projections
variable (s : NState) (work temporaries : Nat)

@[simp] theorem charge_frame : (s.charge work temporaries).frame = s.frame := rfl
@[simp] theorem charge_slots : (s.charge work temporaries).slots = s.slots := rfl
@[simp] theorem charge_scope : (s.charge work temporaries).scope = s.scope := rfl
@[simp] theorem charge_memory : (s.charge work temporaries).scalars.memory = s.scalars.memory := rfl
@[simp] theorem charge_bindings : (s.charge work temporaries).scalars.bindings = s.scalars.bindings := rfl
@[simp] theorem charge_baseMemory : (s.charge work temporaries).scalars.baseMemory = s.scalars.baseMemory := rfl
@[simp] theorem observe_frame : s.observe.frame = s.frame := rfl
@[simp] theorem observe_slots : s.observe.slots = s.slots := rfl
@[simp] theorem observe_scope : s.observe.scope = s.scope := rfl
@[simp] theorem observe_scalars : s.observe.scalars = s.scalars := rfl
@[simp] theorem release_slots (before : NState) : (s.release before).slots = s.slots := rfl
@[simp] theorem release_scope (before : NState) : (s.release before).scope = s.scope := rfl
@[simp] theorem release_scalars (before : NState) : (s.release before).scalars = s.scalars := rfl
@[simp] theorem release_state (before : NState) : (s.release before).frame.state = s.frame.state := rfl
@[simp] theorem release_rootWritable (before : NState) :
    (s.release before).frame.rootWritable = s.frame.rootWritable := rfl
@[simp] theorem release_bindings (before : NState) :
    (s.release before).frame.bindings = s.frame.bindings.take before.frame.bindings.length := rfl
end projections

@[simp] theorem charge_state (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).frame.state = s.frame.state := rfl
@[simp] theorem charge_frame_bindings (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).frame.bindings = s.frame.bindings := rfl

theorem charge_work (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).scalars.work = s.scalars.work+work := rfl

-- The scalar peak after a charge is the larger of the old peak and the live cells.
theorem charge_scalar_peak (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).scalars.peak = max s.scalars.peak
      (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length+temporaries) := rfl

theorem charge_peak (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).peak = max s.peak
      (max s.scalars.peak (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length+temporaries)
        +s.frame.state.storage.peak) := rfl

theorem charge_storage (s : NState) (work temporaries : Nat) :
    (s.charge work temporaries).frame.state.storage = s.frame.state.storage := rfl

@[simp] theorem release_peak (s before : NState) : (s.release before).peak = s.peak := rfl

-- The outer peak after a final charge of a statement that released its temporaries.
theorem charge_release_peak (x before : NState) (work temporaries : Nat) :
    ((x.release before).charge work temporaries).peak =
      max x.peak (((x.release before).charge work temporaries).scalars.peak + x.frame.state.storage.peak) := by
  simp only [charge_peak,charge_scalar_peak,release_scalars,release_peak,release_state]

end Proofs.CppNestedSim
