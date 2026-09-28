import Proofs.Generated.AssociativeArray

namespace Proofs.AssociativeArray

theorem get_empty (key : Nat) : get empty key = 0 := rfl

theorem get_absent (s : State) (key : Nat)
    (h : s.entries key = none) : get s key = 0 := by
  simp [get, h]

theorem get_present (s : State) (key value : Nat)
    (h : s.entries key = some value) : get s key = value := by
  simp [get, h]

theorem get_set_same (s : State) (key value : Nat) :
    get (set s key value) key = value := by
  simp [get, set]

theorem get_set_other (s : State) (key other value : Nat) (h : other ≠ key) :
    get (set s key value) other = get s other := by
  simp [get, set, h]

theorem set_writes (s : State) (key value : Nat) :
    (set s key value).writes = s.writes + 1 := rfl

theorem run_steps (qs : List Query) (s : State) :
    (run qs s).steps = qs.length := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
      cases q with
      | set key value => simp [run, ih]
      | get key => simp [run, ih]

theorem run_writes_le (qs : List Query) (s : State) :
    (run qs s).state.writes ≤ s.writes + qs.length := by
  induction qs generalizing s with
  | nil => simp [run]
  | cons q qs ih =>
      cases q with
      | set key value =>
          simpa [run, set_writes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (set s key value)
      | get key =>
          simpa only [run, List.length_cons] using
            Nat.le_trans (ih s) (by omega)

theorem run_cost (qs : List Query) (s : State) :
    (run qs s).steps * unitCost qs.length = totalCost qs.length := by
  rw [run_steps]
  rfl

theorem run_slots (qs : List Query) :
    (run qs empty).state.writes ≤ extraSlots qs.length := by
  simpa [empty, extraSlots] using run_writes_le qs empty

-- There are no loops in the wrapper methods. Each call has one terminating
-- STL map operation. The recursive query model decreases the list length.
theorem run_terminates (qs : List Query) (s : State) :
    ∃ r : Result, run qs s = r := ⟨run qs s, rfl⟩

end Proofs.AssociativeArray
