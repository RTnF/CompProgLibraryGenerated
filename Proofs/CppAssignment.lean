import Proofs.CppLoop

namespace Proofs.CppAssignment
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

-- Assignment checks the binding, its permission, the destination type and
-- expression before changing exactly one cell.
theorem assign_runs (s : State) (slot : Nat) (e : Expr) (binding : Binding)
    (cell : Cell) (result : Result) (value : Int)
    (hb : s.bindings[slot]? = some binding) (writable : binding.writable = true)
    (hc : s.memory[binding.address]? = some cell)
    (he : s.evaluate e = some result) (converted : cell.type.convert result.value = some value) :
    (Stmt.assign slot e).run s = some ⟨({s with
      memory := s.memory.set binding.address ⟨cell.type,value⟩,
      work := s.work+result.work+1}).observe e.nodes,none,false⟩ := by
  simp [Stmt.run,hb,writable,hc,he,converted]

theorem assign_runsFuel (fuel : Nat) (s : State) (slot : Nat) (e : Expr) (binding : Binding)
    (cell : Cell) (result : Result) (value : Int)
    (hb : s.bindings[slot]? = some binding) (writable : binding.writable = true)
    (hc : s.memory[binding.address]? = some cell)
    (he : s.evaluate e = some result) (converted : cell.type.convert result.value = some value) :
    runFuel (fuel+1) (.assign slot e) s = .finished ⟨({s with
      memory := s.memory.set binding.address ⟨cell.type,value⟩,
      work := s.work+result.work+1}).observe e.nodes,none,false⟩ := by
  simp only [runFuel,assign_runs s slot e binding cell result value hb writable hc he converted,liftChecked]

theorem assign_readonly (s : State) (slot : Nat) (e : Expr) (binding : Binding)
    (hb : s.bindings[slot]? = some binding) (readonly : binding.writable = false) :
    (Stmt.assign slot e).run s = none := by simp [Stmt.run,hb,readonly]

end Proofs.CppAssignment
