import Proofs.SafeModFrame

namespace Proofs.SafeModInvoke
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppInvokePreparation
open Proofs.SafeModProofs Proofs.SafeModFrame

def valueParameters : List (Ty × Bool) :=
  SafeModInstance.safe_mod.parameters.map fun p => (p.type,p.writable)

theorem valueParameters_shape : valueParameters = [(signed64,true),(signed64,true)] := rfl

def preparedState (s : State) (arguments : List Expr) (x m : Int) : State :=
  {parameterState x m (callerPrefix s) (s.work+1+(arguments.map Expr.nodes).sum+2)
    (max (argumentPeak s arguments) ((callerPrefix s).length+2-s.baseMemory+2)) with
      baseMemory := s.baseMemory}

theorem prepare_exact (s : State) (arguments : List Expr) (x m : Int) (wx wm : Nat)
    (evaluated : arguments.mapM s.evaluate = some [⟨x,wx⟩,⟨m,wm⟩])
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) :
    prepareInvoke s valueParameters arguments = some (preparedState s arguments x m) := by
  have valid : (valueParameters.zip ([⟨x,wx⟩,⟨m,wm⟩] : List Result)).all
      (fun (p,v) => p.1.valid v.value) = true := by simp [valueParameters_shape,hx,hm]
  obtain ⟨callee,prepared⟩ := prepare_of_evaluated s valueParameters arguments [⟨x,wx⟩,⟨m,wm⟩]
    evaluated (by simp [valueParameters_shape]) valid
  obtain ⟨values,evaluated',_,memory,bindings,base,work,peak⟩ :=
    prepare_shape s valueParameters arguments callee prepared
  have same : values = [⟨x,wx⟩,⟨m,wm⟩] := Option.some.inj (evaluated'.symm.trans evaluated)
  subst values
  have shape : callee = preparedState s arguments x m := by
    cases callee
    simp only [preparedState,parameterState,State.mk.injEq]
    refine ⟨?_,?_,?_,base,?_⟩
    · simpa [valueParameters_shape,copiedCells] using memory
    · simpa [valueParameters_shape,copiedBindings,Nat.add_assoc] using bindings
    · simpa [valueParameters_shape] using work
    · simpa [valueParameters_shape] using peak
  rw [shape] at prepared
  exact prepared

theorem normalized_valid (x m : Int) (hm : signed64.valid m = true) (positive : 0 < m) :
    signed64.valid (x%m) = true := by
  have bm : -9223372036854775808 ≤ m ∧ m < 9223372036854775808 := of_decide_eq_true hm
  have low := Int.emod_nonneg x (by omega : m ≠ 0)
  have high := Int.emod_lt_of_pos x positive
  show decide (-9223372036854775808 ≤ x%m ∧ x%m < 9223372036854775808) = true
  apply decide_eq_true
  omega

theorem invoke_correct (s : State) (arguments : List Expr) (x m : Int) (wx wm : Nat)
    (evaluated : arguments.mapM s.evaluate = some [⟨x,wx⟩,⟨m,wm⟩])
    (allocated : s.baseMemory ≤ s.memory.length)
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) (positive : 0 < m) :
    ∃ peak : Nat,
      runFuel 10 (.invoke valueParameters signed64 arguments SafeModInstance.safe_mod.body) s =
        .finished ⟨{s with
          memory := s.memory ++ [⟨signed64,x%m⟩],
          bindings := s.bindings ++ [⟨s.memory.length,false⟩],
          work := s.work+(arguments.map Expr.nodes).sum+bodyWork x m+4,peak := peak},none,false⟩ ∧
      peak ≤ max (argumentPeak s arguments) (8+(callerPrefix s).length-s.baseMemory) ∧
      bodyWork x m ≤ 15 ∧ 0 ≤ x%m ∧ x%m < m := by
  have prepared := prepare_exact s arguments x m wx wm evaluated hx hm
  have prefixBound : s.baseMemory ≤ (callerPrefix s).length := by simp [callerPrefix]; omega
  have preparationBound : (callerPrefix s).length-s.baseMemory ≤ (preparedState s arguments x m).peak := by
    simp [preparedState,parameterState]
    omega
  have body := body_runs_withCallerBase x m (callerPrefix s)
    (preparedState s arguments x m).work (preparedState s arguments x m).peak s.baseMemory
    prefixBound preparationBound hx hm positive
  change runFuel 9 SafeModInstance.safe_mod.body (preparedState s arguments x m) = _ at body
  have invoked := invoke_composed 9 s (preparedState s arguments x m) valueParameters signed64 arguments
    SafeModInstance.safe_mod.body
    ⟨{parameterState (x%m) m (callerPrefix s)
      ((preparedState s arguments x m).work+bodyWork x m)
      (max (preparedState s arguments x m).peak (8+(callerPrefix s).length-s.baseMemory)) with
        baseMemory := s.baseMemory},some (x%m),false⟩
    (x%m) (bodyWork x m) prepared body rfl rfl (normalized_valid x m hm positive) rfl
  let finalPeak := max (max s.peak
    (max (preparedState s arguments x m).peak (8+(callerPrefix s).length-s.baseMemory)))
    (s.memory.length+1-s.baseMemory+s.bindings.length+1)
  refine ⟨finalPeak,?_,?_,bodyWork_bound x m,Int.emod_nonneg x (by omega),Int.emod_lt_of_pos x positive⟩
  · have total : 2+(2+bodyWork x m) = 4+bodyWork x m := by omega
    simpa [valueParameters_shape,State.observe,parameterState,finalPeak,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,total] using invoked
  · have callerPeak : s.peak ≤ argumentPeak s arguments := by
      have foldBound (xs : List Expr) (initial : Nat) : initial ≤ xs.foldl
          (fun peak e => max peak ((s.observe (arguments.length+e.nodes)).peak)) initial := by
        induction xs generalizing initial with
        | nil => exact Nat.le_refl _
        | cons e es ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      exact foldBound arguments s.peak
    simp [finalPeak,preparedState,parameterState,callerPrefix]
    simp [callerPrefix] at prefixBound
    omega

end Proofs.SafeModInvoke
