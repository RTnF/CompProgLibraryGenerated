import Proofs.FloorSumWorkFrame

namespace Proofs.FloorSumInvoke
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppInvokePreparation
open Proofs.FloorSumArithmetic Proofs.FloorSumState Proofs.FloorSumCall Proofs.FloorSumWorkFrame

def valueParameters : List (Ty × Bool) :=
  FloorSumUnsignedInstance.floor_sum_unsigned.parameters.map fun p => (p.type,p.writable)

theorem valueParameters_shape : valueParameters =
    [(unsigned64,true),(unsigned64,true),(unsigned64,true),(unsigned64,true)] := rfl

def preparedState (s : State) (arguments : List Expr) (n m a b : Nat) : State :=
  {parameterState n m a b (callerPrefix s) with
    work := s.work+1+(arguments.map Expr.nodes).sum+4,
    baseMemory := s.baseMemory,
    peak := max (argumentPeak s arguments) ((callerPrefix s).length+4-s.baseMemory+4)}

theorem prepare_exact (s : State) (arguments : List Expr) (n m a b wn wm wa wb : Nat)
    (evaluated : arguments.mapM s.evaluate = some [⟨n,wn⟩,⟨m,wm⟩,⟨a,wa⟩,⟨b,wb⟩])
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit) (hb : b < wordLimit) :
    prepareInvoke s valueParameters arguments = some (preparedState s arguments n m a b) := by
  have valid : (valueParameters.zip ([⟨n,wn⟩,⟨m,wm⟩,⟨a,wa⟩,⟨b,wb⟩] : List Result)).all
      (fun (p,v) => p.1.valid v.value) = true := by
    simp [valueParameters_shape,unsigned64_valid n hn,unsigned64_valid m hm,
      unsigned64_valid a ha,unsigned64_valid b hb]
  obtain ⟨callee,prepared⟩ := prepare_of_evaluated s valueParameters arguments
    [⟨n,wn⟩,⟨m,wm⟩,⟨a,wa⟩,⟨b,wb⟩] evaluated (by simp [valueParameters_shape]) valid
  obtain ⟨values,evaluated',_,memory,bindings,base,work,peak⟩ :=
    prepare_shape s valueParameters arguments callee prepared
  have same : values = [⟨n,wn⟩,⟨m,wm⟩,⟨a,wa⟩,⟨b,wb⟩] := Option.some.inj (evaluated'.symm.trans evaluated)
  subst values
  have shape : callee = preparedState s arguments n m a b := by
    cases callee
    simp only [preparedState,parameterState,State.mk.injEq]
    refine ⟨?_,?_,?_,base,?_⟩
    · simpa [valueParameters_shape,copiedCells] using memory
    · simpa [valueParameters_shape,copiedBindings,Nat.add_assoc] using bindings
    · simpa [valueParameters_shape] using work
    · simpa [valueParameters_shape] using peak
  rw [shape] at prepared
  exact prepared

theorem fold_max_ge (xs : List α) (f : α → Nat) (initial : Nat) :
    initial ≤ xs.foldl (fun peak x => max peak (f x)) initial := by
  induction xs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      exact Nat.le_trans (Nat.le_max_left initial (f x)) (ih (max initial (f x)))

theorem argumentPeak_ge (s : State) (arguments : List Expr) : s.peak ≤ argumentPeak s arguments :=
  fold_max_ge arguments (fun e => (s.observe (arguments.length+e.nodes)).peak) s.peak

theorem invoke_correct (s : State) (arguments : List Expr) (n m a b wn wm wa wb : Nat)
    (evaluated : arguments.mapM s.evaluate = some [⟨n,wn⟩,⟨m,wm⟩,⟨a,wa⟩,⟨b,wb⟩])
    (allocated : s.baseMemory ≤ s.memory.length)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ work peak : Nat,
      runFuel 837 (.invoke valueParameters unsigned64 arguments
        FloorSumUnsignedInstance.floor_sum_unsigned.body) s =
        .finished ⟨{s with
          memory := s.memory ++ [⟨unsigned64,(directSum m a b n%wordLimit : Nat)⟩],
          bindings := s.bindings ++ [⟨s.memory.length,false⟩],
          work := s.work+(arguments.map Expr.nodes).sum+work+6,peak := peak},none,false⟩ ∧
      work ≤ 4229 ∧ peak ≤ max (argumentPeak s arguments) (25+(callerPrefix s).length-s.baseMemory) ∧
      work ≤ 5+132*(m.log2+1) := by
  have nb : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mb : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have prepared := prepare_exact s arguments n m a b wn wm wa wb evaluated nb mb ha hb
  have prefixBound : s.baseMemory ≤ (callerPrefix s).length := by
    simp [callerPrefix]
    omega
  have preparationBound : (callerPrefix s).length-s.baseMemory ≤
      (preparedState s arguments n m a b).peak := by
    simp [preparedState]
    omega
  obtain ⟨fn,fm,fa,fb,work,peak,body,hw,hp,hlog⟩ := body_runs_withCallerBase n m a b
    (callerPrefix s) (preparedState s arguments n m a b).work
    (preparedState s arguments n m a b).peak s.baseMemory prefixBound preparationBound
    hn hm positive ha hb
  change runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body
    (preparedState s arguments n m a b) = _ at body
  have valid := unsigned64_valid (directSum m a b n%wordLimit)
    (Nat.mod_lt _ (by decide : 0 < wordLimit))
  have invoked := invoke_composed 836 s (preparedState s arguments n m a b)
    valueParameters unsigned64 arguments FloorSumUnsignedInstance.floor_sum_unsigned.body
    ⟨{parameterState fn fm fa fb (callerPrefix s) with
      work := work+(preparedState s arguments n m a b).work,baseMemory := s.baseMemory,peak := peak},
      some (directSum m a b n%wordLimit : Nat),false⟩
    (directSum m a b n%wordLimit : Nat) work prepared body rfl rfl valid (by simp [Nat.add_comm])
  let finalPeak := max (max s.peak peak)
    (s.memory.length+1-s.baseMemory+s.bindings.length+1)
  refine ⟨work,finalPeak,?_,hw,?_,hlog⟩
  · simpa [valueParameters_shape,State.observe,finalPeak,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using invoked
  · have callerPeak := argumentPeak_ge s arguments
    simp [preparedState] at hp
    simp [finalPeak,callerPrefix] at hp ⊢
    omega

end Proofs.FloorSumInvoke
