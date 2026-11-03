import Proofs.FloorSumANormalization
import Proofs.FloorSumReduction
import Proofs.FloorSumReciprocity

namespace Proofs.FloorSumRound
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.FloorSumState
open Proofs.FloorSumArithmetic Proofs.FloorSumANormalization Proofs.FloorSumNormalization
open Proofs.FloorSumReduction Proofs.FloorSumReciprocity

def afterNormalization : Stmt := match iteration with
  | .scope (.scope (.sequence _ (.sequence _ rest))) => rest
  | _ => .skip

theorem afterNormalization_shape : afterNormalization =
    .sequence declareY (.sequence stopCheck afterStop) := rfl

theorem iteration_finish (fuel : Nat) (n m a b ans fn fm fa fb fans y : Int)
    (caller : List Cell) (work peak finalWork finalPeak : Nat) (breaking : Bool)
    (middle next : State)
    (hA : runFuel (fuel+8) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨middle,none,false⟩)
    (hB : runFuel (fuel+7) normalizeB middle = .finished ⟨next,none,false⟩)
    (ht : runFuel (fuel+7) afterNormalization next =
      .finished ⟨yState fn fm fa fb fans y caller finalWork finalPeak,none,breaking⟩) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState fn fm fa fb fans caller finalWork finalPeak,none,breaking⟩ := by
  rw [afterNormalization_shape] at ht
  have fromB := sequence_finished (fuel+7) normalizeB
    (.sequence declareY (.sequence stopCheck afterStop)) _ _ _ hB ht
  have core := sequence_finished (fuel+8) normalizeA
    (.sequence normalizeB (.sequence declareY (.sequence stopCheck afterStop))) _ _ _ hA
    (by simpa [Nat.add_assoc] using fromB)
  have inner := scope_finished (fuel+9) _ _ _ (by simpa [Nat.add_assoc] using core)
  have cleaned : runFuel (fuel+10) (.scope
      (.sequence normalizeA (.sequence normalizeB (.sequence declareY (.sequence stopCheck afterStop)))))
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState fn fm fa fb fans caller finalWork finalPeak,none,breaking⟩ := by
    simpa [Nat.add_assoc, frameState, yState, List.take_append, List.take_of_length_le] using inner
  have outer := scope_finished (fuel+10) _ _ _ cleaned
  rw [iteration_shape]
  simpa [Nat.add_assoc,frameState,List.take_of_length_le] using outer

theorem suffix_stop (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (ha : a < m) (hb : b < m)
    (hans : ans < wordLimit) (hy : a*n+b < m) :
    runFuel (fuel+7) afterNormalization (frameState n m a b ans caller work peak) =
      .finished ⟨yState n m a b ans (a*n+b : Nat) caller (work+11) (max peak 17),none,true⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have vy := unsigned64_valid (a*n+b) (normalized_y_bound n m a b hn hm ha hb)
  have declaration := declareY_runs (fuel+4) (n:Int) m a b ans (a*n+b : Nat) caller work peak
    (frame_y n m a b ans caller work peak hn hm ha hb hans) vy
  have stop := stopCheck_breaks fuel (n:Int) m a b ans (a*n+b : Nat) caller
    (work+6) (max peak 17) (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a aBound) (unsigned64_valid b bBound) (unsigned64_valid ans hans)
    vy (Int.ofNat_lt.mpr hy)
  have tail := sequence_breaking (fuel+5) stopCheck afterStop _ _ stop
  rw [afterNormalization_shape]
  have result := sequence_finished (fuel+6) declareY (.sequence stopCheck afterStop) _ _ _
    (by simpa [Nat.add_assoc] using declaration)
    (by simpa [Nat.add_assoc] using tail)
  simpa [Nat.add_assoc,Nat.max_assoc] using result

theorem suffix_continue (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < m) (hb : b < m) (hans : ans < wordLimit) (hy : m ≤ a*n+b) :
    runFuel (fuel+7) afterNormalization (frameState n m a b ans caller work peak) =
      .finished ⟨yState ((a*n+b)/m : Nat) a m ((a*n+b)%m : Nat) ans (a*n+b : Nat) caller
        (work+24) (max peak 17),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have yBound := normalized_y_bound n m a b hn hm ha hb
  have vy := unsigned64_valid (a*n+b) yBound
  have declaration := declareY_runs (fuel+4) (n:Int) m a b ans (a*n+b : Nat) caller work peak
    (frame_y n m a b ans caller work peak hn hm ha hb hans) vy
  have stop := stopCheck_continues (fuel+3) (n:Int) m a b ans (a*n+b : Nat) caller
    (work+6) (max peak 17) (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a aBound) (unsigned64_valid b bBound) (unsigned64_valid ans hans)
    vy (Int.ofNat_le.mpr hy)
  have update := afterStop_runs (fuel+1) n m a b ans (a*n+b) caller
    (work+10) (max peak 17) nBound mBound aBound bBound hans yBound positive
  have tail := sequence_finished (fuel+5) stopCheck afterStop _ _ _
    (by simpa [Nat.add_assoc,Nat.max_assoc] using stop)
    (by simpa [Nat.add_assoc,Nat.max_assoc] using update)
  rw [afterNormalization_shape]
  have result := sequence_finished (fuel+6) declareY (.sequence stopCheck afterStop) _ _ _
    (by simpa [Nat.add_assoc] using declaration)
    (by simpa [Nat.add_assoc] using tail)
  simpa [Nat.add_assoc,Nat.max_assoc] using result

def roundY (n m a b : Nat) : Nat := (a%m)*n+b%m

def roundPeak (m a b : Nat) : Nat := max (normalizationPeak m a b) 17

theorem normalizedAns_bound (n m a b ans : Nat) : normalizedAns n m a b ans < wordLimit := by
  exact Nat.mod_lt _ (by decide)

theorem roundPeak_bound (m a b : Nat) : roundPeak m a b ≤ 25 := by
  have := normalizationPeak_bound m a b
  simp only [roundPeak, Nat.max_le]
  omega

theorem iteration_normalized_suffix (fuel : Nat) (n m a b ans : Nat)
    (fn fm fa fb fans y : Int) (caller : List Cell)
    (work peak finalWork finalPeak : Nat) (breaking : Bool)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit)
    (ht : runFuel (fuel+7) afterNormalization
        (frameState n m (a%m : Nat) (b%m : Nat) (normalizedAns n m a b ans) caller
          (work+normalizationWork m a b) (max peak (normalizationPeak m a b))) =
      .finished ⟨yState fn fm fa fb fans y caller finalWork finalPeak,none,breaking⟩) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState fn fm fa fb fans caller finalWork finalPeak,none,breaking⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have arBound : a%m < wordLimit := by have := Nat.mod_lt a positive; omega
  have first := normalizeA_runs (fuel+2) n m a b ans caller work peak hn mBound ha hb hans positive
  have second := normalizeB_runs (fuel+1) n m (a%m) b (aAns n m a ans) caller
    (work + if m ≤ a then 24 else 4) (max peak (if m ≤ a then 25 else 13))
    nBound mBound arBound hb (aAns_bound n m a ans) positive
  exact iteration_finish fuel n m a b ans fn fm fa fb fans y caller work peak finalWork finalPeak
    breaking _ _ (by simpa [Nat.add_assoc] using first)
    (by simpa [Nat.add_assoc,Nat.max_assoc,normalizationWork,normalizationPeak,bAns_after_aAns] using second)
    ht

theorem iteration_stop_general (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) (hy : roundY n m a b < m) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) (b%m : Nat) (normalizedAns n m a b ans) caller
        (work+normalizationWork m a b+11) (max peak (roundPeak m a b)),none,true⟩ := by
  have suffix := suffix_stop fuel n m (a%m) (b%m) (normalizedAns n m a b ans) caller
    (work+normalizationWork m a b) (max peak (normalizationPeak m a b)) hn hm
    (Nat.mod_lt a positive) (Nat.mod_lt b positive) (normalizedAns_bound n m a b ans) hy
  exact iteration_normalized_suffix fuel n m a b ans n m (a%m : Nat) (b%m : Nat)
    (normalizedAns n m a b ans) (roundY n m a b) caller work peak _ _ true
    hn hm positive ha hb hans (by simpa [roundY,roundPeak,Nat.max_assoc] using suffix)

theorem iteration_continue_general (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) (hy : m ≤ roundY n m a b) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState (roundY n m a b/m : Nat) (a%m : Nat) m (roundY n m a b%m : Nat)
        (normalizedAns n m a b ans) caller (work+normalizationWork m a b+24)
        (max peak (roundPeak m a b)),none,false⟩ := by
  have suffix := suffix_continue fuel n m (a%m) (b%m) (normalizedAns n m a b ans) caller
    (work+normalizationWork m a b) (max peak (normalizationPeak m a b)) hn hm positive
    (Nat.mod_lt a positive) (Nat.mod_lt b positive) (normalizedAns_bound n m a b ans) hy
  exact iteration_normalized_suffix fuel n m a b ans (roundY n m a b/m : Nat) (a%m : Nat) m
    (roundY n m a b%m : Nat) (normalizedAns n m a b ans) (roundY n m a b) caller work peak _ _ false
    hn hm positive ha hb hans (by simpa [roundY,roundPeak,Nat.max_assoc] using suffix)

theorem outerLoop_stop_general (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) (hy : roundY n m a b < m) :
    runFuel (fuel+12) outerLoop (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) (b%m : Nat) (normalizedAns n m a b ans) caller
        (work+normalizationWork m a b+13) (max peak (roundPeak m a b)),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have rpLow : 11 ≤ roundPeak m a b := Nat.le_trans (by decide) (Nat.le_max_right _ _)
  have he := frame_loop_condition (n:Int) m a b ans caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a ha) (unsigned64_valid b hb) (unsigned64_valid ans hans)
  have body := iteration_stop_general fuel n m a b ans caller (work+2) (max peak 11)
    hn hm positive ha hb hans hy
  have next : ({frameState n m a b ans caller work peak with work := work+2}).observe loopCondition.nodes =
      frameState n m a b ans caller (work+2) (max peak 11) := by
    simp [frameState,State.observe,loopCondition_shape,Expr.nodes]
  have hw : work+2+normalizationWork m a b+11 =
      work+normalizationWork m a b+13 := by omega
  have hp : max (max peak 11) (roundPeak m a b) = max peak (roundPeak m a b) := by omega
  have bodyResult := body
  simp only [hw,hp] at bodyResult
  have bodyExact := (congrArg (runFuel (fuel+11) iteration) next).trans bodyResult
  rw [outerLoop_shape]
  have finished := while_finished_break (fuel+11) loopCondition iteration
    (frameState n m a b ans caller work peak)
    (frameState n m (a%m : Nat) (b%m : Nat) (normalizedAns n m a b ans) caller
      (work+normalizationWork m a b+13) (max peak (roundPeak m a b))) ⟨1,1⟩ he (by decide)
    bodyExact
  simpa [Nat.add_assoc] using finished

theorem outerLoop_continue_general (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) (hy : m ≤ roundY n m a b) :
    runFuel (fuel+12) outerLoop (frameState n m a b ans caller work peak) =
      runFuel (fuel+11) outerLoop
        (frameState (roundY n m a b/m : Nat) (a%m : Nat) m (roundY n m a b%m : Nat)
          (normalizedAns n m a b ans) caller (work+normalizationWork m a b+26)
          (max peak (roundPeak m a b))) := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have rpLow : 11 ≤ roundPeak m a b := Nat.le_trans (by decide) (Nat.le_max_right _ _)
  have he := frame_loop_condition (n:Int) m a b ans caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a ha) (unsigned64_valid b hb) (unsigned64_valid ans hans)
  have body := iteration_continue_general fuel n m a b ans caller (work+2) (max peak 11)
    hn hm positive ha hb hans hy
  have next : ({frameState n m a b ans caller work peak with work := work+2}).observe loopCondition.nodes =
      frameState n m a b ans caller (work+2) (max peak 11) := by
    simp [frameState,State.observe,loopCondition_shape,Expr.nodes]
  have hw : work+2+normalizationWork m a b+24 =
      work+normalizationWork m a b+26 := by omega
  have hp : max (max peak 11) (roundPeak m a b) = max peak (roundPeak m a b) := by omega
  have bodyResult := body
  simp only [hw,hp] at bodyResult
  have bodyExact := (congrArg (runFuel (fuel+11) iteration) next).trans bodyResult
  rw [outerLoop_shape]
  have continued := while_continues (fuel+11) loopCondition iteration
    (frameState n m a b ans caller work peak)
    (frameState (roundY n m a b/m : Nat) (a%m : Nat) m (roundY n m a b%m : Nat)
      (normalizedAns n m a b ans) caller (work+normalizationWork m a b+26)
      (max peak (roundPeak m a b))) ⟨1,1⟩ he (by decide)
    bodyExact
  simpa [Nat.add_assoc] using continued

theorem loop_correct (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) :
    ∃ fuel fn fm fa fb finalWork finalPeak : Nat,
      runFuel fuel outerLoop (frameState n m a b ans caller work peak) =
        .finished ⟨frameState fn fm fa fb (mathRun n m a b ans) caller finalWork finalPeak,none,false⟩ ∧
      fn < inputLimit ∧ 0 < fm ∧ fm < inputLimit ∧ fa < wordLimit ∧ fb < wordLimit ∧
      finalWork ≤ work+66*rounds n m a b ∧ finalPeak ≤ max peak 25 ∧
      fuel ≤ 13*rounds n m a b := by
  induction m using Nat.strongRecOn generalizing n a b ans work peak with
  | ind m ih =>
    have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
    have arBound : a%m < wordLimit := by have := Nat.mod_lt a positive; omega
    have brBound : b%m < wordLimit := by have := Nat.mod_lt b positive; omega
    have hcost := normalizationWork_bound m a b
    by_cases hy : roundY n m a b < m
    · have mathStop : mathRun n m a b ans = normalizedAns n m a b ans := by
        rw [mathRun]
        simp only [dite_eq_right (Nat.ne_of_gt positive)]
        exact ite_eq_left hy
      have roundsStop : rounds n m a b = 1 := by
        rw [rounds]
        simp only [dite_eq_right (Nat.ne_of_gt positive)]
        exact ite_eq_left hy
      refine ⟨12,n,m,a%m,b%m,work+normalizationWork m a b+13,max peak (roundPeak m a b),
        ?_,hn,positive,hm,arBound,brBound,?_,?_,?_⟩
      · simpa only [Nat.zero_add,mathStop] using
          outerLoop_stop_general 0 n m a b ans caller work peak hn hm positive ha hb hans hy
      · rw [roundsStop]
        omega
      · have := roundPeak_bound m a b
        omega
      · rw [roundsStop]
        decide
    · have continues : m ≤ roundY n m a b := by omega
      have transition := reduction_preserves_domain n m a b hn hm positive continues
      have nextN := transition.2.2.2.1
      have nextM := transition.2.2.1
      have remBound : roundY n m a b%m < wordLimit := by
        have := Nat.mod_lt (roundY n m a b) positive
        omega
      have nextAns := normalizedAns_bound n m a b ans
      obtain ⟨fuel,fn,fm,fa,fb,finalWork,finalPeak,hRun,hfn,hpos,hfm,hfa,hfb,hwork,hpeak,hfuel⟩ :=
        ih (a%m) (Nat.mod_lt a positive) (roundY n m a b/m) m (roundY n m a b%m)
          (normalizedAns n m a b ans) (work+normalizationWork m a b+26) (max peak (roundPeak m a b))
          nextN nextM transition.1 mBound remBound nextAns
      have mathStep : mathRun n m a b ans =
          mathRun (roundY n m a b/m) (a%m) m (roundY n m a b%m) (normalizedAns n m a b ans) := by
        rw [mathRun]
        simp only [dite_eq_right (Nat.ne_of_gt positive)]
        exact ite_eq_right hy
      have roundsStep : rounds n m a b =
          1+rounds (roundY n m a b/m) (a%m) m (roundY n m a b%m) := by
        rw [rounds]
        simp only [dite_eq_right (Nat.ne_of_gt positive)]
        exact ite_eq_right hy
      have padded := runFuel_success_mono fuel 12 outerLoop _ _ hRun
      have fromCurrent := outerLoop_continue_general (fuel+1) n m a b ans caller work peak
        hn hm positive ha hb hans continues
      refine ⟨fuel+13,fn,fm,fa,fb,finalWork,finalPeak,?_,hfn,hpos,hfm,hfa,hfb,?_,?_,?_⟩
      · rw [mathStep]
        simp only [Nat.add_assoc] at fromCurrent
        exact fromCurrent.trans padded
      · rw [roundsStep,Nat.mul_add,Nat.mul_one]
        omega
      · have hp := roundPeak_bound m a b
        omega
      · rw [roundsStep,Nat.mul_add,Nat.mul_one]
        omega

theorem loop_uniform_correct (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit) :
    ∃ fn fm fa fb finalWork finalPeak : Nat,
      runFuel 832 outerLoop (frameState n m a b ans caller work peak) =
        .finished ⟨frameState fn fm fa fb ((ans+directSum m a b n)%wordLimit : Nat)
          caller finalWork finalPeak,none,false⟩ ∧
      fn < inputLimit ∧ 0 < fm ∧ fm < inputLimit ∧ fa < wordLimit ∧ fb < wordLimit ∧
      finalWork ≤ work+4224 ∧ finalPeak ≤ max peak 25 ∧
      finalWork ≤ work+132*(m.log2+1) := by
  obtain ⟨fuel,fn,fm,fa,fb,finalWork,finalPeak,hRun,hfn,hpos,hfm,hfa,hfb,hwork,hpeak,hfuel⟩ :=
    loop_correct n m a b ans caller work peak hn hm positive ha hb hans
  have roundBound := rounds_bound_input n m a b hm
  have fuelBound : fuel ≤ 832 := by omega
  have padded := runFuel_success_mono fuel (832-fuel) outerLoop _ _ hRun
  refine ⟨fn,fm,fa,fb,finalWork,finalPeak,?_,hfn,hpos,hfm,hfa,hfb,?_,hpeak,?_⟩
  · simpa only [Nat.add_sub_of_le fuelBound,mathRun_correct n m a b ans positive] using padded
  · omega
  · have logBound := rounds_bound_log n m a b
    omega

end Proofs.FloorSumRound
