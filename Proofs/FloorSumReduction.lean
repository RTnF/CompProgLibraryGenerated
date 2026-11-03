import Proofs.FloorSumState

namespace Proofs.FloorSumReduction
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.FloorSumState
open Proofs.FloorSumArithmetic

def quotient : Expr := match afterStop with
  | .sequence (.assign _ value) _ => value
  | _ => .literal unsigned64 0

def remainder : Expr := match afterStop with
  | .sequence _ (.sequence (.assign _ value) _) => value
  | _ => .literal unsigned64 0

theorem quotient_shape : quotient =
    .divrem unsigned64 false (.variable unsigned64 5) (.variable unsigned64 1) := rfl

theorem remainder_shape : remainder =
    .divrem unsigned64 true (.variable unsigned64 5) (.variable unsigned64 1) := rfl

theorem afterStop_shape : afterStop = .sequence (.assign 0 quotient)
    (.sequence (.assign 3 remainder) (.sequence (.swap 1 2) .skip)) := rfl

theorem y_assign_n (fuel : Nat) (n m a b ans y q : Int) (caller : List Cell)
    (work peak : Nat) (e : Expr)
    (he : (yState n m a b ans y caller work peak).evaluate e = some ⟨q,3⟩)
    (hq : unsigned64.valid q = true) (hnodes : e.nodes = 3) :
    runFuel (fuel+1) (.assign 0 e) (yState n m a b ans y caller work peak) =
      .finished ⟨yState q m a b ans y caller (work+4) (max peak 15),none,false⟩ := by
  have cv := Ty.convert_of_valid unsigned64 q hq
  have h0 : ¬caller.length < caller.length := by omega
  simp only [yState] at he
  simp [runFuel, Stmt.run, yState, List.getElem?_append, h0, he, cv,
    List.set_append_right, State.observe, hnodes, Nat.add_assoc, liftChecked]

theorem y_assign_b (fuel : Nat) (n m a b ans y r : Int) (caller : List Cell)
    (work peak : Nat) (e : Expr)
    (he : (yState n m a b ans y caller work peak).evaluate e = some ⟨r,3⟩)
    (hr : unsigned64.valid r = true) (hnodes : e.nodes = 3) :
    runFuel (fuel+1) (.assign 3 e) (yState n m a b ans y caller work peak) =
      .finished ⟨yState n m a r ans y caller (work+4) (max peak 15),none,false⟩ := by
  have cv := Ty.convert_of_valid unsigned64 r hr
  have h3 : ¬caller.length+3 < caller.length := by omega
  simp only [yState] at he
  simp [runFuel, Stmt.run, yState, List.getElem?_append, h3, he, cv,
    List.set_append_right, State.observe, hnodes, Nat.add_assoc, liftChecked]

theorem y_swap (fuel : Nat) (n m a b ans y : Int) (caller : List Cell)
    (work peak : Nat) (vm : unsigned64.valid m = true) (va : unsigned64.valid a = true) :
    runFuel (fuel+1) (.swap 1 2) (yState n m a b ans y caller work peak) =
      .finished ⟨yState n a m b ans y caller (work+6) (max peak 15),none,false⟩ := by
  have h1 : ¬caller.length+1 < caller.length := by omega
  have h2 : ¬caller.length+2 < caller.length := by omega
  simp [runFuel, Stmt.run, yState, List.getElem?_append, h1,h2, vm,va,
    List.set_append_right, State.observe, liftChecked]

theorem quotient_evaluate (n m a b ans y : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true)
    (hm : m ≠ 0) (vq : unsigned64.valid (y.tdiv m) = true) :
    (yState n m a b ans y caller work peak).evaluate quotient = some ⟨y.tdiv m,3⟩ := by
  rw [State.evaluate, y_environment n m a b ans y caller work peak vn vm va vb vans vy,
    quotient_shape]
  have hd := checkedDivRem_division_exact unsigned64 y m hm vq
  simp [Expr.eval, vm, vy, hd]

theorem remainder_evaluate (n m a b ans y : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true)
    (hm : m ≠ 0) (vq : unsigned64.valid (y.tdiv m) = true)
    (vr : unsigned64.valid (y.tmod m) = true) :
    (yState n m a b ans y caller work peak).evaluate remainder = some ⟨y.tmod m,3⟩ := by
  rw [State.evaluate, y_environment n m a b ans y caller work peak vn vm va vb vans vy,
    remainder_shape]
  have hd := checkedDivRem_remainder_exact unsigned64 y m hm vq vr
  simp [Expr.eval, vm, vy, hd]

theorem afterStop_runs_int (fuel : Nat) (n m a b ans y : Int) (caller : List Cell)
    (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true)
    (hm : m ≠ 0) (vq : unsigned64.valid (y.tdiv m) = true)
    (vr : unsigned64.valid (y.tmod m) = true) :
    runFuel (fuel+4) afterStop (yState n m a b ans y caller work peak) =
      .finished ⟨yState (y.tdiv m) a m (y.tmod m) ans y caller
        (work+14) (max peak 15),none,false⟩ := by
  have first := y_assign_n (fuel+2) n m a b ans y (y.tdiv m) caller work peak quotient
    (quotient_evaluate n m a b ans y caller work peak vn vm va vb vans vy hm vq)
    vq (by rw [quotient_shape]; rfl)
  have second := y_assign_b (fuel+1) (y.tdiv m) m a b ans y (y.tmod m)
    caller (work+4) (max peak 15) remainder
    (remainder_evaluate (y.tdiv m) m a b ans y caller (work+4) (max peak 15)
      vq vm va vb vans vy hm vq vr) vr (by rw [remainder_shape]; rfl)
  have swap := y_swap fuel (y.tdiv m) m a (y.tmod m) ans y caller
    (work+8) (max peak 15) vm va
  have tail := sequence_finished (fuel+1) (.swap 1 2) .skip _ _
    ⟨yState (y.tdiv m) a m (y.tmod m) ans y caller (work+8+6) (max (max peak 15) 15),none,false⟩
    swap (by rfl)
  have middle := sequence_finished (fuel+2) (.assign 3 remainder)
    (.sequence (.swap 1 2) .skip) _ _ _
    (by simpa [Nat.add_assoc,Nat.max_assoc] using second)
    (by simpa [Nat.add_assoc,Nat.max_assoc] using tail)
  rw [afterStop_shape]
  have finished := sequence_finished (fuel+3) (.assign 0 quotient)
    (.sequence (.assign 3 remainder) (.sequence (.swap 1 2) .skip)) _ _ _
    (by simpa [Nat.add_assoc] using first)
    (by simpa [Nat.add_assoc,Nat.max_assoc] using middle)
  simpa [Nat.add_assoc,Nat.max_assoc] using finished

theorem afterStop_runs (fuel : Nat) (n m a b ans y : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < wordLimit) (hm : m < wordLimit)
    (ha : a < wordLimit) (hb : b < wordLimit) (hans : ans < wordLimit)
    (hy : y < wordLimit) (positive : 0 < m) :
    runFuel (fuel+4) afterStop (yState n m a b ans y caller work peak) =
      .finished ⟨yState (y/m : Nat) a m (y%m : Nat) ans y caller
        (work+14) (max peak 15),none,false⟩ := by
  have qBound : y/m < wordLimit := by have := Nat.div_le_self y m; omega
  have rBound : y%m < wordLimit := by have := Nat.mod_lt y positive; omega
  simpa only [← Int.ofNat_tdiv, ← Int.ofNat_tmod] using
    afterStop_runs_int fuel (n:Int) m a b ans y caller work peak
      (unsigned64_valid n hn) (unsigned64_valid m hm)
      (unsigned64_valid a ha) (unsigned64_valid b hb)
      (unsigned64_valid ans hans) (unsigned64_valid y hy) (by omega)
      (by simpa only [← Int.ofNat_tdiv] using unsigned64_valid (y/m) qBound)
      (by simpa only [← Int.ofNat_tmod] using unsigned64_valid (y%m) rBound)

theorem iteration_continue (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit)
    (positive : 0 < m) (ha : a < m) (hb : b < m) (hans : ans < wordLimit)
    (hy : m ≤ a*n+b) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState ((a*n+b)/m : Nat) a m ((a*n+b)%m : Nat) ans caller
        (work+32) (max peak 17),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have yBound := normalized_y_bound n m a b hn hm ha hb
  have vn := unsigned64_valid n nBound
  have vm := unsigned64_valid m mBound
  have va := unsigned64_valid a aBound
  have vb := unsigned64_valid b bBound
  have vans := unsigned64_valid ans hans
  have vy := unsigned64_valid (a*n+b) yBound
  have first : runFuel (fuel+8) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+4) (max peak 13),none,false⟩ := by
    simpa [Nat.add_assoc] using normalizeA_skip (fuel+6) (n:Int) m a b ans caller work peak
      vn vm va vb vans (Int.ofNat_lt.mpr ha)
  have second : runFuel (fuel+7) normalizeB
      (frameState n m a b ans caller (work+4) (max peak 13)) =
      .finished ⟨frameState n m a b ans caller (work+8) (max peak 13),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using normalizeB_skip (fuel+5) (n:Int) m a b ans
      caller (work+4) (max peak 13) vn vm va vb vans (Int.ofNat_lt.mpr hb)
  have declaration : runFuel (fuel+6) declareY
      (frameState n m a b ans caller (work+8) (max peak 13)) =
      .finished ⟨yState n m a b ans (a*n+b : Nat) caller (work+14) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using declareY_runs (fuel+4) (n:Int) m a b ans
      (a*n+b : Nat) caller (work+8) (max peak 13)
      (frame_y n m a b ans caller (work+8) (max peak 13) hn hm ha hb hans) vy
  have stop : runFuel (fuel+5) stopCheck
      (yState n m a b ans (a*n+b : Nat) caller (work+14) (max peak 17)) =
      .finished ⟨yState n m a b ans (a*n+b : Nat) caller (work+18) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using stopCheck_continues (fuel+3) (n:Int) m a b ans
      (a*n+b : Nat) caller (work+14) (max peak 17) vn vm va vb vans vy (Int.ofNat_le.mpr hy)
  have update := afterStop_runs (fuel+1) n m a b ans (a*n+b) caller
    (work+18) (max peak 17) nBound mBound aBound bBound hans yBound positive
  have tail := sequence_finished (fuel+5) stopCheck afterStop _ _ _ stop
    (by simpa [Nat.add_assoc,Nat.max_assoc] using update)
  have fromDeclaration := sequence_finished (fuel+6) declareY (.sequence stopCheck afterStop)
    _ _ _ declaration (by simpa [Nat.add_assoc] using tail)
  have fromB := sequence_finished (fuel+7) normalizeB
    (.sequence declareY (.sequence stopCheck afterStop)) _ _ _ second
    (by simpa [Nat.add_assoc] using fromDeclaration)
  have core := sequence_finished (fuel+8) normalizeA
    (.sequence normalizeB (.sequence declareY (.sequence stopCheck afterStop))) _ _ _ first
    (by simpa [Nat.add_assoc] using fromB)
  have inner := scope_finished (fuel+9) _ _ _ (by simpa [Nat.add_assoc] using core)
  have cleaned : runFuel (fuel+10) (.scope
      (.sequence normalizeA (.sequence normalizeB (.sequence declareY (.sequence stopCheck afterStop)))))
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState ((a*n+b)/m : Nat) a m ((a*n+b)%m : Nat) ans caller
        (work+32) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc, frameState, yState, List.take_append,
      List.take_of_length_le] using inner
  have outer := scope_finished (fuel+10) _ _ _ cleaned
  rw [iteration_shape]
  simpa [Nat.add_assoc, frameState, List.take_of_length_le] using outer

theorem while_continues (fuel : Nat) (condition : Expr) (body : Stmt)
    (s final : State) (result : Result)
    (he : s.evaluate condition = some result) (hvalue : result.value ≠ 0)
    (hb : runFuel fuel body (({s with work := s.work+result.work+1}).observe condition.nodes) =
      .finished ⟨final,none,false⟩) :
    runFuel (fuel+1) (.whileLoop condition body) s =
      runFuel fuel (.whileLoop condition body) final := by
  change (do
    let result ← liftChecked (s.evaluate condition)
    let next := ({s with work := s.work+result.work+1}).observe condition.nodes
    if result.value == 0 then pure (⟨next,none,false⟩ : Step) else do
      let step ← runFuel fuel body next
      if step.returned.isSome then pure step
      else if step.breaking then pure {step with breaking := false}
      else runFuel fuel (.whileLoop condition body) step.state) = _
  simp only [he, liftChecked, bind, Outcome.bind, hvalue, beq_iff_eq, ite_false, hb]
  rfl

theorem outerLoop_continue (fuel : Nat) (n m a b ans : Nat) (caller : List Cell)
    (work peak : Nat) (hn : n < inputLimit) (hm : m < inputLimit)
    (positive : 0 < m) (ha : a < m) (hb : b < m) (hans : ans < wordLimit)
    (hy : m ≤ a*n+b) :
    runFuel (fuel+12) outerLoop (frameState n m a b ans caller work peak) =
      runFuel (fuel+11) outerLoop
        (frameState ((a*n+b)/m : Nat) a m ((a*n+b)%m : Nat) ans caller
          (work+34) (max peak 17)) := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have he := frame_loop_condition (n:Int) m a b ans caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a aBound) (unsigned64_valid b bBound) (unsigned64_valid ans hans)
  have body := iteration_continue fuel n m a b ans caller (work+2) (max peak 11)
    hn hm positive ha hb hans hy
  rw [outerLoop_shape]
  have continued := while_continues (fuel+11) loopCondition iteration
    (frameState n m a b ans caller work peak)
    (frameState ((a*n+b)/m : Nat) a m ((a*n+b)%m : Nat) ans caller
      (work+34) (max peak 17)) ⟨1,1⟩ he (by decide)
    (by simpa [frameState, State.observe, loopCondition_shape, Expr.nodes,
      Nat.add_assoc, Nat.max_assoc] using body)
  simpa [Nat.add_assoc] using continued

end Proofs.FloorSumReduction
