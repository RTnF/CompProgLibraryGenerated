import Proofs.Generated.FloorSumUnsigned
import Proofs.FloorSumArithmetic

namespace Proofs.FloorSumState
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop
open Proofs.FloorSumArithmetic

def unsigned64 : Ty := ⟨64, false, false⟩
def boolType : Ty := ⟨1, false, true⟩

-- These projections select subterms of the generated C++ model. The shape
-- theorems below must still typecheck if that model changes; no replacement
-- algorithm is selected by the source hash or function name.
def iteration : Stmt := match FloorSumUnsignedInstance.floor_sum_unsigned.body with
  | .scope (.sequence _ (.sequence (.whileLoop _ body) _)) => body
  | _ => .skip

def normalizeA : Stmt := match iteration with
  | .scope (.scope (.sequence first _)) => first
  | _ => .skip

def normalizeB : Stmt := match iteration with
  | .scope (.scope (.sequence _ (.sequence second _))) => second
  | _ => .skip

def guardA : Expr := match normalizeA with
  | .branch condition _ _ => condition
  | _ => .literal boolType 0

def guardB : Expr := match normalizeB with
  | .branch condition _ _ => condition
  | _ => .literal boolType 0

def yExpression : Expr := match iteration with
  | .scope (.scope (.sequence _ (.sequence _ (.sequence (.sequence (.declare _ _ value) _) _)))) => value
  | _ => .literal unsigned64 0

theorem guardA_shape : guardA =
    .binary boolType .ge (.variable unsigned64 2) (.variable unsigned64 1) := rfl

theorem guardB_shape : guardB =
    .binary boolType .ge (.variable unsigned64 3) (.variable unsigned64 1) := rfl

theorem yExpression_shape : yExpression =
    .binary unsigned64 .add
      (.binary unsigned64 .mul (.variable unsigned64 2) (.variable unsigned64 0))
      (.variable unsigned64 3) := rfl

theorem unsigned64_valid (v : Nat) (bound : v < wordLimit) :
    unsigned64.valid (v : Int) = true := by
  simp [unsigned64, Ty.valid, wordLimit] at *
  omega

theorem ge_eval_int (n m a b ans : Int) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) :
    (Expr.binary boolType .ge (.variable unsigned64 2) (.variable unsigned64 1)).eval
      [n,m,a,b,ans] = some ⟨if m ≤ a then 1 else 0, 3⟩ := by
  by_cases h : m ≤ a
  · have hnot : ¬a < m := by omega
    simp [Expr.eval, hm, ha, boolType, Ty.convert, binaryValue, h, hnot]
  · have hlt : a < m := by omega
    simp [Expr.eval, hm, ha, boolType, Ty.convert, binaryValue, h, hlt]

theorem guardA_eval (n m a b ans : Nat) (hm : m < wordLimit) (ha : a < wordLimit) :
    guardA.eval [(n : Int),m,a,b,ans] = some ⟨if m ≤ a then 1 else 0, 3⟩ := by
  rw [guardA_shape]
  simpa only [Int.ofNat_le] using
    ge_eval_int (n:Int) m a b ans (unsigned64_valid m hm) (unsigned64_valid a ha)

theorem ge_b_eval_int (n m a b ans : Int) (hm : unsigned64.valid m = true)
    (hb : unsigned64.valid b = true) :
    (Expr.binary boolType .ge (.variable unsigned64 3) (.variable unsigned64 1)).eval
      [n,m,a,b,ans] = some ⟨if m ≤ b then 1 else 0, 3⟩ := by
  by_cases h : m ≤ b
  · have hnot : ¬b < m := by omega
    simp [Expr.eval, hm, hb, boolType, Ty.convert, binaryValue, h, hnot]
  · have hlt : b < m := by omega
    simp [Expr.eval, hm, hb, boolType, Ty.convert, binaryValue, h, hlt]

theorem guardB_eval (n m a b ans : Nat) (hm : m < wordLimit) (hb : b < wordLimit) :
    guardB.eval [(n : Int),m,a,b,ans] = some ⟨if m ≤ b then 1 else 0, 3⟩ := by
  rw [guardB_shape]
  simpa only [Int.ofNat_le] using
    ge_b_eval_int (n:Int) m a b ans (unsigned64_valid m hm) (unsigned64_valid b hb)

theorem y_eval_int (n m a b ans : Int) (vn : unsigned64.valid n = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (product : unsigned64.convert (a*n) = some (a*n))
    (total : unsigned64.convert (a*n+b) = some (a*n+b)) :
    (Expr.binary unsigned64 .add
      (.binary unsigned64 .mul (.variable unsigned64 2) (.variable unsigned64 0))
      (.variable unsigned64 3)).eval [n,m,a,b,ans] = some ⟨a*n+b,5⟩ := by
  simp [Expr.eval, vn, va, vb, binaryValue, product, total]

theorem yExpression_eval (n m a b ans : Nat) (hn : n < inputLimit)
    (hm : m < inputLimit) (ha : a < m) (hb : b < m) :
    yExpression.eval [(n : Int),m,a,b,ans] = some ⟨(a*n+b : Nat), 5⟩ := by
  rw [yExpression_shape]
  have yBound := normalized_y_bound n m a b hn hm ha hb
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have bBound : b < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have productBound : a*n < wordLimit := by omega
  have vn := unsigned64_valid n nBound
  have va := unsigned64_valid a aBound
  have vb := unsigned64_valid b bBound
  have product := Ty.convert_of_valid unsigned64 ((a*n : Nat) : Int) (unsigned64_valid (a*n) productBound)
  have total := Ty.convert_of_valid unsigned64 ((a*n+b : Nat) : Int) (unsigned64_valid (a*n+b) yBound)
  simpa only [Int.natCast_mul, Int.natCast_add] using
    y_eval_int (n:Int) m a b ans vn va vb
      (by simpa only [Int.natCast_mul] using product)
      (by simpa only [Int.natCast_mul, Int.natCast_add] using total)

def frameState (n m a b ans : Int) (caller : List Cell) (work peak : Nat) : State :=
  ⟨caller ++ [⟨unsigned64,n⟩,⟨unsigned64,m⟩,⟨unsigned64,a⟩,⟨unsigned64,b⟩,⟨unsigned64,ans⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,
      ⟨caller.length+3,true⟩,⟨caller.length+4,true⟩], work, caller.length, peak⟩

theorem frame_environment (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) :
    (frameState n m a b ans caller work peak).environment = some [n,m,a,b,ans] := by
  have h0 : ¬ caller.length < caller.length := by omega
  have h1 : ¬ caller.length+1 < caller.length := by omega
  have h2 : ¬ caller.length+2 < caller.length := by omega
  have h3 : ¬ caller.length+3 < caller.length := by omega
  have h4 : ¬ caller.length+4 < caller.length := by omega
  simp [frameState, State.environment, List.getElem?_append, h0,h1,h2,h3,h4,
    vn,vm,va,vb,vans]

theorem frame_guardA (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) :
    (frameState n m a b ans caller work peak).evaluate guardA =
      some ⟨if m ≤ a then 1 else 0,3⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    guardA_shape]
  exact ge_eval_int n m a b ans vm va

theorem frame_guardB (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) :
    (frameState n m a b ans caller work peak).evaluate guardB =
      some ⟨if m ≤ b then 1 else 0,3⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    guardB_shape]
  exact ge_b_eval_int n m a b ans vm vb

theorem frame_y_int (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true)
    (product : unsigned64.convert (a*n) = some (a*n))
    (total : unsigned64.convert (a*n+b) = some (a*n+b)) :
    (frameState n m a b ans caller work peak).evaluate yExpression = some ⟨a*n+b,5⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    yExpression_shape]
  exact y_eval_int n m a b ans vn va vb product total

theorem frame_y (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (ha : a < m) (hb : b < m)
    (hans : ans < wordLimit) :
    (frameState n m a b ans caller work peak).evaluate yExpression =
      some ⟨(a*n+b : Nat),5⟩ := by
  have yBound := normalized_y_bound n m a b hn hm ha hb
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have productBound : a*n < wordLimit := by omega
  have product := Ty.convert_of_valid unsigned64 ((a*n : Nat) : Int)
    (unsigned64_valid (a*n) productBound)
  have total := Ty.convert_of_valid unsigned64 ((a*n+b : Nat) : Int)
    (unsigned64_valid (a*n+b) yBound)
  simpa only [Int.natCast_mul, Int.natCast_add] using
    frame_y_int (n:Int) m a b ans caller work peak
      (unsigned64_valid n nBound) (unsigned64_valid m mBound)
      (unsigned64_valid a aBound) (unsigned64_valid b bBound) (unsigned64_valid ans hans)
      (by simpa only [Int.natCast_mul] using product)
      (by simpa only [Int.natCast_mul, Int.natCast_add] using total)

def yesA : Stmt := match normalizeA with
  | .branch _ yes _ => yes
  | _ => .skip

def yesB : Stmt := match normalizeB with
  | .branch _ yes _ => yes
  | _ => .skip

theorem normalizeA_shape : normalizeA = .branch guardA yesA .skip := rfl
theorem normalizeB_shape : normalizeB = .branch guardB yesB .skip := rfl

theorem frame_observe (n m a b ans : Int) (caller : List Cell) (work peak : Nat) :
    (frameState n m a b ans caller work peak).observe 3 =
      frameState n m a b ans caller work (max peak 13) := by
  simp [frameState, State.observe]

theorem normalizeA_skip (fuel : Nat) (n m a b ans : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (ha : a < m) :
    runFuel (fuel+2) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+4) (max peak 13), none, false⟩ := by
  have hnot : ¬m ≤ a := by omega
  have he := frame_guardA n m a b ans caller work peak vn vm va vb vans
  simp only [hnot, ite_false] at he
  rw [normalizeA_shape]
  simp only [runFuel, he, liftChecked, bind, pure, Outcome.bind]
  simp [Stmt.run, frameState, State.observe, guardA_shape, Expr.nodes, Nat.add_assoc]

theorem normalizeB_skip (fuel : Nat) (n m a b ans : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (hb : b < m) :
    runFuel (fuel+2) normalizeB (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+4) (max peak 13), none, false⟩ := by
  have hnot : ¬m ≤ b := by omega
  have he := frame_guardB n m a b ans caller work peak vn vm va vb vans
  simp only [hnot, ite_false] at he
  rw [normalizeB_shape]
  simp only [runFuel, he, liftChecked, bind, pure, Outcome.bind]
  simp [Stmt.run, frameState, State.observe, guardB_shape, Expr.nodes, Nat.add_assoc]

theorem normalized_branches_skip (fuel : Nat) (n m a b ans : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (ha : a < m) (hb : b < m) :
    runFuel (fuel+3) (.sequence normalizeA normalizeB)
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+8) (max peak 13), none, false⟩ := by
  have first := normalizeA_skip fuel n m a b ans caller work peak vn vm va vb vans ha
  have second := normalizeB_skip fuel n m a b ans caller (work+4) (max peak 13)
    vn vm va vb vans hb
  change (do
    let step ← runFuel (fuel+2) normalizeA (frameState n m a b ans caller work peak)
    if step.returned.isSome || step.breaking then pure step
    else runFuel (fuel+2) normalizeB step.state) = _
  rw [first]
  simpa [bind, Outcome.bind, Nat.add_assoc, Nat.max_assoc] using second

def declareY : Stmt := match iteration with
  | .scope (.scope (.sequence _ (.sequence _ (.sequence declaration _)))) => declaration
  | _ => .skip

theorem declareY_shape : declareY = .sequence (.declare unsigned64 true yExpression) .skip := rfl

def yState (n m a b ans y : Int) (caller : List Cell) (work peak : Nat) : State :=
  ⟨caller ++ [⟨unsigned64,n⟩,⟨unsigned64,m⟩,⟨unsigned64,a⟩,⟨unsigned64,b⟩,
    ⟨unsigned64,ans⟩,⟨unsigned64,y⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,
      ⟨caller.length+3,true⟩,⟨caller.length+4,true⟩,⟨caller.length+5,true⟩],
    work, caller.length, peak⟩

theorem declareY_runs (fuel : Nat) (n m a b ans y : Int)
    (caller : List Cell) (work peak : Nat)
    (he : (frameState n m a b ans caller work peak).evaluate yExpression = some ⟨y,5⟩)
    (vy : unsigned64.valid y = true) :
    runFuel (fuel+2) declareY (frameState n m a b ans caller work peak) =
      .finished ⟨yState n m a b ans y caller (work+6) (max peak 17), none, false⟩ := by
  rw [declareY_shape]
  have cv := Ty.convert_of_valid unsigned64 y vy
  have first : runFuel (fuel+1) (.declare unsigned64 true yExpression)
      (frameState n m a b ans caller work peak) =
      .finished ⟨yState n m a b ans y caller (work+6) (max peak 17), none, false⟩ := by
    simp only [runFuel, Stmt.run, he]
    simp [cv, liftChecked, frameState, yState, State.observe, yExpression_shape,
      Expr.nodes, List.append_assoc, Nat.add_assoc]
  change (do
    let step ← runFuel (fuel+1) (.declare unsigned64 true yExpression)
      (frameState n m a b ans caller work peak)
    if step.returned.isSome || step.breaking then pure step
    else runFuel (fuel+1) .skip step.state) = _
  rw [first]
  simp [bind, Outcome.bind, runFuel, Stmt.run, liftChecked]

def stopCheck : Stmt := match iteration with
  | .scope (.scope (.sequence _ (.sequence _ (.sequence _ (.sequence check _))))) => check
  | _ => .skip

def stopCondition : Expr := match stopCheck with
  | .branch condition _ _ => condition
  | _ => .literal boolType 0

def afterStop : Stmt := match iteration with
  | .scope (.scope (.sequence _ (.sequence _ (.sequence _ (.sequence _ rest))))) => rest
  | _ => .skip

theorem stopCondition_shape : stopCondition =
    .binary boolType .lt (.variable unsigned64 5) (.variable unsigned64 1) := rfl

theorem stopCheck_shape : stopCheck =
    .branch stopCondition (.scope (.scope (.sequence .breakLoop .skip))) .skip := rfl

theorem iteration_shape : iteration = .scope (.scope
    (.sequence normalizeA (.sequence normalizeB
      (.sequence declareY (.sequence stopCheck afterStop))))) := rfl

theorem y_environment (n m a b ans y : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true) :
    (yState n m a b ans y caller work peak).environment = some [n,m,a,b,ans,y] := by
  have h0 : ¬ caller.length < caller.length := by omega
  have h1 : ¬ caller.length+1 < caller.length := by omega
  have h2 : ¬ caller.length+2 < caller.length := by omega
  have h3 : ¬ caller.length+3 < caller.length := by omega
  have h4 : ¬ caller.length+4 < caller.length := by omega
  have h5 : ¬ caller.length+5 < caller.length := by omega
  simp [yState, State.environment, List.getElem?_append, h0,h1,h2,h3,h4,h5,
    vn,vm,va,vb,vans,vy]

theorem stop_eval_int (n m a b ans y : Int)
    (vm : unsigned64.valid m = true) (vy : unsigned64.valid y = true) :
    stopCondition.eval [n,m,a,b,ans,y] = some ⟨if y < m then 1 else 0,3⟩ := by
  rw [stopCondition_shape]
  by_cases h : y < m <;>
    simp [Expr.eval, vm, vy, binaryValue, boolType, Ty.convert, h]

theorem y_stop_evaluate (n m a b ans y : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true) :
    (yState n m a b ans y caller work peak).evaluate stopCondition =
      some ⟨if y < m then 1 else 0,3⟩ := by
  rw [State.evaluate, y_environment n m a b ans y caller work peak vn vm va vb vans vy]
  exact stop_eval_int n m a b ans y vm vy

theorem stopCheck_breaks (fuel : Nat) (n m a b ans y : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true) (hy : y < m) :
    runFuel (fuel+5) stopCheck (yState n m a b ans y caller work peak) =
      .finished ⟨yState n m a b ans y caller (work+5) (max peak 15), none, true⟩ := by
  have he := y_stop_evaluate n m a b ans y caller work peak vn vm va vb vans vy
  simp only [hy, ite_true] at he
  rw [stopCheck_shape]
  simp only [runFuel, he, liftChecked, bind, pure, Outcome.bind]
  simp [yState, State.observe, stopCondition_shape, Expr.nodes, Nat.add_assoc,
    List.take_of_length_le]

theorem stopCheck_continues (fuel : Nat) (n m a b ans y : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true) (hy : m ≤ y) :
    runFuel (fuel+2) stopCheck (yState n m a b ans y caller work peak) =
      .finished ⟨yState n m a b ans y caller (work+4) (max peak 15), none, false⟩ := by
  have hnot : ¬ y < m := by omega
  have he := y_stop_evaluate n m a b ans y caller work peak vn vm va vb vans vy
  simp only [hnot, ite_false] at he
  rw [stopCheck_shape]
  simp only [runFuel, he, liftChecked, bind, pure, Outcome.bind]
  simp [Stmt.run, yState, State.observe, stopCondition_shape, Expr.nodes, Nat.add_assoc]

theorem sequence_finished (fuel : Nat) (first rest : Stmt) (s middle : State)
    (step : Step)
    (hf : runFuel fuel first s = .finished ⟨middle, none, false⟩)
    (hr : runFuel fuel rest middle = .finished step) :
    runFuel (fuel+1) (.sequence first rest) s = .finished step := by
  change (do
    let step ← runFuel fuel first s
    if step.returned.isSome || step.breaking then pure step
    else runFuel fuel rest step.state) = _
  rw [hf]
  simpa [bind, Outcome.bind] using hr

theorem sequence_breaking (fuel : Nat) (first rest : Stmt) (s final : State)
    (hf : runFuel fuel first s = .finished ⟨final, none, true⟩) :
    runFuel (fuel+1) (.sequence first rest) s = .finished ⟨final, none, true⟩ := by
  change (do
    let step ← runFuel fuel first s
    if step.returned.isSome || step.breaking then pure step
    else runFuel fuel rest step.state) = _
  rw [hf]
  simp [bind, pure, Outcome.bind]

theorem scope_finished (fuel : Nat) (body : Stmt) (s : State) (step : Step)
    (h : runFuel fuel body s = .finished step) :
    runFuel (fuel+1) (.scope body) s = .finished
      { step with state := { step.state with
        memory := step.state.memory.take s.memory.length
        bindings := step.state.bindings.take s.bindings.length } } := by
  change (do
    let step ← runFuel fuel body s
    pure { step with state := { step.state with
      memory := step.state.memory.take s.memory.length
      bindings := step.state.bindings.take s.bindings.length } }) = _
  rw [h]
  rfl

theorem y_scope_restore (n m a b ans y : Int) (caller : List Cell)
    (work peak : Nat) :
    {yState n m a b ans y caller work peak with
      memory := (yState n m a b ans y caller work peak).memory.take (caller.length+5),
      bindings := (yState n m a b ans y caller work peak).bindings.take 5} =
      frameState n m a b ans caller work peak := by
  simp [yState, frameState, List.take_append, List.take_of_length_le]

theorem iteration_stop_int (fuel : Nat) (n m a b ans y : Int)
    (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (vy : unsigned64.valid y = true)
    (ha : a < m) (hb : b < m) (hy : y < m)
    (he : (frameState n m a b ans caller (work+8) (max peak 13)).evaluate yExpression =
      some ⟨y,5⟩) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+19) (max peak 17), none, true⟩ := by
  have first : runFuel (fuel+8) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+4) (max peak 13), none, false⟩ := by
    simpa [Nat.add_assoc] using
      normalizeA_skip (fuel+6) n m a b ans caller work peak vn vm va vb vans ha
  have second : runFuel (fuel+7) normalizeB
      (frameState n m a b ans caller (work+4) (max peak 13)) =
      .finished ⟨frameState n m a b ans caller (work+8) (max peak 13), none, false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using
      normalizeB_skip (fuel+5) n m a b ans caller (work+4) (max peak 13) vn vm va vb vans hb
  have declaration : runFuel (fuel+6) declareY
      (frameState n m a b ans caller (work+8) (max peak 13)) =
      .finished ⟨yState n m a b ans y caller (work+14) (max peak 17), none, false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using
      declareY_runs (fuel+4) n m a b ans y caller (work+8) (max peak 13) he vy
  have stop : runFuel (fuel+5) stopCheck
      (yState n m a b ans y caller (work+14) (max peak 17)) =
      .finished ⟨yState n m a b ans y caller (work+19) (max peak 17), none, true⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using
      stopCheck_breaks fuel n m a b ans y caller (work+14) (max peak 17)
        vn vm va vb vans vy hy
  have tail := sequence_breaking (fuel+5) stopCheck afterStop _ _ stop
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
      .finished ⟨frameState n m a b ans caller (work+19) (max peak 17), none, true⟩ := by
    simpa [Nat.add_assoc, frameState, yState, List.take_append, List.take_of_length_le] using inner
  have outer := scope_finished (fuel+10) _ _ _ cleaned
  rw [iteration_shape]
  simpa [Nat.add_assoc, frameState, List.take_of_length_le] using outer

theorem iteration_stop (fuel : Nat) (n m a b ans : Nat)
    (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (ha : a < m) (hb : b < m)
    (hans : ans < wordLimit) (hy : a*n+b < m) :
    runFuel (fuel+11) iteration (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+19) (max peak 17), none, true⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have yBound := normalized_y_bound n m a b hn hm ha hb
  exact iteration_stop_int fuel n m a b ans (a*n+b : Nat) caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a aBound) (unsigned64_valid b bBound)
    (unsigned64_valid ans hans) (unsigned64_valid (a*n+b) yBound)
    (Int.ofNat_lt.mpr ha) (Int.ofNat_lt.mpr hb) (Int.ofNat_lt.mpr hy)
    (frame_y n m a b ans caller (work+8) (max peak 13) hn hm ha hb hans)

def outerLoop : Stmt := match FloorSumUnsignedInstance.floor_sum_unsigned.body with
  | .scope (.sequence _ (.sequence loop _)) => loop
  | _ => .skip

def loopCondition : Expr := match outerLoop with
  | .whileLoop condition _ => condition
  | _ => .literal boolType 0

theorem outerLoop_shape : outerLoop = .whileLoop loopCondition iteration := rfl
theorem loopCondition_shape : loopCondition = .literal boolType 1 := rfl

theorem frame_loop_condition (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) :
    (frameState n m a b ans caller work peak).evaluate loopCondition = some ⟨1,1⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    loopCondition_shape]
  rfl

theorem while_finished_break (fuel : Nat) (condition : Expr) (body : Stmt)
    (s final : State) (result : Result)
    (he : s.evaluate condition = some result) (hvalue : result.value ≠ 0)
    (hb : runFuel fuel body (({s with work := s.work+result.work+1}).observe condition.nodes) =
      .finished ⟨final,none,true⟩) :
    runFuel (fuel+1) (.whileLoop condition body) s = .finished ⟨final,none,false⟩ := by
  change (do
    let result ← liftChecked (s.evaluate condition)
    let next := ({s with work := s.work+result.work+1}).observe condition.nodes
    if result.value == 0 then pure (⟨next,none,false⟩ : Step) else do
      let step ← runFuel fuel body next
      if step.returned.isSome then pure step
      else if step.breaking then pure {step with breaking := false}
      else runFuel fuel (.whileLoop condition body) step.state) = _
  simp only [he, liftChecked, bind, Outcome.bind, hvalue, beq_iff_eq,
    ite_false, hb]
  rfl

theorem outerLoop_stop (fuel : Nat) (n m a b ans : Nat)
    (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (ha : a < m) (hb : b < m)
    (hans : ans < wordLimit) (hy : a*n+b < m) :
    runFuel (fuel+12) outerLoop (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+21) (max peak 17), none, false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mBound : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have aBound : a < wordLimit := by omega
  have bBound : b < wordLimit := by omega
  have he := frame_loop_condition (n:Int) m a b ans caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m mBound)
    (unsigned64_valid a aBound) (unsigned64_valid b bBound) (unsigned64_valid ans hans)
  have body := iteration_stop fuel n m a b ans caller (work+2) (max peak 11)
    hn hm ha hb hans hy
  rw [outerLoop_shape]
  have finished := while_finished_break (fuel+11) loopCondition iteration
    (frameState n m a b ans caller work peak)
    (frameState n m a b ans caller (work+21) (max peak 17)) ⟨1,1⟩ he (by decide)
    (by simpa [frameState, State.observe, loopCondition_shape, Expr.nodes,
      Nat.add_assoc, Nat.max_assoc] using body)
  simpa [Nat.add_assoc] using finished

end Proofs.FloorSumState
