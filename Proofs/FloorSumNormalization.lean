import Proofs.FloorSumState

namespace Proofs.FloorSumNormalization
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.FloorSumState
open Proofs.FloorSumArithmetic

def bAnsExpression : Expr := match yesB with
  | .scope (.scope (.sequence (.assign _ e) _)) => e
  | _ => .literal unsigned64 0

def bRemExpression : Expr := match yesB with
  | .scope (.scope (.sequence _ (.sequence (.assign _ e) _))) => e
  | _ => .literal unsigned64 0

theorem bAnsExpression_shape : bAnsExpression = .binary unsigned64 .add
    (.variable unsigned64 4) (.binary unsigned64 .mul (.variable unsigned64 0)
      (.divrem unsigned64 false (.variable unsigned64 3) (.variable unsigned64 1))) := rfl

theorem bRemExpression_shape : bRemExpression =
    .divrem unsigned64 true (.variable unsigned64 3) (.variable unsigned64 1) := rfl

theorem yesB_shape : yesB = .scope (.scope (.sequence (.assign 4 bAnsExpression)
    (.sequence (.assign 3 bRemExpression) .skip))) := rfl

theorem unsigned64_convert_nat (v : Nat) :
    unsigned64.convert (v : Int) = some ((v % wordLimit : Nat) : Int) := by
  simp [unsigned64, Ty.convert, wordLimit, Int.natCast_emod]

theorem bAns_eval_int (n m a b ans p result : Int)
    (vn : unsigned64.valid n = true) (vb : unsigned64.valid b = true)
    (vm : unsigned64.valid m = true) (vans : unsigned64.valid ans = true)
    (hm : m ≠ 0) (vq : unsigned64.valid (b.tdiv m) = true)
    (product : unsigned64.convert (n*b.tdiv m) = some p)
    (total : unsigned64.convert (ans+p) = some result) :
    bAnsExpression.eval [n,m,a,b,ans] = some ⟨result,7⟩ := by
  rw [bAnsExpression_shape]
  have hd := checkedDivRem_division_exact unsigned64 b m hm vq
  simp [Expr.eval, vn,vb,vm,vans, hd, binaryValue, product,total]

theorem frame_bAns_int (n m a b ans p result : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (hm : m ≠ 0)
    (vq : unsigned64.valid (b.tdiv m) = true)
    (product : unsigned64.convert (n*b.tdiv m) = some p)
    (total : unsigned64.convert (ans+p) = some result) :
    (frameState n m a b ans caller work peak).evaluate bAnsExpression = some ⟨result,7⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans]
  exact bAns_eval_int n m a b ans p result vn vb vm vans hm vq product total

theorem bAns_evaluate (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    (frameState n m a b ans caller work peak).evaluate bAnsExpression =
      some ⟨((ans+n*(b/m)) % wordLimit : Nat),7⟩ := by
  have vn := unsigned64_valid n hn
  have vm := unsigned64_valid m hm
  have va := unsigned64_valid a ha
  have vb := unsigned64_valid b hb
  have vans := unsigned64_valid ans hans
  have qBound : b/m < wordLimit := by have := Nat.div_le_self b m; omega
  have vq : unsigned64.valid ((b:Int).tdiv m) = true := by
    simpa only [← Int.ofNat_tdiv] using unsigned64_valid (b/m) qBound
  have product : unsigned64.convert ((n:Int)*(b:Int).tdiv m) =
      some ((n*(b/m) % wordLimit : Nat) : Int) := by
    simpa only [← Int.ofNat_tdiv, Int.natCast_mul] using unsigned64_convert_nat (n*(b/m))
  have total : unsigned64.convert ((ans:Int) + ((n*(b/m)%wordLimit : Nat):Int)) =
      some (((ans+n*(b/m))%wordLimit : Nat):Int) := by
    simpa only [Int.natCast_add, Nat.add_mod_mod] using
      unsigned64_convert_nat (ans+n*(b/m)%wordLimit)
  exact frame_bAns_int n m a b ans (n*(b/m)%wordLimit : Nat)
    ((ans+n*(b/m))%wordLimit : Nat) caller work peak vn vm va vb vans (by omega) vq product total

theorem bRem_evaluate_int (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (hm : m ≠ 0)
    (vq : unsigned64.valid (b.tdiv m) = true) (vr : unsigned64.valid (b.tmod m) = true) :
    (frameState n m a b ans caller work peak).evaluate bRemExpression = some ⟨b.tmod m,3⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    bRemExpression_shape]
  have hd := checkedDivRem_remainder_exact unsigned64 b m hm vq vr
  simp [Expr.eval, vb,vm,hd]

theorem bRem_evaluate (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    (frameState n m a b ans caller work peak).evaluate bRemExpression = some ⟨(b%m : Nat),3⟩ := by
  have qBound : b/m < wordLimit := by have := Nat.div_le_self b m; omega
  have rBound : b%m < wordLimit := by have := Nat.mod_lt b positive; omega
  simpa only [← Int.ofNat_tmod] using
    bRem_evaluate_int (n:Int) m a b ans caller work peak
      (unsigned64_valid n hn) (unsigned64_valid m hm) (unsigned64_valid a ha)
      (unsigned64_valid b hb) (unsigned64_valid ans hans) (by omega)
      (by simpa only [← Int.ofNat_tdiv] using unsigned64_valid (b/m) qBound)
      (by simpa only [← Int.ofNat_tmod] using unsigned64_valid (b%m) rBound)

theorem frame_assign_ans (fuel : Nat) (n m a b ans result : Int) (caller : List Cell)
    (work peak cost : Nat) (e : Expr)
    (he : (frameState n m a b ans caller work peak).evaluate e = some ⟨result,cost⟩)
    (vr : unsigned64.valid result = true) (hnodes : e.nodes = cost) :
    runFuel (fuel+1) (.assign 4 e) (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b result caller (work+cost+1) (max peak (10+cost)),none,false⟩ := by
  have cv := Ty.convert_of_valid unsigned64 result vr
  have h4 : ¬caller.length+4 < caller.length := by omega
  simp only [frameState] at he
  simp [runFuel, Stmt.run, frameState, List.getElem?_append, h4, he, cv,
    List.set_append_right, State.observe, hnodes, Nat.add_assoc, liftChecked]

theorem frame_assign_b (fuel : Nat) (n m a b ans result : Int) (caller : List Cell)
    (work peak : Nat) (e : Expr)
    (he : (frameState n m a b ans caller work peak).evaluate e = some ⟨result,3⟩)
    (vr : unsigned64.valid result = true) (hnodes : e.nodes = 3) :
    runFuel (fuel+1) (.assign 3 e) (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a result ans caller (work+4) (max peak 13),none,false⟩ := by
  have cv := Ty.convert_of_valid unsigned64 result vr
  have h3 : ¬caller.length+3 < caller.length := by omega
  simp only [frameState] at he
  simp [runFuel, Stmt.run, frameState, List.getElem?_append, h3, he, cv,
    List.set_append_right, State.observe, hnodes, Nat.add_assoc, liftChecked]

def bAns (n m b ans : Nat) : Nat := (ans+n*(b/m)) % wordLimit

theorem bAns_bound (n m b ans : Nat) : bAns n m b ans < wordLimit := by
  exact Nat.mod_lt _ (by decide)

theorem yesB_runs (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    runFuel (fuel+5) yesB (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller
        (work+12) (max peak 17),none,false⟩ := by
  have resultBound := bAns_bound n m b ans
  have remBound : b%m < wordLimit := by have := Nat.mod_lt b positive; omega
  have first : runFuel (fuel+2) (.assign 4 bAnsExpression)
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b (bAns n m b ans) caller (work+8) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, bAns] using
      frame_assign_ans (fuel+1) (n:Int) m a b ans (bAns n m b ans) caller work peak 7
        bAnsExpression (bAns_evaluate n m a b ans caller work peak hn hm ha hb hans positive)
        (unsigned64_valid (bAns n m b ans) resultBound)
        (by rw [bAnsExpression_shape]; rfl)
  have second : runFuel (fuel+1) (.assign 3 bRemExpression)
      (frameState n m a b (bAns n m b ans) caller (work+8) (max peak 17)) =
      .finished ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller
        (work+12) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using
      frame_assign_b fuel (n:Int) m a b (bAns n m b ans) (b%m : Nat) caller
        (work+8) (max peak 17) bRemExpression
        (bRem_evaluate n m a b (bAns n m b ans) caller (work+8) (max peak 17)
          hn hm ha hb resultBound positive)
        (unsigned64_valid (b%m) remBound) (by rw [bRemExpression_shape]; rfl)
  have tail := sequence_finished (fuel+1) (.assign 3 bRemExpression) .skip _ _
    ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller (work+12) (max peak 17),none,false⟩
    second (by rfl)
  have core := sequence_finished (fuel+2) (.assign 4 bAnsExpression)
    (.sequence (.assign 3 bRemExpression) .skip) _ _ _ first
    (by simpa [Nat.add_assoc] using tail)
  have inner := scope_finished (fuel+3) _ _ _ (by simpa [Nat.add_assoc] using core)
  have cleaned : runFuel (fuel+4) (.scope (.sequence (.assign 4 bAnsExpression)
      (.sequence (.assign 3 bRemExpression) .skip)))
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller
        (work+12) (max peak 17),none,false⟩ := by
    simpa [Nat.add_assoc, frameState, List.take_of_length_le] using inner
  have outer := scope_finished (fuel+4) _ _ _ cleaned
  rw [yesB_shape]
  simpa [Nat.add_assoc, frameState, List.take_of_length_le] using outer

theorem normalizeB_true (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) (hbranch : m ≤ b) :
    runFuel (fuel+6) normalizeB (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller
        (work+16) (max peak 17),none,false⟩ := by
  have he := frame_guardB (n:Int) m a b ans caller work peak
    (unsigned64_valid n hn) (unsigned64_valid m hm) (unsigned64_valid a ha)
    (unsigned64_valid b hb) (unsigned64_valid ans hans)
  simp only [Int.ofNat_le.mpr hbranch, ite_true] at he
  have body := yesB_runs fuel n m a b ans caller (work+4) (max peak 13)
    hn hm ha hb hans positive
  have next : ({frameState n m a b ans caller work peak with work := work+4}).observe guardB.nodes =
      frameState n m a b ans caller (work+4) (max peak 13) := by
    simp [frameState, State.observe, guardB_shape, Expr.nodes]
  rw [normalizeB_shape]
  change (do
    let result ← liftChecked ((frameState n m a b ans caller work peak).evaluate guardB)
    let next := ({frameState n m a b ans caller work peak with work := work+result.work+1}).observe guardB.nodes
    if result.value == 0 then runFuel (fuel+5) .skip next
    else runFuel (fuel+5) yesB next) = _
  simp only [he, liftChecked, bind, Outcome.bind]
  change runFuel (fuel+5) yesB
    (({frameState n m a b ans caller work peak with work := work+4}).observe guardB.nodes) = _
  rw [next]
  simpa [Nat.add_assoc,Nat.max_assoc] using body

theorem normalizeB_runs (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    runFuel (fuel+6) normalizeB (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a (b%m : Nat) (bAns n m b ans) caller
        (work + if m ≤ b then 16 else 4) (max peak (if m ≤ b then 17 else 13)),none,false⟩ := by
  by_cases hbranch : m ≤ b
  · simpa only [hbranch, ite_true] using
      normalizeB_true fuel n m a b ans caller work peak hn hm ha hb hans positive hbranch
  · have hlt : b < m := by omega
    have stop := normalizeB_skip (fuel+4) (n:Int) m a b ans caller work peak
      (unsigned64_valid n hn) (unsigned64_valid m hm) (unsigned64_valid a ha)
      (unsigned64_valid b hb) (unsigned64_valid ans hans) (Int.ofNat_lt.mpr hlt)
    simpa [hbranch, Nat.add_assoc, bAns, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hans] using stop

end Proofs.FloorSumNormalization
