import Proofs.FloorSumNormalization

namespace Proofs.FloorSumANormalization
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.FloorSumState
open Proofs.FloorSumArithmetic Proofs.FloorSumNormalization

def aAnsExpression : Expr := match yesA with
  | .scope (.scope (.sequence (.assign _ e) _)) => e
  | _ => .literal unsigned64 0

def aRemExpression : Expr := match yesA with
  | .scope (.scope (.sequence _ (.sequence (.assign _ e) _))) => e
  | _ => .literal unsigned64 0

def triangleExpression : Expr := match aAnsExpression with
  | .binary _ _ _ (.binary _ _ e _) => e
  | _ => .literal unsigned64 0

theorem triangleExpression_shape : triangleExpression = .divrem unsigned64 false
    (.binary unsigned64 .mul (.variable unsigned64 0)
      (.binary unsigned64 .sub (.variable unsigned64 0)
        (.cast unsigned64 (.literal ⟨32,true,false⟩ 1))))
    (.cast unsigned64 (.literal ⟨32,true,false⟩ 2)) := rfl

theorem aAnsExpression_shape : aAnsExpression = .binary unsigned64 .add
    (.variable unsigned64 4) (.binary unsigned64 .mul triangleExpression
      (.divrem unsigned64 false (.variable unsigned64 2) (.variable unsigned64 1))) := rfl

theorem aRemExpression_shape : aRemExpression =
    .divrem unsigned64 true (.variable unsigned64 2) (.variable unsigned64 1) := rfl

theorem yesA_shape : yesA = .scope (.scope (.sequence (.assign 4 aAnsExpression)
    (.sequence (.assign 2 aRemExpression) .skip))) := rfl

theorem triangle_eval_int (n m a b ans pred product : Int)
    (vn : unsigned64.valid n = true)
    (hs : unsigned64.convert (n-1) = some pred)
    (hp : unsigned64.convert (n*pred) = some product)
    (vq : unsigned64.valid (product.tdiv 2) = true) :
    triangleExpression.eval [n,m,a,b,ans] = some ⟨product.tdiv 2,9⟩ := by
  rw [triangleExpression_shape]
  have c1 : unsigned64.convert 1 = some 1 := by decide
  have c2 : unsigned64.convert 2 = some 2 := by decide
  have l1 : (⟨32,true,false⟩ : Ty).valid 1 = true := by decide
  have l2 : (⟨32,true,false⟩ : Ty).valid 2 = true := by decide
  have hd := checkedDivRem_division_exact unsigned64 product 2 (by decide) vq
  simp [Expr.eval,vn,c1,c2,l1,l2,binaryValue,hs,hp,hd]

theorem triangle_eval (n m a b ans : Nat) (hn : n < inputLimit) :
    triangleExpression.eval [(n:Int),m,a,b,ans] = some ⟨(triangle n : Nat),9⟩ := by
  by_cases hz : n = 0
  · subst n
    have zero := triangle_eval_int 0 m a b ans (wordLimit-1 : Nat) 0
      (by decide) (by decide) (by decide) (by decide)
    simpa [triangle] using zero
  · have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
    have predBound : n-1 < wordLimit := by omega
    have productBound := triangular_product_bound n hn
    have qBound : n*(n-1)/2 < wordLimit := by
      have := Nat.div_le_self (n*(n-1)) 2
      omega
    have sub : (n:Int)-1 = ((n-1 : Nat):Int) := by omega
    have hs : unsigned64.convert ((n:Int)-1) = some ((n-1 : Nat):Int) := by
      rw [sub]
      exact Ty.convert_of_valid unsigned64 _ (unsigned64_valid (n-1) predBound)
    have hp : unsigned64.convert ((n:Int)*((n-1 : Nat):Int)) = some ((n*(n-1) : Nat):Int) := by
      simpa only [Int.natCast_mul] using
        Ty.convert_of_valid unsigned64 ((n*(n-1) : Nat):Int) (unsigned64_valid _ productBound)
    have qeq : (((n*(n-1) : Nat):Int).tdiv 2) = ((n*(n-1)/2 : Nat):Int) := rfl
    have vq : unsigned64.valid (((n*(n-1) : Nat):Int).tdiv 2) = true := by
      rw [qeq]
      exact unsigned64_valid (n*(n-1)/2) qBound
    simpa only [qeq, triangle] using
      triangle_eval_int (n:Int) m a b ans (n-1 : Nat) (n*(n-1) : Nat)
        (unsigned64_valid n nBound) hs hp vq

theorem aAns_eval_int (n m a b ans tri p result : Int)
    (ht : triangleExpression.eval [n,m,a,b,ans] = some ⟨tri,9⟩)
    (va : unsigned64.valid a = true) (vm : unsigned64.valid m = true)
    (vans : unsigned64.valid ans = true) (hm : m ≠ 0)
    (vq : unsigned64.valid (a.tdiv m) = true)
    (product : unsigned64.convert (tri*a.tdiv m) = some p)
    (total : unsigned64.convert (ans+p) = some result) :
    aAnsExpression.eval [n,m,a,b,ans] = some ⟨result,15⟩ := by
  rw [aAnsExpression_shape]
  have hd := checkedDivRem_division_exact unsigned64 a m hm vq
  simp [Expr.eval,ht,va,vm,vans,hd,binaryValue,product,total]

theorem frame_aAns_int (n m a b ans tri p result : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (hm : m ≠ 0)
    (ht : triangleExpression.eval [n,m,a,b,ans] = some ⟨tri,9⟩)
    (vq : unsigned64.valid (a.tdiv m) = true)
    (product : unsigned64.convert (tri*a.tdiv m) = some p)
    (total : unsigned64.convert (ans+p) = some result) :
    (frameState n m a b ans caller work peak).evaluate aAnsExpression = some ⟨result,15⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans]
  exact aAns_eval_int n m a b ans tri p result ht va vm vans hm vq product total

theorem aAns_evaluate (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    (frameState n m a b ans caller work peak).evaluate aAnsExpression =
      some ⟨((ans+triangle n*(a/m))%wordLimit : Nat),15⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have qBound : a/m < wordLimit := by have := Nat.div_le_self a m; omega
  have vq : unsigned64.valid ((a:Int).tdiv m) = true := by
    simpa only [← Int.ofNat_tdiv] using unsigned64_valid (a/m) qBound
  have product : unsigned64.convert ((triangle n:Int)*(a:Int).tdiv m) =
      some ((triangle n*(a/m)%wordLimit : Nat):Int) := by
    simpa only [← Int.ofNat_tdiv, Int.natCast_mul] using unsigned64_convert_nat (triangle n*(a/m))
  have total : unsigned64.convert ((ans:Int)+((triangle n*(a/m)%wordLimit : Nat):Int)) =
      some (((ans+triangle n*(a/m))%wordLimit : Nat):Int) := by
    simpa only [Int.natCast_add, Nat.add_mod_mod] using
      unsigned64_convert_nat (ans+triangle n*(a/m)%wordLimit)
  exact frame_aAns_int n m a b ans (triangle n) (triangle n*(a/m)%wordLimit : Nat)
    ((ans+triangle n*(a/m))%wordLimit : Nat) caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m hm) (unsigned64_valid a ha)
    (unsigned64_valid b hb) (unsigned64_valid ans hans) (by omega)
    (triangle_eval n m a b ans hn) vq product total

theorem aRem_evaluate_int (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (vn : unsigned64.valid n = true) (vm : unsigned64.valid m = true)
    (va : unsigned64.valid a = true) (vb : unsigned64.valid b = true)
    (vans : unsigned64.valid ans = true) (hm : m ≠ 0)
    (vq : unsigned64.valid (a.tdiv m) = true) (vr : unsigned64.valid (a.tmod m) = true) :
    (frameState n m a b ans caller work peak).evaluate aRemExpression = some ⟨a.tmod m,3⟩ := by
  rw [State.evaluate, frame_environment n m a b ans caller work peak vn vm va vb vans,
    aRemExpression_shape]
  have hd := checkedDivRem_remainder_exact unsigned64 a m hm vq vr
  simp [Expr.eval, va,vm,hd]

theorem aRem_evaluate (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < wordLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    (frameState n m a b ans caller work peak).evaluate aRemExpression = some ⟨(a%m : Nat),3⟩ := by
  have qBound : a/m < wordLimit := by have := Nat.div_le_self a m; omega
  have rBound : a%m < wordLimit := by have := Nat.mod_lt a positive; omega
  simpa only [← Int.ofNat_tmod] using
    aRem_evaluate_int (n:Int) m a b ans caller work peak
      (unsigned64_valid n hn) (unsigned64_valid m hm) (unsigned64_valid a ha)
      (unsigned64_valid b hb) (unsigned64_valid ans hans) (by omega)
      (by simpa only [← Int.ofNat_tdiv] using unsigned64_valid (a/m) qBound)
      (by simpa only [← Int.ofNat_tmod] using unsigned64_valid (a%m) rBound)

theorem frame_assign_a (fuel : Nat) (n m a b ans result : Int) (caller : List Cell)
    (work peak : Nat) (e : Expr)
    (he : (frameState n m a b ans caller work peak).evaluate e = some ⟨result,3⟩)
    (vr : unsigned64.valid result = true) (hnodes : e.nodes = 3) :
    runFuel (fuel+1) (.assign 2 e) (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m result b ans caller (work+4) (max peak 13),none,false⟩ := by
  have cv := Ty.convert_of_valid unsigned64 result vr
  have h2 : ¬caller.length+2 < caller.length := by omega
  simp only [frameState] at he
  simp [runFuel, Stmt.run, frameState, List.getElem?_append, h2, he, cv,
    List.set_append_right, State.observe, hnodes, Nat.add_assoc, liftChecked]

def aAns (n m a ans : Nat) : Nat := (ans+triangle n*(a/m)) % wordLimit

theorem aAns_bound (n m a ans : Nat) : aAns n m a ans < wordLimit := by
  exact Nat.mod_lt _ (by decide)

theorem yesA_runs (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    runFuel (fuel+5) yesA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller
        (work+20) (max peak 25),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have resultBound := aAns_bound n m a ans
  have remBound : a%m < wordLimit := by have := Nat.mod_lt a positive; omega
  have first : runFuel (fuel+2) (.assign 4 aAnsExpression)
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b (aAns n m a ans) caller (work+16) (max peak 25),none,false⟩ := by
    simpa [Nat.add_assoc, aAns] using
      frame_assign_ans (fuel+1) (n:Int) m a b ans (aAns n m a ans) caller work peak 15
        aAnsExpression (aAns_evaluate n m a b ans caller work peak hn hm ha hb hans positive)
        (unsigned64_valid (aAns n m a ans) resultBound)
        (by rw [aAnsExpression_shape]; rfl)
  have second : runFuel (fuel+1) (.assign 2 aRemExpression)
      (frameState n m a b (aAns n m a ans) caller (work+16) (max peak 25)) =
      .finished ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller
        (work+20) (max peak 25),none,false⟩ := by
    simpa [Nat.add_assoc, Nat.max_assoc] using
      frame_assign_a fuel (n:Int) m a b (aAns n m a ans) (a%m : Nat) caller
        (work+16) (max peak 25) aRemExpression
        (aRem_evaluate n m a b (aAns n m a ans) caller (work+16) (max peak 25)
          nBound hm ha hb resultBound positive)
        (unsigned64_valid (a%m) remBound) (by rw [aRemExpression_shape]; rfl)
  have tail := sequence_finished (fuel+1) (.assign 2 aRemExpression) .skip _ _
    ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller (work+20) (max peak 25),none,false⟩
    second (by rfl)
  have core := sequence_finished (fuel+2) (.assign 4 aAnsExpression)
    (.sequence (.assign 2 aRemExpression) .skip) _ _ _ first
    (by simpa [Nat.add_assoc] using tail)
  have inner := scope_finished (fuel+3) _ _ _ (by simpa [Nat.add_assoc] using core)
  have cleaned : runFuel (fuel+4) (.scope (.sequence (.assign 4 aAnsExpression)
      (.sequence (.assign 2 aRemExpression) .skip)))
      (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller
        (work+20) (max peak 25),none,false⟩ := by
    simpa [Nat.add_assoc, frameState, List.take_of_length_le] using inner
  have outer := scope_finished (fuel+4) _ _ _ cleaned
  rw [yesA_shape]
  simpa [Nat.add_assoc, frameState, List.take_of_length_le] using outer

theorem normalizeA_true (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) (hbranch : m ≤ a) :
    runFuel (fuel+6) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller
        (work+24) (max peak 25),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have he := frame_guardA (n:Int) m a b ans caller work peak
    (unsigned64_valid n nBound) (unsigned64_valid m hm) (unsigned64_valid a ha)
    (unsigned64_valid b hb) (unsigned64_valid ans hans)
  simp only [Int.ofNat_le.mpr hbranch, ite_true] at he
  have body := yesA_runs fuel n m a b ans caller (work+4) (max peak 13)
    hn hm ha hb hans positive
  have next : ({frameState n m a b ans caller work peak with work := work+4}).observe guardA.nodes =
      frameState n m a b ans caller (work+4) (max peak 13) := by
    simp [frameState, State.observe, guardA_shape, Expr.nodes]
  rw [normalizeA_shape]
  change (do
    let result ← liftChecked ((frameState n m a b ans caller work peak).evaluate guardA)
    let next := ({frameState n m a b ans caller work peak with work := work+result.work+1}).observe guardA.nodes
    if result.value == 0 then runFuel (fuel+5) .skip next
    else runFuel (fuel+5) yesA next) = _
  simp only [he, liftChecked, bind, Outcome.bind]
  change runFuel (fuel+5) yesA
    (({frameState n m a b ans caller work peak with work := work+4}).observe guardA.nodes) = _
  rw [next]
  simpa [Nat.add_assoc,Nat.max_assoc] using body

theorem normalizeA_runs (fuel : Nat) (n m a b ans : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    runFuel (fuel+6) normalizeA (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) b (aAns n m a ans) caller
        (work + if m ≤ a then 24 else 4) (max peak (if m ≤ a then 25 else 13)),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  by_cases hbranch : m ≤ a
  · simpa only [hbranch, ite_true] using
      normalizeA_true fuel n m a b ans caller work peak hn hm ha hb hans positive hbranch
  · have hlt : a < m := by omega
    have stop := normalizeA_skip (fuel+4) (n:Int) m a b ans caller work peak
      (unsigned64_valid n nBound) (unsigned64_valid m hm) (unsigned64_valid a ha)
      (unsigned64_valid b hb) (unsigned64_valid ans hans) (Int.ofNat_lt.mpr hlt)
    simpa [hbranch, Nat.add_assoc, aAns, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hans] using stop

theorem bAns_after_aAns (n m a b ans : Nat) :
    bAns n m b (aAns n m a ans) = normalizedAns n m a b ans := by
  simp [bAns,aAns,normalizedAns]

def normalizationWork (m a b : Nat) : Nat :=
  (if m ≤ a then 24 else 4) + (if m ≤ b then 16 else 4)

def normalizationPeak (m a b : Nat) : Nat :=
  max (if m ≤ a then 25 else 13) (if m ≤ b then 17 else 13)

theorem normalizationWork_bound (m a b : Nat) : normalizationWork m a b ≤ 40 := by
  by_cases ha : m ≤ a <;> by_cases hb : m ≤ b <;> simp [normalizationWork,ha,hb]

theorem normalizationPeak_bound (m a b : Nat) : normalizationPeak m a b ≤ 25 := by
  by_cases ha : m ≤ a <;> by_cases hb : m ≤ b <;> simp [normalizationPeak,ha,hb]

theorem normalizations_runs (fuel : Nat) (n m a b ans : Nat)
    (caller : List Cell) (work peak : Nat)
    (hn : n < inputLimit) (hm : m < wordLimit) (ha : a < wordLimit)
    (hb : b < wordLimit) (hans : ans < wordLimit) (positive : 0 < m) :
    runFuel (fuel+7) (.sequence normalizeA normalizeB) (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m (a%m : Nat) (b%m : Nat) (normalizedAns n m a b ans) caller
        (work+normalizationWork m a b) (max peak (normalizationPeak m a b)),none,false⟩ := by
  have nBound : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have remBound : a%m < wordLimit := by have := Nat.mod_lt a positive; omega
  have first := normalizeA_runs fuel n m a b ans caller work peak hn hm ha hb hans positive
  have second := normalizeB_runs fuel n m (a%m) b (aAns n m a ans) caller
    (work + if m ≤ a then 24 else 4) (max peak (if m ≤ a then 25 else 13))
    nBound hm remBound hb (aAns_bound n m a ans) positive
  have finished := sequence_finished (fuel+6) normalizeA normalizeB _ _ _ first second
  simpa [Nat.add_assoc, Nat.max_assoc, bAns_after_aAns, normalizationWork, normalizationPeak]
    using finished

end Proofs.FloorSumANormalization
