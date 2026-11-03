import Proofs.FloorSumArithmetic
namespace Proofs.FloorSumReciprocity
open Proofs.FloorSumArithmetic

def sum (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => sum n f + f n

theorem sum_congr (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (by intro i hi; exact h i (by omega)), h n (by omega)]

theorem sum_add (n : Nat) (f g : Nat → Nat) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sum_zero (n : Nat) : sum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum, ih]

theorem sum_swap (n h : Nat) (f : Nat → Nat → Nat) :
    sum n (fun i => sum h (f i)) = sum h (fun j => sum n (fun i => f i j)) := by
  induction n with
  | zero => simpa [sum] using (sum_zero h).symm
  | succ n ih =>
    simp only [sum]
    rw [ih]
    exact (sum_add h (fun j => sum n (fun i => f i j)) (f n)).symm

theorem sum_shift (n : Nat) (f : Nat → Nat) :
    sum n (fun i => f (i+1)) + f 0 = sum (n+1) f := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp only [sum] at *
    omega

theorem sum_reverse (n : Nat) (f : Nat → Nat) :
    sum n (fun i => f (n-1-i)) = sum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [sum, Nat.add_sub_cancel, Nat.sub_self]
    have hprefix : sum n (fun i => f (n-i)) = sum n (fun i => f (i+1)) := by
      calc
        _ = sum n (fun i => f ((n-1-i)+1)) := by
          apply sum_congr
          intro i hi
          congr 1
          omega
        _ = _ := ih (fun i => f (i+1))
    rw [hprefix, sum_shift]
    rfl

theorem count_below (n q : Nat) :
    sum n (fun i => if i+1 ≤ q then 1 else 0) = min n q := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    rw [sum, ih]
    by_cases h : n+1 ≤ q
    · simp [h, Nat.min_eq_left (by omega : n ≤ q), Nat.min_eq_left h]
    · have hn : q ≤ n := by omega
      simp [h, Nat.min_eq_right hn, Nat.min_eq_right (by omega : q ≤ n+1)]

theorem division_as_count (n x m : Nat) (positive : 0 < m) (bound : x/m ≤ n) :
    x/m = sum n (fun j => if m*(j+1) ≤ x then 1 else 0) := by
  have replace : sum n (fun j => if m*(j+1) ≤ x then 1 else 0) =
      sum n (fun j => if j+1 ≤ x/m then 1 else 0) := by
    apply sum_congr
    intro j hj
    have equivalent : m*(j+1) ≤ x ↔ j+1 ≤ x/m := by
      rw [Nat.le_div_iff_mul_le positive, Nat.mul_comm]
    simp [equivalent]
  rw [replace, count_below, Nat.min_eq_right bound]

theorem directSum_as_sum (n m a b : Nat) :
    directSum m a b n = sum n (fun i => (a*i+b)/m) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [directSum, sum, ih]


theorem reflected_rectangle (n m a b i j : Nat) (hi : i < n)
    (hj : j < (a*n+b)/m) :
    m * (((a*n+b)/m)-1-j+1) ≤ a * (n-1-i) + b ↔
      a * (i+1) ≤ m*j + (a*n+b)%m := by
  have relation := Nat.div_add_mod (a*n+b) m
  have boundA := Nat.mul_le_mul_left a (show i+1 ≤ n by omega)
  have boundM := Nat.mul_le_mul_left m (show j ≤ (a*n+b)/m by omega)
  have left : ((a*n+b)/m)-1-j+1 = (a*n+b)/m-j := by omega
  have right : n-1-i = n-(i+1) := by omega
  rw [left, right, Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  omega


theorem directSum_reciprocity (n m a b : Nat) (hm : 0 < m) (ha : 0 < a) (hb : b < m) :
    directSum m a b n = directSum a m ((a*n+b)%m) ((a*n+b)/m) := by
  let h := (a*n+b)/m
  let r := (a*n+b)%m
  rw [directSum_as_sum, directSum_as_sum]
  change sum n (fun i => (a*i+b)/m) = sum h (fun j => (m*j+r)/a)
  calc
    _ = sum n (fun i => sum h (fun j => if m*(j+1) ≤ a*i+b then 1 else 0)) := by
      apply sum_congr
      intro i hi
      apply division_as_count h (a*i+b) m hm
      have num := Nat.mul_le_mul_left a (show i ≤ n by omega)
      exact Nat.div_le_div_right (by omega : a*i+b ≤ a*n+b)
    _ = sum h (fun j => sum n (fun i => if m*(j+1) ≤ a*i+b then 1 else 0)) := sum_swap n h _
    _ = sum h (fun j => sum n (fun i => if m*(h-1-j+1) ≤ a*(n-1-i)+b then 1 else 0)) := by
      rw [← sum_reverse h (fun j => sum n (fun i => if m*(j+1) ≤ a*i+b then 1 else 0))]
      apply sum_congr
      intro j hj
      exact (sum_reverse n (fun i => if m*(h-1-j+1) ≤ a*i+b then 1 else 0)).symm
    _ = _ := by
      apply sum_congr
      intro j hj
      have product := Nat.mul_le_mul_left m (show j+1 ≤ h by omega)
      have relation := Nat.div_add_mod (a*n+b) m
      change m*h+r = a*n+b at relation
      rw [Nat.mul_succ] at product
      have upper : m*j+r < a*n := by omega
      have bound : (m*j+r)/a ≤ n := by
        have small := Nat.div_lt_of_lt_mul upper
        omega
      calc
        _ = sum n (fun i => if a*(i+1) ≤ m*j+r then 1 else 0) := by
          apply sum_congr
          intro i hi
          have equivalent := reflected_rectangle n m a b i j hi hj
          simp [h, r, equivalent]
        _ = _ := (division_as_count n (m*j+r) a ha bound).symm


-- Mathematical reduction with wrapped accumulation. FloorSumRound connects
-- this recursion to the generated while under the bounded C++ input domain.
def mathRun (n m a b ans : Nat) : Nat :=
  if _hm : m = 0 then ans % wordLimit
  else
    let ar := a % m
    let br := b % m
    let nextAns := normalizedAns n m a b ans
    let y := ar*n+br
    if y < m then nextAns
    else mathRun (y/m) ar m (y%m) nextAns
termination_by m
decreasing_by exact Nat.mod_lt a (by omega)

theorem mathRun_correct (n m a b ans : Nat) (positive : 0 < m) :
    mathRun n m a b ans = (ans + directSum m a b n) % wordLimit := by
  induction m using Nat.strongRecOn generalizing n a b ans with
  | ind m ih =>
    rw [mathRun]
    simp only [dite_eq_right (by omega : m ≠ 0)]
    have ha := Nat.mod_lt a positive
    have hb := Nat.mod_lt b positive
    have invariant := normalization_preserves_accumulated_sum n m a b ans positive
    split
    · rename_i stops
      have zero := directSum_stop n m (a%m) (b%m) stops
      rw [invariant, zero]
      simp [normalizedAns]
    · rename_i continues
      have transition := normalized_transition n m (a%m) (b%m) ha hb (by omega)
      rw [ih (a%m) ha ((a%m*n+b%m)/m) m ((a%m*n+b%m)%m)
        (normalizedAns n m a b ans) transition.1]
      have reciprocity := directSum_reciprocity n m (a%m) (b%m) positive transition.1 hb
      rw [invariant, reciprocity]

theorem mathRun_result_bound (n m a b ans : Nat) (positive : 0 < m) :
    mathRun n m a b ans < wordLimit := by
  rw [mathRun_correct n m a b ans positive]
  exact Nat.mod_lt _ (by decide)

end Proofs.FloorSumReciprocity
