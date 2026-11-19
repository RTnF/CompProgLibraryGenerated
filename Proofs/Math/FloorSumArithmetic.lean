
namespace Proofs.FloorSumArithmetic

def wordLimit : Nat := 18446744073709551616
def inputLimit : Nat := 4294967296

def triangle (n : Nat) : Nat := n * (n - 1) / 2

-- The product is evaluated before division in the source.
theorem triangular_product_bound (n : Nat) (hn : n < inputLimit) :
    n * (n - 1) < wordLimit := by
  have hn' : n ≤ 4294967295 := by simp [inputLimit] at hn; omega
  have hp := Nat.mul_le_mul hn' (show n - 1 ≤ 4294967295 by omega)
  change n * (n - 1) < 18446744073709551616
  omega

theorem normalized_y_bound (n m a b : Nat) (hn : n < inputLimit)
    (hm : m < inputLimit) (ha : a < m) (hb : b < m) :
    a * n + b < wordLimit := by
  have hn' : n ≤ 4294967295 := by simp [inputLimit] at hn; omega
  have hm' : m ≤ 4294967295 := by simp [inputLimit] at hm; omega
  have hy := Nat.mul_le_mul (show a ≤ 4294967294 by omega) hn'
  change a * n + b < 18446744073709551616
  omega

-- The quotient becomes the next n, and a becomes the next modulus.
theorem normalized_transition (n m a b : Nat) (ha : a < m) (hb : b < m)
    (continues : m ≤ a * n + b) :
    0 < a ∧ a < m ∧ (a * n + b) / m ≤ n ∧ (a * n + b) % m < m := by
  have hm : 0 < m := by omega
  have hapos : 0 < a := by
    by_cases hz : a = 0
    · simp [hz] at continues
      omega
    · omega
  have prod := Nat.mul_le_mul_right n (show a ≤ m by omega)
  have upper : a * n + b < m * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have quot := Nat.div_lt_of_lt_mul upper
  have rem := Nat.mod_lt (a * n + b) hm
  omega

theorem reduction_preserves_domain (n m a b : Nat) (hn : n < inputLimit)
    (hm : m < inputLimit) (positive : 0 < m)
    (continues : m ≤ (a % m) * n + b % m) :
    0 < a % m ∧ a % m < m ∧ a % m < inputLimit ∧
    ((a % m) * n + b % m) / m < inputLimit ∧
    (a % m) * n + b % m < wordLimit := by
  have ha := Nat.mod_lt a positive
  have hb := Nat.mod_lt b positive
  have transition := normalized_transition n m (a % m) (b % m) ha hb continues
  have bound := normalized_y_bound n m (a % m) (b % m) hn hm ha hb
  omega

-- This auxiliary recursion only counts mathematical reduction rounds. Connecting
-- it to the generated C++ state interpreter is a separate proof obligation.

theorem triangle_intermediate_exact (n : Nat) (hn : n < inputLimit) :
    (n * ((n + wordLimit - 1) % wordLimit)) % wordLimit / 2 = triangle n := by
  by_cases hz : n = 0
  · simp [hz, triangle]
  · have small : n - 1 < wordLimit := by simp [inputLimit, wordLimit] at *; omega
    have sub : n + wordLimit - 1 = (n - 1) + wordLimit := by omega
    rw [sub, Nat.add_mod]
    simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (triangular_product_bound n hn)]
    rfl

def directSum (m a b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => directSum m a b n + (a * n + b) / m

def indexSum : Nat → Nat
  | 0 => 0
  | n + 1 => indexSum n + n

theorem term_normalization (i m a b : Nat) (positive : 0 < m) :
    (a * i + b) / m = (a % m * i + b % m) / m + (a / m) * i + b / m := by
  have num : a * i + b = (a % m * i + b % m) + m * ((a / m) * i + b / m) := by
    calc
      a * i + b = (a % m + m * (a / m)) * i + (b % m + m * (b / m)) := by
        rw [Nat.mod_add_div, Nat.mod_add_div]
      _ = _ := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [num, Nat.add_mul_div_left _ _ positive]
  omega

theorem directSum_normalization (n m a b : Nat) (positive : 0 < m) :
    directSum m a b n = indexSum n * (a / m) + n * (b / m) + directSum m (a % m) (b % m) n := by
  induction n with
  | zero => simp [directSum, indexSum]
  | succ n ih =>
    rw [directSum, ih, term_normalization n m a b positive, indexSum]
    simp [directSum, Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem double_indexSum (n : Nat) : 2 * indexSum n = n * (n - 1) := by
  induction n with
  | zero => simp [indexSum]
  | succ n ih =>
    simp only [indexSum, Nat.mul_add, ih, Nat.succ_sub_one]
    cases n with
    | zero => simp
    | succ k =>
      simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem indexSum_eq_triangle (n : Nat) : indexSum n = triangle n := by
  unfold triangle
  rw [← double_indexSum n, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

theorem directSum_normalization_triangle (n m a b : Nat) (positive : 0 < m) :
    directSum m a b n = triangle n * (a / m) + n * (b / m) + directSum m (a % m) (b % m) n := by
  simpa [indexSum_eq_triangle] using directSum_normalization n m a b positive

theorem directSum_stop (n m a b : Nat) (below : a * n + b < m) :
    directSum m a b n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have smaller : a * n + b < m := by
      rw [Nat.mul_succ] at below
      omega
    simp [directSum, ih smaller, Nat.div_eq_of_lt smaller]

def normalizedAns (n m a b ans : Nat) : Nat :=
  (ans + triangle n * (a / m) + n * (b / m)) % wordLimit

theorem normalization_preserves_accumulated_sum (n m a b ans : Nat) (positive : 0 < m) :
    (ans + directSum m a b n) % wordLimit =
      (normalizedAns n m a b ans + directSum m (a % m) (b % m) n) % wordLimit := by
  rw [directSum_normalization_triangle n m a b positive]
  simp [normalizedAns, Nat.add_assoc]

end Proofs.FloorSumArithmetic
