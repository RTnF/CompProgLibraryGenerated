import Mathlib.Algebra.Ring.Defs

/-! Square matrices as functions of the indices `i, j < n` over a semiring: the product as the left fold computed by
`SquareMatrix::operator*=`, its associativity and identity, and powers. -/

namespace Proofs.Cpp.SquareMatrixMath

variable {T : Type}

/-- `((0 + f 0) + f 1) + ... + f (n - 1)`. -/
def Sum [Zero T] [Add T] (n : Nat) (f : Nat → T) : T := (List.range n).foldl (fun s t => s + f t) 0

theorem Sum_zero [Zero T] [Add T] (f : Nat → T) : Sum 0 f = 0 := rfl

theorem Sum_succ [Zero T] [Add T] (n : Nat) (f : Nat → T) : Sum (n + 1) f = Sum n f + f n := by
  unfold Sum
  rw [List.range_succ, List.foldl_append]
  simp

theorem Sum_congr [Zero T] [Add T] (n : Nat) (f g : Nat → T) (h : ∀ t, t < n → f t = g t) : Sum n f = Sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Sum_succ, Sum_succ, ih (fun t ht => h t (by omega)), h n (by omega)]

theorem Sum_add [AddCommMonoid T] (n : Nat) (f g : Nat → T) :
    Sum n (fun t => f t + g t) = Sum n f + Sum n g := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih =>
    rw [Sum_succ, Sum_succ, Sum_succ, ih, add_assoc, add_assoc]
    congr 1
    rw [← add_assoc, add_comm (Sum n g) (f n), add_assoc]

theorem Sum_mul_left [Semiring T] (n : Nat) (x : T) (f : Nat → T) : Sum n (fun t => x * f t) = x * Sum n f := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih => rw [Sum_succ, Sum_succ, ih, mul_add]

theorem Sum_mul_right [Semiring T] (n : Nat) (x : T) (f : Nat → T) : Sum n (fun t => f t * x) = Sum n f * x := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih => rw [Sum_succ, Sum_succ, ih, add_mul]

theorem Sum_zero_fun [AddMonoid T] (n : Nat) : Sum n (fun _ => (0 : T)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Sum_succ, ih, add_zero]

theorem Sum_swap [AddCommMonoid T] (n m : Nat) (g : Nat → Nat → T) :
    Sum n (fun t => Sum m (fun k => g t k)) = Sum m (fun k => Sum n (fun t => g t k)) := by
  induction n with
  | zero => rw [Sum_zero]; exact (Sum_zero_fun m).symm
  | succ n ih => rw [Sum_succ, ih, ← Sum_add]; apply Sum_congr; intro k _; rw [Sum_succ]

/-- The matrix product (entries `i, j < n`). -/
def mulF [Zero T] [Add T] [Mul T] (n : Nat) (A B : Nat → Nat → T) : Nat → Nat → T :=
  fun i j => Sum n (fun t => A i t * B t j)

/-- The identity matrix. -/
def Idm [Zero T] [One T] : Nat → Nat → T := fun i j => if i = j then 1 else 0

/-- Equality of the entries `i, j < n`. -/
def EqOn (n : Nat) (A B : Nat → Nat → T) : Prop := ∀ i j, i < n → j < n → A i j = B i j

theorem EqOn_refl (n : Nat) (A : Nat → Nat → T) : EqOn n A A := fun _ _ _ _ => rfl

theorem EqOn_symm {n : Nat} {A B : Nat → Nat → T} (h : EqOn n A B) : EqOn n B A :=
  fun i j hi hj => (h i j hi hj).symm

theorem EqOn_trans {n : Nat} {A B C : Nat → Nat → T} (h1 : EqOn n A B) (h2 : EqOn n B C) : EqOn n A C :=
  fun i j hi hj => (h1 i j hi hj).trans (h2 i j hi hj)

theorem mulF_congr [Zero T] [Add T] [Mul T] (n : Nat) (A A' B B' : Nat → Nat → T) (hA : EqOn n A A')
    (hB : EqOn n B B') : EqOn n (mulF n A B) (mulF n A' B') := by
  intro i j hi hj
  unfold mulF
  apply Sum_congr
  intro t ht
  rw [hA i t hi ht, hB t j ht hj]

theorem mulF_assoc [Semiring T] (n : Nat) (A B C : Nat → Nat → T) :
    mulF n (mulF n A B) C = mulF n A (mulF n B C) := by
  funext i j
  unfold mulF
  have e1 : Sum n (fun t => Sum n (fun k => A i k * B k t) * C t j) =
      Sum n (fun t => Sum n (fun k => A i k * B k t * C t j)) := by
    apply Sum_congr; intro t _; rw [Sum_mul_right]
  have e2 : Sum n (fun k => A i k * Sum n (fun t => B k t * C t j)) =
      Sum n (fun k => Sum n (fun t => A i k * (B k t * C t j))) := by
    apply Sum_congr; intro k _; rw [Sum_mul_left]
  rw [e1, e2, Sum_swap]
  apply Sum_congr; intro k _
  apply Sum_congr; intro t _
  rw [mul_assoc]

theorem Sum_ite_left [Semiring T] (n i : Nat) (f : Nat → T) :
    Sum n (fun t => (if i = t then (1 : T) else 0) * f t) = if i < n then f i else 0 := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih =>
    rw [Sum_succ, ih]
    by_cases h : i < n
    · have : i ≠ n := by omega
      simp [h, this, show i < n + 1 by omega]
    · by_cases h2 : i = n
      · subst h2; simp [h]
      · have : ¬ i < n + 1 := by omega
        simp [h, h2, this]

theorem Sum_ite_right [Semiring T] (n j : Nat) (f : Nat → T) :
    Sum n (fun t => f t * (if t = j then (1 : T) else 0)) = if j < n then f j else 0 := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih =>
    rw [Sum_succ, ih]
    by_cases h : j < n
    · have : n ≠ j := by omega
      simp [h, this, show j < n + 1 by omega]
    · by_cases h2 : j = n
      · subst h2; simp [h]
      · have : ¬ j < n + 1 := by omega
        have h3 : n ≠ j := by omega
        simp [h, this, h3]

theorem mulF_one_left [Semiring T] (n : Nat) (X : Nat → Nat → T) : EqOn n (mulF n Idm X) X := by
  intro i j hi _
  unfold mulF Idm
  rw [Sum_ite_left n i (fun t => X t j)]; simp [hi]

theorem mulF_one_right [Semiring T] (n : Nat) (X : Nat → Nat → T) : EqOn n (mulF n X Idm) X := by
  intro i j _ hj
  unfold mulF Idm
  rw [Sum_ite_right n j (fun t => X i t)]; simp [hj]

/-- `A^k` by right multiplication. -/
def PW [Semiring T] (n : Nat) (A : Nat → Nat → T) : Nat → Nat → Nat → T
  | 0 => Idm
  | k + 1 => mulF n (PW n A k) A

theorem PW_add [Semiring T] (n : Nat) (A : Nat → Nat → T) (i : Nat) :
    ∀ j, EqOn n (PW n A (i + j)) (mulF n (PW n A i) (PW n A j)) := by
  intro j
  induction j with
  | zero => exact EqOn_symm (mulF_one_right n _)
  | succ j ih =>
    have h1 : EqOn n (mulF n (PW n A (i + j)) A) (mulF n (mulF n (PW n A i) (PW n A j)) A) :=
      mulF_congr n _ _ _ _ ih (EqOn_refl n A)
    have h2 : mulF n (mulF n (PW n A i) (PW n A j)) A = mulF n (PW n A i) (PW n A (j + 1)) := by
      rw [mulF_assoc]; rfl
    rw [h2] at h1
    exact h1

theorem PW_congr [Semiring T] (n : Nat) (A A' : Nat → Nat → T) (h : EqOn n A' A) :
    ∀ k, EqOn n (PW n A' k) (PW n A k) := by
  intro k
  induction k with
  | zero => exact EqOn_refl n _
  | succ k ih => exact mulF_congr n _ _ _ _ ih h

theorem PW_sq [Semiring T] (n : Nat) (Y : Nat → Nat → T) :
    ∀ k, EqOn n (PW n (mulF n Y Y) k) (PW n Y (2 * k)) := by
  intro k
  induction k with
  | zero => exact EqOn_refl n _
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [e]
    have h2 := PW_add n Y (2 * k) 2
    have h1 : EqOn n (mulF n (PW n (mulF n Y Y) k) (mulF n Y Y)) (mulF n (PW n Y (2 * k)) (mulF n Y Y)) :=
      mulF_congr n _ _ _ _ ih (EqOn_refl n _)
    have h3 : EqOn n (PW n Y 2) (mulF n Y Y) := by
      show EqOn n (mulF n (mulF n Idm Y) Y) (mulF n Y Y)
      exact mulF_congr n _ _ _ _ (mulF_one_left n Y) (EqOn_refl n Y)
    exact EqOn_trans h1 (EqOn_trans (mulF_congr n _ _ _ _ (EqOn_refl n _) (EqOn_symm h3)) (EqOn_symm h2))

/-- One round of binary exponentiation keeps `R * Y^e`: `(R * Y) * (Y * Y)^(e / 2)` for odd `e`, `R * (Y * Y)^(e / 2)`
for even `e`. -/
theorem pow_round [Semiring T] (n : Nat) (R Y : Nat → Nat → T) (e : Nat) :
    EqOn n (mulF n (if e % 2 = 1 then mulF n R Y else R) (PW n (mulF n Y Y) (e / 2))) (mulF n R (PW n Y e)) := by
  have hsq : EqOn n (PW n (mulF n Y Y) (e / 2)) (PW n Y (2 * (e / 2))) := PW_sq n Y (e / 2)
  split
  · rename_i h
    have he : e = 1 + 2 * (e / 2) := by omega
    have h1 : EqOn n (mulF n (mulF n R Y) (PW n (mulF n Y Y) (e / 2))) (mulF n (mulF n R Y) (PW n Y (2 * (e / 2)))) :=
      mulF_congr n _ _ _ _ (EqOn_refl n _) hsq
    have h2 : mulF n (mulF n R Y) (PW n Y (2 * (e / 2))) = mulF n R (mulF n Y (PW n Y (2 * (e / 2)))) :=
      mulF_assoc n _ _ _
    have h3 : EqOn n (mulF n Y (PW n Y (2 * (e / 2)))) (PW n Y e) := by
      have := PW_add n Y 1 (2 * (e / 2))
      rw [← he] at this
      have h1' : EqOn n (PW n Y 1) Y := by
        show EqOn n (mulF n Idm Y) Y
        exact mulF_one_left n Y
      exact EqOn_trans (mulF_congr n _ _ _ _ (EqOn_symm h1') (EqOn_refl n _)) (EqOn_symm this)
    rw [h2] at h1
    exact EqOn_trans h1 (mulF_congr n _ _ _ _ (EqOn_refl n R) h3)
  · rename_i h
    have he : 2 * (e / 2) = e := by omega
    rw [he] at hsq
    exact mulF_congr n _ _ _ _ (EqOn_refl n R) hsq

end Proofs.Cpp.SquareMatrixMath
