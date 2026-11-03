namespace Proofs.MatPowMath

abbrev M64 : Nat := 18446744073709551616

/-- `Σ_{t<n} f t`. -/
def Sum (n : Nat) (f : Nat → Nat) : Nat := (List.range n).foldl (fun s t => s + f t) 0

theorem Sum_zero (f : Nat → Nat) : Sum 0 f = 0 := rfl

theorem foldl_add_init (l : List Nat) (f : Nat → Nat) (s : Nat) :
    l.foldl (fun s t => s + f t) s = s + l.foldl (fun s t => s + f t) 0 := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih (s + f x), ih (0 + f x)]; omega

theorem Sum_succ (n : Nat) (f : Nat → Nat) : Sum (n + 1) f = Sum n f + f n := by
  unfold Sum
  rw [List.range_succ, List.foldl_append]
  simp

theorem Sum_congr (n : Nat) (f g : Nat → Nat) (h : ∀ t, t < n → f t = g t) : Sum n f = Sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Sum_succ, Sum_succ, ih (fun t ht => h t (by omega)), h n (by omega)]

theorem Sum_add (n : Nat) (f g : Nat → Nat) : Sum n (fun t => f t + g t) = Sum n f + Sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Sum_succ, Sum_succ, Sum_succ, ih]; omega

theorem Sum_mul_left (n : Nat) (x : Nat) (f : Nat → Nat) : Sum n (fun t => x * f t) = x * Sum n f := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih => rw [Sum_succ, Sum_succ, ih, Nat.mul_add]

theorem Sum_mul_right (n : Nat) (x : Nat) (f : Nat → Nat) : Sum n (fun t => f t * x) = Sum n f * x := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih => rw [Sum_succ, Sum_succ, ih, Nat.add_mul]

theorem Sum_swap (n m : Nat) (g : Nat → Nat → Nat) :
    Sum n (fun t => Sum m (fun k => g t k)) = Sum m (fun k => Sum n (fun t => g t k)) := by
  induction n with
  | zero => simp [Sum_zero]; induction m with
    | zero => rfl
    | succ m ih => rw [Sum_succ]; simpa [Sum_zero] using ih
  | succ n ih => rw [Sum_succ, ih, ← Sum_add]; apply Sum_congr; intro k _; rw [Sum_succ]

theorem Sum_mod (n : Nat) (f : Nat → Nat) : Sum n f % M64 = Sum n (fun t => f t % M64) % M64 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Sum_succ, Sum_succ]
    have h1 : (Sum n f + f n) % M64 = (Sum n f % M64 + f n % M64) % M64 := Nat.add_mod _ _ _
    have h2 : ((Sum n fun t => f t % M64) + f n % M64) % M64 =
        ((Sum n fun t => f t % M64) % M64 + f n % M64 % M64) % M64 := Nat.add_mod _ _ _
    rw [h1, h2, ih, Nat.mod_mod]

/-- The matrix product modulo `2^64` (entries are indexed by `i, j < n`). -/
def mulF (n : Nat) (A B : Nat → Nat → Nat) : Nat → Nat → Nat := fun i j => Sum n (fun t => A i t * B t j) % M64

def Idm : Nat → Nat → Nat := fun i j => if i = j then 1 else 0

def EqOn (n : Nat) (A B : Nat → Nat → Nat) : Prop := ∀ i j, i < n → j < n → A i j = B i j

def Bd (n : Nat) (A : Nat → Nat → Nat) : Prop := ∀ i j, i < n → j < n → A i j < M64

theorem mulF_congr (n : Nat) (A A' B B' : Nat → Nat → Nat) (hA : EqOn n A A') (hB : EqOn n B B') :
    EqOn n (mulF n A B) (mulF n A' B') := by
  intro i j hi hj
  unfold mulF
  rw [Sum_congr n (fun t => A i t * B t j) (fun t => A' i t * B' t j)]
  intro t ht
  rw [hA i t hi ht, hB t j ht hj]

theorem mulF_bd (n : Nat) (A B : Nat → Nat → Nat) : Bd n (mulF n A B) := by
  intro i j _ _
  exact Nat.mod_lt _ (by decide)

theorem Sum_mul_mod (n : Nat) (g c : Nat → Nat) :
    Sum n (fun t => (g t % M64) * c t) % M64 = Sum n (fun t => g t * c t) % M64 := by
  rw [Sum_mod n (fun t => (g t % M64) * c t), Sum_mod n (fun t => g t * c t)]
  congr 1
  apply Sum_congr
  intro t _
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem Sum_mul_mod2 (n : Nat) (g c : Nat → Nat) :
    Sum n (fun t => c t * (g t % M64)) % M64 = Sum n (fun t => c t * g t) % M64 := by
  rw [Sum_mod n (fun t => c t * (g t % M64)), Sum_mod n (fun t => c t * g t)]
  congr 1
  apply Sum_congr
  intro t _
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mulF_assoc (n : Nat) (A B C : Nat → Nat → Nat) : mulF n (mulF n A B) C = mulF n A (mulF n B C) := by
  funext i j
  unfold mulF
  rw [Sum_mul_mod n (fun t => Sum n (fun k => A i k * B k t)) (fun t => C t j)]
  rw [Sum_mul_mod2 n (fun k => Sum n (fun t => B k t * C t j)) (fun k => A i k)]
  congr 1
  have e1 : Sum n (fun t => Sum n (fun k => A i k * B k t) * C t j) =
      Sum n (fun t => Sum n (fun k => A i k * B k t * C t j)) := by
    apply Sum_congr; intro t _; rw [Sum_mul_right]
  have e2 : Sum n (fun k => A i k * Sum n (fun t => B k t * C t j)) =
      Sum n (fun k => Sum n (fun t => A i k * (B k t * C t j))) := by
    apply Sum_congr; intro k _; rw [Sum_mul_left]
  rw [e1, e2, Sum_swap]
  apply Sum_congr; intro k _
  apply Sum_congr; intro t _
  rw [Nat.mul_assoc]

theorem Sum_ite_left (n i : Nat) (f : Nat → Nat) :
    Sum n (fun t => (if i = t then 1 else 0) * f t) = if i < n then f i else 0 := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih =>
    rw [Sum_succ, ih]
    by_cases h : i < n
    · have : i ≠ n := by omega
      simp [h, this]; omega
    · by_cases h2 : i = n
      · subst h2; simp
      · have : ¬ i < n + 1 := by omega
        simp [h, h2, this]

theorem Sum_ite_right (n j : Nat) (f : Nat → Nat) :
    Sum n (fun t => f t * (if t = j then 1 else 0)) = if j < n then f j else 0 := by
  induction n with
  | zero => simp [Sum_zero]
  | succ n ih =>
    rw [Sum_succ, ih]
    by_cases h : j < n
    · have : n ≠ j := by omega
      simp [h, this]; omega
    · by_cases h2 : j = n
      · subst h2; simp
      · have : ¬ j < n + 1 := by omega
        have h3 : n ≠ j := by omega
        simp [h, h2, this, h3]

theorem mulF_one_left (n : Nat) (X : Nat → Nat → Nat) (hX : Bd n X) : EqOn n (mulF n Idm X) X := by
  intro i j hi hj
  unfold mulF Idm
  rw [Sum_ite_left n i (fun t => X t j), if_pos hi]
  exact Nat.mod_eq_of_lt (hX i j hi hj)

theorem mulF_one_right (n : Nat) (X : Nat → Nat → Nat) (hX : Bd n X) : EqOn n (mulF n X Idm) X := by
  intro i j hi hj
  unfold mulF Idm
  rw [Sum_ite_right n j (fun t => X i t), if_pos hj]
  exact Nat.mod_eq_of_lt (hX i j hi hj)

/-- `A^k` by left multiplication. -/
def PW (n : Nat) (A : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0 => Idm
  | k + 1 => mulF n (PW n A k) A

theorem PW_bd (n : Nat) (A : Nat → Nat → Nat) : ∀ k, Bd n (PW n A k) := by
  intro k
  cases k with
  | zero =>
    intro i j _ _
    show (if i = j then 1 else 0) < M64
    split <;> decide
  | succ k => exact mulF_bd n _ _

theorem PW_add (n : Nat) (A : Nat → Nat → Nat) (i : Nat) : ∀ j, EqOn n (PW n A (i + j)) (mulF n (PW n A i) (PW n A j)) := by
  intro j
  induction j with
  | zero =>
    intro a b ha hb
    exact ((mulF_one_right n _ (PW_bd n A i)) a b ha hb).symm
  | succ j ih =>
    have h1 : EqOn n (mulF n (PW n A (i + j)) A) (mulF n (mulF n (PW n A i) (PW n A j)) A) :=
      mulF_congr n _ _ _ _ ih (fun _ _ _ _ => rfl)
    have h2 : mulF n (mulF n (PW n A i) (PW n A j)) A = mulF n (PW n A i) (PW n A (j + 1)) := by
      rw [mulF_assoc]; rfl
    intro a b ha hb
    have := h1 a b ha hb
    rw [h2] at this
    exact this

end Proofs.MatPowMath

