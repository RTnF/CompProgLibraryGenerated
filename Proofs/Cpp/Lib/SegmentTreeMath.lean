import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Proofs.Math.FenwickMath

/-! # The mathematics of the iterative segment tree over an arbitrary monoid

`Mon M` is a monoid on the representable values `V` of a type `M` (closed under `op`, containing `e`, the laws hold
on `V`). A node array is read through a function `a : Nat → M` (`a i = node[i]!`). The tree with `N` leaves has the
leaves at `a N, ..., a (2N - 1)` and every inner node `1 ≤ i < N` holds `op (a (2i)) (a (2i+1))` (`TInv`).
`rf a i k` is the product `a i * ... * a (i + k - 1)`. -/

namespace Proofs.Cpp.SegmentTreeMath

/-- A monoid on the values `V` of `M`. -/
structure Mon (M : Type) where
  V : M → Prop
  op : M → M → M
  e : M
  closed : ∀ a b, V a → V b → V (op a b)
  he : V e
  assoc : ∀ a b c, V a → V b → V c → op (op a b) c = op a (op b c)
  lid : ∀ a, V a → op e a = a
  rid : ∀ a, V a → op a e = a

variable {M : Type} (m : Mon M)

/-- `rf a i k`: the product of `a i, ..., a (i + k - 1)` from left to right. -/
def rf (a : Nat → M) : Nat → Nat → M
  | _, 0 => m.e
  | i, k + 1 => m.op (a i) (rf a (i + 1) k)

/-- The entries `a 0, ..., a (L - 1)` are representable. -/
def AllV (a : Nat → M) (L : Nat) : Prop := ∀ i, i < L → m.V (a i)

theorem rf_V (a : Nat → M) (L : Nat) (h : AllV m a L) : ∀ (k i : Nat), i + k ≤ L → m.V (rf m a i k) := by
  intro k
  induction k with
  | zero => intro i _; exact m.he
  | succ k ih => intro i hi; exact m.closed _ _ (h i (by omega)) (ih (i + 1) (by omega))

theorem rf_one (a : Nat → M) (i : Nat) (h : m.V (a i)) : rf m a i 1 = a i := by
  show m.op (a i) m.e = a i
  exact m.rid _ h

theorem rf_add (a : Nat → M) (L : Nat) (h : AllV m a L) :
    ∀ (k1 k2 i : Nat), i + k1 + k2 ≤ L → rf m a i (k1 + k2) = m.op (rf m a i k1) (rf m a (i + k1) k2) := by
  intro k1
  induction k1 with
  | zero =>
    intro k2 i hi
    simp only [Nat.zero_add, Nat.add_zero, rf]
    rw [m.lid _ (rf_V m a L h k2 i (by omega))]
  | succ k ih =>
    intro k2 i hi
    have e : k + 1 + k2 = (k + k2) + 1 := by omega
    rw [e, rf, ih k2 (i + 1) (by omega), rf]
    have e2 : i + 1 + k = i + (k + 1) := by omega
    rw [e2, m.assoc _ _ _ (h i (by omega)) (rf_V m a L h k (i + 1) (by omega))
      (rf_V m a L h k2 (i + (k + 1)) (by omega))]

/-- The products only read the entries they cover. -/
theorem rf_congr (a b : Nat → M) : ∀ (k i : Nat), (∀ j, i ≤ j → j < i + k → a j = b j) → rf m a i k = rf m b i k := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro i h
    simp only [rf]
    rw [h i (by omega) (by omega), ih (i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

/-- The tree layout with `N` leaves. -/
def TInv (a : Nat → M) (N : Nat) : Prop :=
  ∀ i, 1 ≤ i → i < N → a i = m.op (a (2 * i)) (a (2 * i + 1))

theorem rf_pairs (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (h : TInv m a N) :
    ∀ (k i : Nat), 1 ≤ i → i + k ≤ N → rf m a (2 * i) (2 * k) = rf m a i k := by
  intro k
  induction k with
  | zero => intro i _ _; simp [rf]
  | succ k ih =>
    intro i hi hk
    have e2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [e2, rf, rf]
    have e3 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [e3, ih (i + 1) (by omega) (by omega), rf]
    have v0 := hV (2 * i) (by omega)
    have v1 := hV (2 * i + 1) (by omega)
    have vr := rf_V m a (2 * N) hV k (i + 1) (by omega)
    rw [← m.assoc _ _ _ v0 v1 vr, ← h i hi (by omega)]

theorem re_eo (a x y r : M) (va : m.V a) (vx : m.V x) (vy : m.V y) (vr : m.V r) :
    m.op (m.op a (m.op x y)) r = m.op (m.op a x) (m.op y r) := by
  rw [← m.assoc _ _ _ va vx vy, m.assoc _ _ _ (m.closed _ _ va vx) vy vr]

theorem re_oe (a y x r : M) (va : m.V a) (vy : m.V y) (vx : m.V x) :
    m.op (m.op a (m.op y x)) r = m.op (m.op (m.op a y) x) r := by
  rw [← m.assoc _ _ _ va vy vx]

theorem re_oo (a y x z r : M) (va : m.V a) (vy : m.V y) (vx : m.V x) (vz : m.V z) (vr : m.V r) :
    m.op (m.op a (m.op y (m.op x z))) r = m.op (m.op (m.op a y) x) (m.op z r) := by
  rw [← m.assoc _ _ _ vy vx vz, ← m.assoc _ _ _ va (m.closed _ _ vy vx) vz, ← m.assoc _ _ _ va vy vx,
    m.assoc _ _ _ (m.closed _ _ (m.closed _ _ va vy) vx) vz vr]

/-! ## The product loop -/

def pl1 (l : Nat) : Nat := if l % 2 = 1 then l + 1 else l
def pr1 (r : Nat) : Nat := if r % 2 = 1 then r - 1 else r
def pleft (a : Nat → M) (l : Nat) (left : M) : M := if l % 2 = 1 then m.op left (a l) else left
def pright (a : Nat → M) (r : Nat) (right : M) : M := if r % 2 = 1 then m.op (a (r - 1)) right else right

/-- The invariant of the product loop: the answer `T` is `left * (nodes [l, r)) * right`. -/
def PInv (a : Nat → M) (N : Nat) (T : M) (l r : Nat) (left right : M) : Prop :=
  1 ≤ l ∧ l ≤ r ∧ r ≤ 2 * N ∧ m.V left ∧ m.V right ∧ m.op (m.op left (rf m a l (r - l))) right = T

theorem prod_step (a : Nat → M) (N : Nat) (T : M) (hV : AllV m a (2 * N)) (h : TInv m a N) (l r : Nat)
    (left right : M) (hI : PInv m a N T l r left right) (hlr : l < r) :
    PInv m a N T (pl1 l / 2) (pr1 r / 2) (pleft m a l left) (pright m a r right) := by
  obtain ⟨h1, h1', h2, h3, h4, h5⟩ := hI
  have hl1 : 2 ≤ pl1 l := by unfold pl1; split <;> omega
  have hl1e : pl1 l % 2 = 0 := by unfold pl1; split <;> omega
  have hr1e : pr1 r % 2 = 0 := by unfold pr1; split <;> omega
  have hlr1 : pl1 l ≤ pr1 r := by unfold pl1 pr1; split <;> split <;> omega
  have hr1le : pr1 r ≤ r := by unfold pr1; split <;> omega
  have hl1ge : l ≤ pl1 l := by unfold pl1; split <;> omega
  have hVl := hV l (by omega)
  have hVr := hV (r - 1) (by omega)
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · unfold pleft; split
    · exact m.closed _ _ h3 hVl
    · exact h3
  · unfold pright; split
    · exact m.closed _ _ hVr h4
    · exact h4
  · have hpair := rf_pairs m a N hV h ((pr1 r - pl1 l) / 2) (pl1 l / 2) (by omega) (by omega)
    have e1 : 2 * (pl1 l / 2) = pl1 l := by omega
    have e2 : 2 * ((pr1 r - pl1 l) / 2) = pr1 r - pl1 l := by omega
    rw [e1, e2] at hpair
    have e3 : pr1 r / 2 - pl1 l / 2 = (pr1 r - pl1 l) / 2 := by omega
    rw [e3, ← hpair]
    have e5 : rf m a (r - 1) 1 = a (r - 1) := rf_one m a (r - 1) hVr
    rcases Nat.mod_two_eq_zero_or_one l with hl | hl <;> rcases Nat.mod_two_eq_zero_or_one r with hr | hr
    · have hp1 : pl1 l = l := by simp [pl1, hl]
      have hp2 : pr1 r = r := by simp [pr1, hr]
      simp only [pleft, pright, hl, hr, hp1, hp2] at *
      simpa using h5
    · have hp1 : pl1 l = l := by simp [pl1, hl]
      have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
      have e : r - l = (r - 1 - l) + 1 := by omega
      rw [e, rf_add m a (2 * N) hV (r - 1 - l) 1 l (by omega)] at h5
      have e4 : l + (r - 1 - l) = r - 1 := by omega
      rw [e4, e5] at h5
      have vX' := rf_V m a (2 * N) hV (r - 1 - l) l (by omega)
      have hl' : ¬ (l % 2 = 1) := by omega
      simp only [pleft, pright, hl', hr, hp1, hp2, ite_true, ite_false]
      rw [← h5]
      exact (re_eo m left _ _ right h3 vX' hVr h4).symm
    · have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
      have hp2 : pr1 r = r := by simp [pr1, hr]
      have e : r - l = (r - (l + 1)) + 1 := by omega
      rw [e, rf] at h5
      have vX' := rf_V m a (2 * N) hV (r - (l + 1)) (l + 1) (by omega)
      have hr' : ¬ (r % 2 = 1) := by omega
      simp only [pleft, pright, hl, hr', hp1, hp2, ite_true, ite_false]
      rw [← h5]
      exact (re_oe m left _ _ right h3 hVl vX').symm
    · have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
      have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
      have e : r - l = ((r - 1 - (l + 1)) + 1) + 1 := by omega
      rw [e, rf, rf_add m a (2 * N) hV (r - 1 - (l + 1)) 1 (l + 1) (by omega)] at h5
      have e4 : l + 1 + (r - 1 - (l + 1)) = r - 1 := by omega
      rw [e4, e5] at h5
      have vX' := rf_V m a (2 * N) hV (r - 1 - (l + 1)) (l + 1) (by omega)
      simp only [pleft, pright, hl, hr, hp1, hp2, ite_true, ite_false]
      rw [← h5]
      exact (re_oo m left _ _ _ right h3 hVl vX' hVr h4).symm

theorem PInv_exit (a : Nat → M) (N : Nat) (T : M) (l r : Nat) (left right : M) (h : PInv m a N T l r left right)
    (hlr : ¬ l < r) : m.op left right = T := by
  obtain ⟨_, h1', _, h3, _, h5⟩ := h
  have : r - l = 0 := by omega
  rw [this] at h5
  simp only [rf] at h5
  rw [m.rid _ h3] at h5
  exact h5

/-! ## Updates (the path from a leaf to the root) and the build loop -/

/-- `j` lies on the path from `i` to the root. -/
def Anc (i j : Nat) : Prop := ∃ t, j = i / 2 ^ t

theorem anc_step (i j : Nat) : Anc i j ↔ j = i ∨ Anc (i / 2) j := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => left; simpa using ht
    | succ s =>
      right
      refine ⟨s, ?_⟩
      rw [ht, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · rintro (h | ⟨s, hs⟩)
    · exact ⟨0, by simpa using h⟩
    · refine ⟨s + 1, ?_⟩
      rw [hs, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Every inner node off the path from `i` to the root holds the product of its children. -/
def SInv (a : Nat → M) (N i : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < N → ¬ Anc i j → a j = m.op (a (2 * j)) (a (2 * j + 1))

/-- The function view of an update at `i`. -/
def upd (a : Nat → M) (i : Nat) (x : M) : Nat → M := fun j => if j = i then x else a j

theorem sinv_step (a : Nat → M) (N i : Nat) (h : SInv m a N i) (hi1 : 1 ≤ i) :
    SInv m (upd a i (m.op (a (2 * i)) (a (2 * i + 1)))) N (i / 2) := by
  intro j hj1 hjN hna
  by_cases hji : j = i
  · subst hji
    simp only [upd, if_neg (show ¬ (2 * j = j) by omega), if_neg (show ¬ (2 * j + 1 = j) by omega), if_true]
  · have hna' : ¬ Anc i j := by
      intro ha
      rcases (anc_step i j).mp ha with e | e
      · exact hji e
      · exact hna e
    have c1 : ¬ (2 * j = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    have c2 : ¬ (2 * j + 1 = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    simp only [upd, if_neg hji, if_neg c1, if_neg c2]
    exact h j hj1 hjN hna'

theorem sinv_zero (a : Nat → M) (N : Nat) (h : SInv m a N 0) : TInv m a N := by
  intro j hj1 hjN
  apply h j hj1 hjN
  rintro ⟨t, ht⟩
  simp at ht
  omega

theorem sinv_init (a : Nat → M) (N p : Nat) (x : M) (hT : TInv m a N) (hp1 : N ≤ p) :
    SInv m (upd a p x) N (p / 2) := by
  intro j hj1 hjN hna
  have c0 : ¬ (j = p) := by omega
  have c1 : ¬ (2 * j = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  have c2 : ¬ (2 * j + 1 = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  simp only [upd, if_neg c0, if_neg c1, if_neg c2]
  exact hT j hj1 hjN

/-- The nodes `j > i` already hold the product of their children (the build loop goes from `N - 1` down to `1`). -/
def BInv (a : Nat → M) (N i : Nat) : Prop :=
  ∀ j, i < j → j < N → a j = m.op (a (2 * j)) (a (2 * j + 1))

theorem binv_init (a : Nat → M) (N : Nat) : BInv m a N (N - 1) := by
  intro j h1 h2; omega

theorem binv_step (a : Nat → M) (N i : Nat) (h : BInv m a N i) (hi1 : 1 ≤ i) :
    BInv m (upd a i (m.op (a (2 * i)) (a (2 * i + 1)))) N (i - 1) := by
  intro j hj1 hjN
  by_cases hji : j = i
  · subst hji
    simp only [upd, if_neg (show ¬ (2 * j = j) by omega), if_neg (show ¬ (2 * j + 1 = j) by omega), if_true]
  · have hj : i < j := by omega
    simp only [upd, if_neg hji, if_neg (show ¬ (2 * j = i) by omega), if_neg (show ¬ (2 * j + 1 = i) by omega)]
    exact h j hj hjN

theorem binv_end (a : Nat → M) (N : Nat) (h : BInv m a N 0) : TInv m a N := by
  intro j hj1 hjN
  exact h j (by omega) hjN

/-! ## Nodes, leaves and padding -/

theorem node_rf (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) :
    ∀ t x, 1 ≤ x → (x + 1) * 2 ^ t ≤ 2 * N → rf m a (x * 2 ^ t) (2 ^ t) = a x := by
  intro t
  induction t with
  | zero => intro x hx h; simp only [pow_zero, Nat.mul_one]; exact rf_one m a x (hV x (by omega))
  | succ t ih =>
    intro x hx h
    have hp : 0 < 2 ^ t := Nat.two_pow_pos _
    have h2 : (x + 1) * 2 ^ t ≤ N := by rw [pow_succ] at h; nlinarith
    have e1 : x * 2 ^ (t + 1) = 2 * (x * 2 ^ t) := by rw [pow_succ]; ring
    have e2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
    have hx1 : 1 ≤ x * 2 ^ t := Nat.mul_pos (by omega) (Nat.two_pow_pos t)
    rw [e1, e2, rf_pairs m a N hV hT (2 ^ t) (x * 2 ^ t) hx1 (by nlinarith)]
    exact ih x hx (by nlinarith)

theorem rf_shift (a : Nat → M) (N : Nat) : ∀ k i, rf m a (N + i) k = rf m (fun j => a (N + j)) i k := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    simp only [rf]
    rw [show N + i + 1 = N + (i + 1) by omega, ih (i + 1)]

theorem rf_e (a : Nat → M) : ∀ k i, (∀ j, i ≤ j → j < i + k → a j = m.e) → rf m a i k = m.e := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i h
    simp only [rf]
    rw [h i (by omega) (by omega), ih (i + 1) (fun j h1 h2 => h j (by omega) (by omega)), m.lid _ m.he]

/-- The leaves after the `n` values hold `e`: a product to the end of the leaves stops at `n`. -/
theorem rf_pad (a : Nat → M) (N n S : Nat) (hV : AllV m a (2 * N)) (hn : n ≤ N) (hS : N ≤ S) (hSn : S ≤ N + n)
    (hpad : ∀ j, n ≤ j → j < N → a (N + j) = m.e) : rf m a S (2 * N - S) = rf m a S (N + n - S) := by
  have e : 2 * N - S = (N + n - S) + (N - n) := by omega
  rw [e, rf_add m a (2 * N) hV _ _ _ (by omega)]
  rw [rf_e m a (N - n) (S + (N + n - S)) (fun j h1 h2 => by
    have := hpad (j - N) (by omega) (by omega); rwa [show N + (j - N) = j by omega] at this)]
  exact m.rid _ (rf_V m a (2 * N) hV _ _ (by omega))

/-! ## Powers of two -/

/-- `lowb x = x` exactly for the powers of two. -/
theorem lowb_eq_self_iff (x : Nat) (hx : 0 < x) : Proofs.FenwickMath.lowb x = x ↔ ∃ k, x = 2 ^ k := by
  constructor
  · intro h
    obtain ⟨s, c, h1, h2⟩ := Proofs.FenwickMath.lowb_form x hx
    refine ⟨s, ?_⟩
    have : 2 ^ s * (2 * c + 1) = 2 ^ s * 1 := by rw [← h2, Nat.mul_one, ← h1, h]
    have hp : 0 < 2 ^ s := Nat.two_pow_pos _
    have := Nat.eq_of_mul_eq_mul_left hp this
    rw [h2, show 2 * c + 1 = 1 by omega, Nat.mul_one]
  · rintro ⟨k, rfl⟩
    have h1 := Proofs.FenwickMath.lowb_max (2 ^ k) k hx (dvd_refl _)
    have h2 := Proofs.FenwickMath.lowb_le (2 ^ k) hx
    omega

theorem t_le (N h l t : Nat) (hN : N = 2 ^ h) (hl : 1 ≤ l) (h2 : (l + 1) * 2 ^ t ≤ 2 * N) : t ≤ h := by
  have : 2 * 2 ^ t ≤ 2 * 2 ^ h := by rw [← hN]; nlinarith
  exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)

/-- Within the `2N = 2^(h+1)` leaves, the blocks of `2^t` leaves tile the range: a block that does not reach the end
ends at least one block before it. -/
theorem block_next (N h y t : Nat) (hN : N = 2 ^ h) (ht : t ≤ h + 1) (hy : y * 2 ^ t ≤ 2 * N)
    (hne : y * 2 ^ t ≠ 2 * N) : (y + 1) * 2 ^ t ≤ 2 * N := by
  have e : 2 * N = 2 ^ t * 2 ^ (h + 1 - t) := by
    rw [← pow_add, show t + (h + 1 - t) = h + 1 by omega, pow_succ, hN]; ring
  rw [e] at hy hne ⊢
  have hp : 0 < 2 ^ t := Nat.two_pow_pos _
  have : y ≤ 2 ^ (h + 1 - t) := by
    rw [Nat.mul_comm] at hy; exact Nat.le_of_mul_le_mul_left hy hp
  have : y ≠ 2 ^ (h + 1 - t) := by intro he; apply hne; rw [he, Nat.mul_comm]
  have : y + 1 ≤ 2 ^ (h + 1 - t) := by omega
  nlinarith

theorem block_pow_end (N h k t : Nat) (hN : N = 2 ^ h) (hlo : N < 2 ^ k * 2 ^ t) (hhi : 2 ^ k * 2 ^ t ≤ 2 * N) :
    2 ^ k * 2 ^ t = 2 * N := by
  rw [← pow_add] at hlo hhi ⊢
  rw [hN] at hlo hhi ⊢
  have h1 : h < k + t := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hlo
  have h2 : k + t ≤ h + 1 := (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by rw [pow_succ]; omega)
  rw [show k + t = h + 1 by omega, pow_succ]; ring

/-! ## Binary search to the right (`search_prod_right`)

The search starts at the leaf `S = N + l0`. At the head of the outer loop the node `l` has height `t`: it covers the
leaves `[l 2^t, (l+1) 2^t)`, and `sm` is the product of the leaves `[S, l 2^t)` (`RInv`). -/

def RInv (a : Nat → M) (N : Nat) (f : M → Bool) (S l : Nat) (sm : M) (t : Nat) : Prop :=
  1 ≤ l ∧ N ≤ l * 2 ^ t ∧ (l + 1) * 2 ^ t ≤ 2 * N ∧ S ≤ l * 2 ^ t ∧ m.V sm ∧
    sm = rf m a S (l * 2 ^ t - S) ∧ f sm = true

theorem rinv_init (a : Nat → M) (N : Nat) (f : M → Bool) (S : Nat) (hS1 : N ≤ S) (hS2 : S < 2 * N)
    (hf : f m.e = true) : RInv m a N f S S m.e 0 := by
  refine ⟨by omega, by simpa using hS1, by simp; omega, by simp, m.he, by simp [rf], hf⟩

/-- Climbing to the parent while `l` is a left child keeps the covered leaves' start. -/
theorem rinv_climb (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (f : M → Bool) (S l : Nat) (sm : M) (t : Nat)
    (hI : RInv m a N f S l sm t) (he : l % 2 = 0) : RInv m a N f S (l / 2) sm (t + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have ht := t_le N h l t hN h1 h3
  have eL : l / 2 * 2 ^ (t + 1) = l * 2 ^ t := by
    rw [pow_succ]; have : l = 2 * (l / 2) := by omega
    conv_rhs => rw [this]
    ring
  have hnext := block_next N h (l + 1) t hN (by omega) h3 (by
    intro heq
    have : (l + 1) * 2 ^ t = 2 ^ t * 2 ^ (h + 1 - t) := by
      rw [heq, ← pow_add, show t + (h + 1 - t) = h + 1 by omega, pow_succ, hN]; ring
    have hp : 0 < 2 ^ t := Nat.two_pow_pos _
    rw [Nat.mul_comm] at this
    have := Nat.eq_of_mul_eq_mul_left hp this
    have h0 : h + 1 - t ≠ 0 := by
      intro h0; rw [h0] at this; simp at this; omega
    have : (l + 1) % 2 = 0 := by
      rw [this, show h + 1 - t = (h - t) + 1 by omega, pow_succ]; simp
    omega)
  refine ⟨by omega, by rw [eL]; exact h2, ?_, by rw [eL]; exact h4, h5, by rw [eL]; exact h6, h7⟩
  have : (l / 2 + 1) * 2 ^ (t + 1) = (l + 1 + 1) * 2 ^ t := by
    rw [pow_succ]; have : l = 2 * (l / 2) := by omega
    conv_rhs => rw [this]
    ring
  rw [this]; exact hnext

/-- The node `l` passes (`f` still holds with it): move to the next node of the same height. -/
theorem rinv_pass (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) (f : M → Bool) (S l : Nat)
    (sm : M) (t : Nat) (hI : RInv m a N f S l sm t) (hf : f (m.op sm (a l)) = true) :
    m.V (m.op sm (a l)) ∧ m.op sm (a l) = rf m a S ((l + 1) * 2 ^ t - S) ∧ S ≤ (l + 1) * 2 ^ t ∧
      N < (l + 1) * 2 ^ t ∧ (l + 1) * 2 ^ t ≤ 2 * N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hp : 0 < 2 ^ t := Nat.two_pow_pos _
  have hl : l < 2 * N := by nlinarith
  refine ⟨m.closed _ _ h5 (hV l hl), ?_, by nlinarith, by nlinarith, h3⟩
  rw [h6, ← node_rf m a N hV hT t l h1 h3]
  have e : (l + 1) * 2 ^ t - S = (l * 2 ^ t - S) + 2 ^ t := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e, rf_add m a (2 * N) hV _ _ _ (by rw [Nat.add_mul, Nat.one_mul] at h3; omega),
    show S + (l * 2 ^ t - S) = l * 2 ^ t by omega]

theorem rinv_op (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) (f : M → Bool) (S l : Nat)
    (sm : M) (t : Nat) (hI : RInv m a N f S l sm t) :
    m.op sm (a l) = rf m a S ((l + 1) * 2 ^ t - S) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hp : 0 < 2 ^ t := Nat.two_pow_pos _
  have hl : l < 2 * N := by nlinarith
  rw [h6, ← node_rf m a N hV hT t l h1 h3]
  have e : (l + 1) * 2 ^ t - S = (l * 2 ^ t - S) + 2 ^ t := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e, rf_add m a (2 * N) hV _ _ _ (by rw [Nat.add_mul, Nat.one_mul] at h3; omega),
    show S + (l * 2 ^ t - S) = l * 2 ^ t by omega]

theorem rinv_next (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (hV : AllV m a (2 * N)) (hT : TInv m a N)
    (f : M → Bool) (S l : Nat) (sm : M) (t : Nat) (hI : RInv m a N f S l sm t) (hf : f (m.op sm (a l)) = true)
    (hpow : ¬ ∃ k, l + 1 = 2 ^ k) : RInv m a N f S (l + 1) (m.op sm (a l)) t := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  obtain ⟨v1, v2, v3, v4, v5⟩ := rinv_pass m a N hV hT f S l sm t hI' hf
  have ht := t_le N h l t hN h1 h3
  refine ⟨by omega, by omega, ?_, v3, v1, v2, hf⟩
  apply block_next N h (l + 1) t hN (by omega) v5
  intro heq
  apply hpow
  have e : 2 * N = 2 ^ t * 2 ^ (h + 1 - t) := by
    rw [← pow_add, show t + (h + 1 - t) = h + 1 by omega, pow_succ, hN]; ring
  rw [e, Nat.mul_comm] at heq
  exact ⟨h + 1 - t, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos t) heq⟩

theorem rinv_end (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (hV : AllV m a (2 * N)) (hT : TInv m a N)
    (f : M → Bool) (S l : Nat) (sm : M) (t : Nat) (hI : RInv m a N f S l sm t) (hf : f (m.op sm (a l)) = true)
    (hpow : ∃ k, l + 1 = 2 ^ k) : m.op sm (a l) = rf m a S (2 * N - S) ∧ f (rf m a S (2 * N - S)) = true := by
  have hI' := hI
  obtain ⟨v1, v2, v3, v4, v5⟩ := rinv_pass m a N hV hT f S l sm t hI' hf
  obtain ⟨k, hk⟩ := hpow
  have hend : (l + 1) * 2 ^ t = 2 * N := by
    rw [hk] at v4 v5 ⊢; exact block_pow_end N h k t hN v4 v5
  rw [hend] at v2
  exact ⟨v2, v2 ▸ hf⟩

/-- The descent below a node where `f` fails: `f` fails with the node (`DInv`). -/
def DInv (a : Nat → M) (N : Nat) (f : M → Bool) (S l : Nat) (sm : M) (t : Nat) : Prop :=
  RInv m a N f S l sm t ∧ f (m.op sm (a l)) = false

theorem dinv_step (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) (f : M → Bool) (S l : Nat)
    (sm : M) (t : Nat) (hI : DInv m a N f S l sm t) (hl : l < N) :
    ∃ t', t = t' + 1 ∧
      (f (m.op sm (a (2 * l))) = true → DInv m a N f S (2 * l + 1) (m.op sm (a (2 * l))) t') ∧
      (f (m.op sm (a (2 * l))) = false → DInv m a N f S (2 * l) sm t') := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hI
  have ht : t ≠ 0 := by intro h0; rw [h0] at h2; simp at h2; omega
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hp : 0 < 2 ^ t' := by positivity
  have eL : l * 2 ^ (t' + 1) = 2 * l * 2 ^ t' := by rw [pow_succ]; ring
  have eR : (l + 1) * 2 ^ (t' + 1) = (2 * l + 1 + 1) * 2 ^ t' := by rw [pow_succ]; ring
  have hnode := hT l h1 hl
  have v0 := hV (2 * l) (by omega)
  have v1 := hV (2 * l + 1) (by omega)
  refine ⟨t', rfl, ?_, ?_⟩
  · intro hf
    have hc := node_rf m a N hV hT t' (2 * l) (by omega) (by rw [eR] at h3; nlinarith)
    refine ⟨⟨by omega, by nlinarith, by rw [eR] at h3; exact h3, by nlinarith, m.closed _ _ h5 v0, ?_, hf⟩, ?_⟩
    · rw [h6, ← hc]
      have e : (2 * l + 1) * 2 ^ t' - S = (l * 2 ^ (t' + 1) - S) + 2 ^ t' := by
        rw [eL]; rw [eL] at h4; rw [Nat.add_mul, Nat.one_mul]; omega
      have hb : S + (l * 2 ^ (t' + 1) - S) + 2 ^ t' ≤ 2 * N := by
        rw [eL] at h4 ⊢; rw [eR] at h3
        have : S + (2 * l * 2 ^ t' - S) = 2 * l * 2 ^ t' := by omega
        rw [this]; nlinarith
      rw [e, rf_add m a (2 * N) hV _ _ _ hb,
        show S + (l * 2 ^ (t' + 1) - S) = 2 * l * 2 ^ t' by rw [eL] at h4 ⊢; omega]
    · rw [m.assoc _ _ _ h5 v0 v1, ← hnode]; exact h8
  · intro hf
    refine ⟨⟨by omega, by rw [← eL]; exact h2, by rw [eR] at h3; nlinarith, by rw [← eL]; exact h4, h5,
      by rw [← eL]; exact h6, h7⟩, hf⟩

theorem dinv_exit (a : Nat → M) (N : Nat) (f : M → Bool) (S l : Nat) (sm : M) (t : Nat)
    (hI : DInv m a N f S l sm t) (hl : N ≤ l) : t = 0 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hI
  by_contra ht
  have : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

/-! ## Binary search to the left (`search_prod_left`)

The search ends at the leaf boundary `R = N + r0`. The node `x` of height `t` covers `[x 2^t, (x+1) 2^t)` and `sm` is
the product of the leaves `[(x+1) 2^t, R)` (`LInv`). -/

def LInv (a : Nat → M) (N : Nat) (f : M → Bool) (R x : Nat) (sm : M) (t : Nat) : Prop :=
  1 ≤ x ∧ N ≤ x * 2 ^ t ∧ (x + 1) * 2 ^ t ≤ R ∧ R ≤ 2 * N ∧ m.V sm ∧
    sm = rf m a ((x + 1) * 2 ^ t) (R - (x + 1) * 2 ^ t) ∧ f sm = true

theorem linv_init (a : Nat → M) (N : Nat) (f : M → Bool) (R : Nat) (hR1 : N < R) (hR2 : R ≤ 2 * N)
    (hf : f m.e = true) : LInv m a N f R (R - 1) m.e 0 := by
  refine ⟨by omega, by simp; omega, by simp; omega, hR2, m.he, ?_, hf⟩
  simp only [pow_zero, Nat.mul_one, show R - 1 + 1 = R by omega, Nat.sub_self, rf]

/-- Within the leaves `[N, 2N)` the blocks of `2^t` leaves tile the range: a block start after `N` is at least one
block after it. -/
theorem block_prev (N h y t : Nat) (hN : N = 2 ^ h) (ht : t ≤ h) (hy : N ≤ y * 2 ^ t) (hne : y * 2 ^ t ≠ N) :
    N ≤ (y - 1) * 2 ^ t := by
  have e : N = 2 ^ t * 2 ^ (h - t) := by rw [← pow_add, show t + (h - t) = h by omega, hN]
  rw [e] at hy hne ⊢
  have : 2 ^ (h - t) ≤ y := by rw [Nat.mul_comm y] at hy; exact Nat.le_of_mul_le_mul_left hy (Nat.two_pow_pos t)
  have : y ≠ 2 ^ (h - t) := by intro he; apply hne; rw [he, Nat.mul_comm]
  have : 2 ^ (h - t) ≤ y - 1 := by omega
  rw [Nat.mul_comm (y - 1)]; exact Nat.mul_le_mul_left _ this

theorem linv_climb (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (f : M → Bool) (R x : Nat) (sm : M) (t : Nat)
    (hI : LInv m a N f R x sm t) (h1x : 1 < x) (ho : x % 2 = 1) : LInv m a N f R (x / 2) sm (t + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hp : 0 < 2 ^ t := Nat.two_pow_pos t
  have ht := t_le N h x t hN h1 (by omega)
  have eR : (x / 2 + 1) * 2 ^ (t + 1) = (x + 1) * 2 ^ t := by
    rw [pow_succ]; have : x = 2 * (x / 2) + 1 := by omega
    conv_rhs => rw [this]
    ring
  have eL : x / 2 * 2 ^ (t + 1) = (x - 1) * 2 ^ t := by
    rw [pow_succ]; have : x - 1 = 2 * (x / 2) := by omega
    rw [this]; ring
  have ht' : t < h := by
    rcases Nat.lt_or_ge t h with h' | h'
    · exact h'
    · exfalso
      have : t = h := by omega
      subst this
      rw [← hN] at h2 h3
      nlinarith
  have hprev := block_prev N h x t hN (by omega) h2 (by
    intro heq
    have e : N = 2 ^ t * 2 ^ (h - t) := by rw [← pow_add, show t + (h - t) = h by omega, hN]
    rw [e, Nat.mul_comm] at heq
    have := Nat.eq_of_mul_eq_mul_left hp heq
    have : x % 2 = 0 := by rw [this, show h - t = (h - t - 1) + 1 by omega, pow_succ]; simp
    omega)
  refine ⟨by omega, by rw [eL]; exact hprev, by rw [eR]; exact h3, h4, h5, by rw [eR]; exact h6, h7⟩

theorem linv_pass (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) (f : M → Bool) (R x : Nat)
    (sm : M) (t : Nat) (hI : LInv m a N f R x sm t) :
    m.V (m.op (a x) sm) ∧ m.op (a x) sm = rf m a (x * 2 ^ t) (R - x * 2 ^ t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hp : 0 < 2 ^ t := Nat.two_pow_pos t
  have hx : x < 2 * N := by nlinarith
  refine ⟨m.closed _ _ (hV x hx) h5, ?_⟩
  rw [h6, ← node_rf m a N hV hT t x h1 (by omega)]
  have e : R - x * 2 ^ t = 2 ^ t + (R - (x + 1) * 2 ^ t) := by rw [Nat.add_mul, Nat.one_mul] at h3 ⊢; omega
  rw [e, rf_add m a (2 * N) hV _ _ _ (by rw [Nat.add_mul, Nat.one_mul] at h3; omega),
    show x * 2 ^ t + 2 ^ t = (x + 1) * 2 ^ t by ring]

theorem linv_next (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (hV : AllV m a (2 * N)) (hT : TInv m a N)
    (f : M → Bool) (R x : Nat) (sm : M) (t : Nat) (hI : LInv m a N f R x sm t) (hf : f (m.op (a x) sm) = true)
    (hpow : ¬ ∃ k, x = 2 ^ k) : LInv m a N f R (x - 1) (m.op (a x) sm) t := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  obtain ⟨v1, v2⟩ := linv_pass m a N hV hT f R x sm t hI'
  have ht := t_le N h x t hN h1 (by omega)
  have hne : x * 2 ^ t ≠ N := by
    intro heq; apply hpow
    have e : N = 2 ^ t * 2 ^ (h - t) := by rw [← pow_add, show t + (h - t) = h by omega, hN]
    rw [e, Nat.mul_comm] at heq
    exact ⟨h - t, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos t) heq⟩
  have hprev := block_prev N h x t hN ht h2 hne
  have hx2 : 2 ≤ x := by
    rcases Nat.lt_or_ge x 2 with h' | h'
    · exfalso; apply hpow; exact ⟨0, by omega⟩
    · exact h'
  refine ⟨by omega, hprev, ?_, h4, v1, ?_, hf⟩
  · rw [show x - 1 + 1 = x by omega]; nlinarith
  · rw [show x - 1 + 1 = x by omega]; exact v2

theorem linv_end (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (hV : AllV m a (2 * N)) (hT : TInv m a N)
    (f : M → Bool) (R x : Nat) (sm : M) (t : Nat) (hI : LInv m a N f R x sm t) (hf : f (m.op (a x) sm) = true)
    (hpow : ∃ k, x = 2 ^ k) : m.op (a x) sm = rf m a N (R - N) ∧ f (rf m a N (R - N)) = true := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  obtain ⟨v1, v2⟩ := linv_pass m a N hV hT f R x sm t hI'
  obtain ⟨k, hk⟩ := hpow
  have hp : 0 < 2 ^ t := Nat.two_pow_pos t
  have hstart : x * 2 ^ t = N := by
    have hP : x * 2 ^ t = 2 ^ (k + t) := by rw [hk, pow_add]
    have hlt : x * 2 ^ t < 2 * N := by nlinarith
    rw [hP] at h2 hlt ⊢
    rw [hN] at h2 hlt ⊢
    have hb : 2 ^ (k + t) < 2 ^ (h + 1) := by rw [pow_succ]; omega
    have h1' : h ≤ k + t := (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp h2
    have h2' : k + t < h + 1 := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hb
    rw [show k + t = h by omega]
  rw [hstart] at v2
  exact ⟨v2, v2 ▸ hf⟩

def DLInv (a : Nat → M) (N : Nat) (f : M → Bool) (R x : Nat) (sm : M) (t : Nat) : Prop :=
  LInv m a N f R x sm t ∧ f (m.op (a x) sm) = false

theorem dlinv_step (a : Nat → M) (N : Nat) (hV : AllV m a (2 * N)) (hT : TInv m a N) (f : M → Bool) (R x : Nat)
    (sm : M) (t : Nat) (hI : DLInv m a N f R x sm t) (hx : x < N) :
    ∃ t', t = t' + 1 ∧
      (f (m.op (a (2 * x + 1)) sm) = true → DLInv m a N f R (2 * x) (m.op (a (2 * x + 1)) sm) t') ∧
      (f (m.op (a (2 * x + 1)) sm) = false → DLInv m a N f R (2 * x + 1) sm t') := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hI
  have ht : t ≠ 0 := by intro h0; rw [h0] at h2; simp at h2; omega
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hp : 0 < 2 ^ t' := Nat.two_pow_pos t'
  have eL : x * 2 ^ (t' + 1) = 2 * x * 2 ^ t' := by rw [pow_succ]; ring
  have eR : (x + 1) * 2 ^ (t' + 1) = (2 * x + 1 + 1) * 2 ^ t' := by rw [pow_succ]; ring
  have hnode := hT x h1 hx
  have v0 := hV (2 * x) (by omega)
  have v1 := hV (2 * x + 1) (by omega)
  refine ⟨t', rfl, ?_, ?_⟩
  · intro hf
    have hc := node_rf m a N hV hT t' (2 * x + 1) (by omega) (by rw [eR] at h3; omega)
    refine ⟨⟨by omega, by rw [eL] at h2; exact h2, by rw [eR] at h3; nlinarith, h4, m.closed _ _ v1 h5, ?_, hf⟩, ?_⟩
    · rw [h6, ← hc, eR]
      have e : R - (2 * x + 1) * 2 ^ t' = 2 ^ t' + (R - (2 * x + 1 + 1) * 2 ^ t') := by
        rw [eR] at h3; rw [show (2 * x + 1 + 1) * 2 ^ t' = (2 * x + 1) * 2 ^ t' + 2 ^ t' by ring] at h3 ⊢; omega
      have hb : (2 * x + 1) * 2 ^ t' + 2 ^ t' + (R - (2 * x + 1 + 1) * 2 ^ t') ≤ 2 * N := by
        rw [eR] at h3
        have : (2 * x + 1) * 2 ^ t' + 2 ^ t' = (2 * x + 1 + 1) * 2 ^ t' := by ring
        omega
      rw [e, rf_add m a (2 * N) hV _ _ _ hb,
        show (2 * x + 1) * 2 ^ t' + 2 ^ t' = (2 * x + 1 + 1) * 2 ^ t' by ring]
    · rw [← m.assoc _ _ _ v0 v1 h5, ← hnode]; exact h8
  · intro hf
    refine ⟨⟨by omega, by nlinarith, by rw [eR] at h3; exact h3, h4, h5, by rw [← eR]; exact h6, h7⟩, hf⟩

theorem dlinv_exit (a : Nat → M) (N : Nat) (f : M → Bool) (R x : Nat) (sm : M) (t : Nat)
    (hI : DLInv m a N f R x sm t) (hx : N ≤ x) : t = 0 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hI
  by_contra ht
  have : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

/-! ## The height of a node -/

theorem height_eq (N h x t : Nat) (hN : N = 2 ^ h) (hx : 1 ≤ x) (h1 : N ≤ x * 2 ^ t) (h2 : x * 2 ^ t < 2 * N) :
    t = h - Nat.log2 x := by
  have ht : t ≤ h := by
    by_contra hc
    have : 2 ^ (h + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 * N ≤ x * 2 ^ t := by rw [hN, ← pow_succ']; nlinarith
    omega
  have e : 2 ^ h = 2 ^ t * 2 ^ (h - t) := by rw [← pow_add, show t + (h - t) = h by omega]
  rw [hN, e] at h1 h2
  have hp := Nat.two_pow_pos t
  have hlo : 2 ^ (h - t) ≤ x := by
    rw [Nat.mul_comm x] at h1; exact Nat.le_of_mul_le_mul_left h1 hp
  have hhi : x < 2 ^ (h - t + 1) := by
    rw [pow_succ]
    have : 2 ^ t * x < 2 ^ t * (2 ^ (h - t) * 2) := by rw [Nat.mul_comm (2 ^ t) x]; nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hl1 : h - t ≤ Nat.log2 x := (Nat.le_log2 (by omega)).mpr hlo
  have hl2 : Nat.log2 x < h - t + 1 := (Nat.log2_lt (by omega)).mpr hhi
  omega

end Proofs.Cpp.SegmentTreeMath
