namespace Proofs.SegTreeMath

/-- A monoid on the values of the model: `V` is the set of representable values (closed under `op`, containing `e`), and
the laws hold on `V`. -/
structure Mon where
  V : Int → Prop
  op : Int → Int → Int
  e : Int
  closed : ∀ a b, V a → V b → V (op a b)
  he : V e
  assoc : ∀ a b c, V a → V b → V c → op (op a b) c = op a (op b c)
  lid : ∀ a, V a → op e a = a
  rid : ∀ a, V a → op a e = a

variable (m : Mon)

/-- `rfold v a k` is the product of the `k` entries of `v` starting at `a`, from left to right. -/
def rfold (v : List Int) : Nat → Nat → Int
  | _, 0 => m.e
  | a, k + 1 => m.op (v.getD a 0) (rfold v (a + 1) k)

/-- All entries are representable. -/
def AllV (v : List Int) : Prop := ∀ x ∈ v, m.V x

theorem getD_V (v : List Int) (h : AllV m v) (a : Nat) (ha : a < v.length) : m.V (v.getD a 0) := by
  have : v.getD a 0 = v[a] := by simp [List.getD_eq_getElem?_getD, ha]
  rw [this]; exact h _ (List.getElem_mem _)

theorem rfold_V (v : List Int) (h : AllV m v) : ∀ (k a : Nat), a + k ≤ v.length → m.V (rfold m v a k) := by
  intro k
  induction k with
  | zero => intro a _; exact m.he
  | succ k ih =>
    intro a ha
    exact m.closed _ _ (getD_V m v h a (by omega)) (ih (a + 1) (by omega))

theorem rfold_add (v : List Int) (h : AllV m v) :
    ∀ (k1 k2 a : Nat), a + k1 + k2 ≤ v.length → rfold m v a (k1 + k2) = m.op (rfold m v a k1) (rfold m v (a + k1) k2) := by
  intro k1
  induction k1 with
  | zero =>
    intro k2 a ha
    simp only [Nat.zero_add, Nat.add_zero, rfold]
    rw [m.lid _ (rfold_V m v h k2 a (by omega))]
  | succ k ih =>
    intro k2 a ha
    have e : k + 1 + k2 = (k + k2) + 1 := by omega
    rw [e, rfold, ih k2 (a + 1) (by omega), rfold]
    have e2 : a + 1 + k = a + (k + 1) := by omega
    rw [e2, m.assoc _ _ _ (getD_V m v h a (by omega)) (rfold_V m v h k (a + 1) (by omega))
      (rfold_V m v h k2 (a + (k + 1)) (by omega))]

/-- The tree layout: `N` leaves `v[N .. 2N)` and every inner node holds the product of its two children. -/
def TInv (v : List Int) (N : Nat) : Prop :=
  0 < N ∧ v.length = 2 * N ∧ ∀ i, 1 ≤ i → i < N → v.getD i 0 = m.op (v.getD (2 * i) 0) (v.getD (2 * i + 1) 0)

theorem rfold_pairs (v : List Int) (N : Nat) (hV : AllV m v) (h : TInv m v N) :
    ∀ (k a : Nat), 1 ≤ a → a + k ≤ N → rfold m v (2 * a) (2 * k) = rfold m v a k := by
  intro k
  induction k with
  | zero => intro a _ _; simp [rfold]
  | succ k ih =>
    intro a ha hk
    have e2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have hlen := h.2.1
    rw [e2, rfold, rfold]
    have e3 : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
    rw [e3]
    have ihh := ih (a + 1) (by omega) (by omega)
    rw [ihh, rfold]
    have hn := h.2.2 a ha (by omega)
    have v0 := getD_V m v hV (2 * a) (by omega)
    have v1 := getD_V m v hV (2 * a + 1) (by omega)
    have vr := rfold_V m v hV k (a + 1) (by omega)
    rw [← m.assoc _ _ _ v0 v1 (by exact vr), ← hn]

theorem re_eo (a x y r : Int) (va : m.V a) (vx : m.V x) (vy : m.V y) (vr : m.V r) :
    m.op (m.op a (m.op x y)) r = m.op (m.op a x) (m.op y r) := by
  rw [← m.assoc _ _ _ va vx vy, m.assoc _ _ _ (m.closed _ _ va vx) vy vr]

theorem re_oe (a y x r : Int) (va : m.V a) (vy : m.V y) (vx : m.V x) (vr : m.V r) :
    m.op (m.op a (m.op y x)) r = m.op (m.op (m.op a y) x) r := by
  rw [← m.assoc _ _ _ va vy vx]

theorem re_oo (a y x z r : Int) (va : m.V a) (vy : m.V y) (vx : m.V x) (vz : m.V z) (vr : m.V r) :
    m.op (m.op a (m.op y (m.op x z))) r = m.op (m.op (m.op a y) x) (m.op z r) := by
  rw [← m.assoc _ _ _ vy vx vz, ← m.assoc _ _ _ va (m.closed _ _ vy vx) vz, ← m.assoc _ _ _ va vy vx,
    m.assoc _ _ _ (m.closed _ _ (m.closed _ _ va vy) vx) vz vr]

/-- The loop state of `product` after one iteration. -/
def pl1 (l : Nat) : Nat := if l % 2 = 1 then l + 1 else l
def pr1 (r : Nat) : Nat := if r % 2 = 1 then r - 1 else r
def pleft (v : List Int) (l : Nat) (left : Int) : Int := if l % 2 = 1 then m.op left (v.getD l 0) else left
def pright (v : List Int) (r : Nat) (right : Int) : Int := if r % 2 = 1 then m.op (v.getD (r - 1) 0) right else right

/-- The invariant of the product loop: the answer is `left * (nodes [l, r)) * right`. -/
def PInv (v : List Int) (N : Nat) (T : Int) (l r : Nat) (left right : Int) : Prop :=
  1 ≤ l ∧ l ≤ r ∧ r ≤ 2 * N ∧ m.V left ∧ m.V right ∧ m.op (m.op left (rfold m v l (r - l))) right = T

theorem prod_step (v : List Int) (N : Nat) (T : Int) (hV : AllV m v) (h : TInv m v N) (l r : Nat) (left right : Int)
    (hI : PInv m v N T l r left right) (hlr : l < r) :
    PInv m v N T (pl1 l / 2) (pr1 r / 2) (pleft m v l left) (pright m v r right) := by
  obtain ⟨h1, h1', h2, h3, h4, h5⟩ := hI
  have hlen := h.2.1
  have hl1 : 2 ≤ pl1 l := by unfold pl1; split <;> omega
  have hl1e : pl1 l % 2 = 0 := by unfold pl1; split <;> omega
  have hr1e : pr1 r % 2 = 0 := by unfold pr1; split <;> omega
  have hlr1 : pl1 l ≤ pr1 r := by unfold pl1 pr1; split <;> split <;> omega
  have hr1le : pr1 r ≤ r := by unfold pr1; split <;> omega
  have hl1ge : l ≤ pl1 l := by unfold pl1; split <;> omega
  have hVl := getD_V m v hV l (by omega)
  have hVr := getD_V m v hV (r - 1) (by omega)
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · unfold pleft; split
    · exact m.closed _ _ h3 hVl
    · exact h3
  · unfold pright; split
    · exact m.closed _ _ hVr h4
    · exact h4
  · have hpair := rfold_pairs m v N hV h ((pr1 r - pl1 l) / 2) (pl1 l / 2) (by omega) (by omega)
    have e1 : 2 * (pl1 l / 2) = pl1 l := by omega
    have e2 : 2 * ((pr1 r - pl1 l) / 2) = pr1 r - pl1 l := by omega
    rw [e1, e2] at hpair
    have e3 : pr1 r / 2 - pl1 l / 2 = (pr1 r - pl1 l) / 2 := by omega
    rw [e3, ← hpair]
    unfold pleft pright
    have vX := rfold_V m v hV (pr1 r - pl1 l) (pl1 l) (by omega)
    have e5 : rfold m v (r - 1) 1 = v.getD (r - 1) 0 := by
      show m.op (v.getD (r - 1) 0) m.e = _
      exact m.rid _ hVr
    rcases Nat.mod_two_eq_zero_or_one l with hl | hl <;> rcases Nat.mod_two_eq_zero_or_one r with hr | hr
    · have hp1 : pl1 l = l := by simp [pl1, hl]
      have hp2 : pr1 r = r := by simp [pr1, hr]
      simp only [hl, hr, hp1, hp2] at *
      simpa using h5
    · -- l even, r odd
      have hp1 : pl1 l = l := by simp [pl1, hl]
      have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
      have e : r - l = (r - 1 - l) + 1 := by omega
      rw [e, rfold_add m v hV (r - 1 - l) 1 l (by omega)] at h5
      have e4 : l + (r - 1 - l) = r - 1 := by omega
      rw [e4, e5] at h5
      have vX' := rfold_V m v hV (r - 1 - l) l (by omega)
      have hl' : ¬ (l % 2 = 1) := by omega
      simp only [pleft, pright, hl', hr, hp1, hp2, if_true, if_false]
      rw [← h5]
      exact (re_eo m left _ _ right h3 vX' hVr h4).symm
    · -- l odd, r even
      have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
      have hp2 : pr1 r = r := by simp [pr1, hr]
      have e : r - l = (r - (l + 1)) + 1 := by omega
      rw [e, rfold] at h5
      have vX' := rfold_V m v hV (r - (l + 1)) (l + 1) (by omega)
      have hr' : ¬ (r % 2 = 1) := by omega
      simp only [pleft, pright, hl, hr', hp1, hp2, if_true, if_false]
      rw [← h5]
      exact (re_oe m left _ _ right h3 hVl vX' h4).symm
    · -- both odd
      have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
      have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
      have e : r - l = ((r - 1 - (l + 1)) + 1) + 1 := by omega
      rw [e, rfold, rfold_add m v hV (r - 1 - (l + 1)) 1 (l + 1) (by omega)] at h5
      have e4 : l + 1 + (r - 1 - (l + 1)) = r - 1 := by omega
      rw [e4, e5] at h5
      have vX' := rfold_V m v hV (r - 1 - (l + 1)) (l + 1) (by omega)
      simp only [pleft, pright, hl, hr, hp1, hp2, if_true, if_false]
      rw [← h5]
      exact (re_oo m left _ _ _ right h3 hVl vX' hVr h4).symm

theorem PInv_exit (v : List Int) (N : Nat) (T : Int) (l r : Nat) (left right : Int) (h : PInv m v N T l r left right)
    (hlr : ¬ l < r) : m.op left right = T := by
  obtain ⟨_, h1', _, h3, _, h5⟩ := h
  have : r - l = 0 := by omega
  rw [this] at h5
  simp only [rfold] at h5
  rw [m.rid _ h3] at h5
  exact h5

theorem getD_setE (v : List Int) (i : Nat) (x : Int) (j : Nat) :
    (v.set i x).getD j 0 = if j = i ∧ i < v.length then x else v.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

theorem allV_set (v : List Int) (hV : AllV m v) (i : Nat) (x : Int) (hx : m.V x) : AllV m (v.set i x) := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hV y h
  · rw [h]; exact hx

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
def SInv (v : List Int) (N i : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < N → ¬ Anc i j → v.getD j 0 = m.op (v.getD (2 * j) 0) (v.getD (2 * j + 1) 0)

theorem sinv_step (v : List Int) (N i : Nat) (h : SInv m v N i) (hi1 : 1 ≤ i) (hiN : i < N) (hlen : v.length = 2 * N) :
    SInv m (v.set i (m.op (v.getD (2 * i) 0) (v.getD (2 * i + 1) 0))) N (i / 2) := by
  intro j hj1 hjN hna
  have hil : i < v.length := by omega
  by_cases hji : j = i
  · subst hji
    rw [getD_setE, getD_setE, getD_setE]
    have a0 : (j = j ∧ j < v.length) := ⟨rfl, hil⟩
    have a1 : ¬ (2 * j = j ∧ j < v.length) := by omega
    have a2 : ¬ (2 * j + 1 = j ∧ j < v.length) := by omega
    rw [if_pos a0, if_neg a1, if_neg a2]
  · have hna' : ¬ Anc i j := by
      intro ha
      rcases (anc_step i j).mp ha with e | e
      · exact hji e
      · exact hna e
    have hold := h j hj1 hjN hna'
    have c1 : ¬ (2 * j = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    have c2 : ¬ (2 * j + 1 = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    rw [getD_setE, getD_setE, getD_setE]
    have b0 : ¬ (j = i ∧ i < v.length) := fun hh => hji hh.1
    have b1 : ¬ (2 * j = i ∧ i < v.length) := fun hh => c1 hh.1
    have b2 : ¬ (2 * j + 1 = i ∧ i < v.length) := fun hh => c2 hh.1
    rw [if_neg b0, if_neg b1, if_neg b2]
    exact hold

theorem sinv_zero (v : List Int) (N : Nat) (h : SInv m v N 0) :
    ∀ j, 1 ≤ j → j < N → v.getD j 0 = m.op (v.getD (2 * j) 0) (v.getD (2 * j + 1) 0) := by
  intro j hj1 hjN
  apply h j hj1 hjN
  rintro ⟨t, ht⟩
  simp at ht
  omega

theorem sinv_init (v : List Int) (N p : Nat) (val : Int) (hT : TInv m v N) (hp1 : N ≤ p) (hp2 : p < 2 * N) :
    SInv m (v.set p val) N (p / 2) := by
  intro j hj1 hjN hna
  have hpl : p < v.length := by have := hT.2.1; omega
  have c0 : ¬ (j = p) := by omega
  have c1 : ¬ (2 * j = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  have c2 : ¬ (2 * j + 1 = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  rw [getD_setE, getD_setE, getD_setE]
  have b0 : ¬ (j = p ∧ p < v.length) := fun hh => c0 hh.1
  have b1 : ¬ (2 * j = p ∧ p < v.length) := fun hh => c1 hh.1
  have b2 : ¬ (2 * j + 1 = p ∧ p < v.length) := fun hh => c2 hh.1
  rw [if_neg b0, if_neg b1, if_neg b2]
  exact hT.2.2 j hj1 hjN

/-- The nodes `j > i` already hold the product of their children (the build loop goes from `N - 1` down to `1`). -/
def BInv (v : List Int) (N i : Nat) : Prop :=
  ∀ j, i < j → j < N → v.getD j 0 = m.op (v.getD (2 * j) 0) (v.getD (2 * j + 1) 0)

theorem binv_init (v : List Int) (N : Nat) : BInv m v N (N - 1) := by
  intro j h1 h2; omega

theorem binv_step (v : List Int) (N i : Nat) (h : BInv m v N i) (hi1 : 1 ≤ i) (hiN : i < N) (hlen : v.length = 2 * N) :
    BInv m (v.set i (m.op (v.getD (2 * i) 0) (v.getD (2 * i + 1) 0))) N (i - 1) := by
  intro j hj1 hjN
  have hil : i < v.length := by omega
  by_cases hji : j = i
  · subst hji
    rw [getD_setE, getD_setE, getD_setE]
    have a0 : (j = j ∧ j < v.length) := ⟨rfl, hil⟩
    have a1 : ¬ (2 * j = j ∧ j < v.length) := by omega
    have a2 : ¬ (2 * j + 1 = j ∧ j < v.length) := by omega
    rw [if_pos a0, if_neg a1, if_neg a2]
  · have hj : i < j := by omega
    have hold := h j hj hjN
    rw [getD_setE, getD_setE, getD_setE]
    have b0 : ¬ (j = i ∧ i < v.length) := fun hh => hji hh.1
    have b1 : ¬ (2 * j = i ∧ i < v.length) := by omega
    have b2 : ¬ (2 * j + 1 = i ∧ i < v.length) := by omega
    rw [if_neg b0, if_neg b1, if_neg b2]
    exact hold

theorem binv_end (v : List Int) (N : Nat) (h : BInv m v N 0) :
    ∀ j, 1 ≤ j → j < N → v.getD j 0 = m.op (v.getD (2 * j) 0) (v.getD (2 * j + 1) 0) := by
  intro j hj1 hjN
  exact h j (by omega) hjN

end Proofs.SegTreeMath
