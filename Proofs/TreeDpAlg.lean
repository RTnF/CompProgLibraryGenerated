namespace Proofs.TreeDpAlg

/-- A commutative monoid (on the values satisfying `V`) with a unary map `su` (`sum_up`). -/
structure CM where
  V : Int → Prop
  op : Int → Int → Int
  e : Int
  su : Int → Int
  he : V e
  closed : ∀ a b, V a → V b → V (op a b)
  suV : ∀ a, V a → V (su a)
  assoc : ∀ a b c, V a → V b → V c → op (op a b) c = op a (op b c)
  comm : ∀ a b, V a → V b → op a b = op b a
  lid : ∀ a, V a → op e a = a

variable (M : CM)

theorem CM.rid (a : Int) (h : M.V a) : M.op a M.e = a := by
  rw [M.comm a M.e h M.he, M.lid a h]

/-- The product of a list, from the left. -/
def fold (xs : List Int) : Int := xs.foldl M.op M.e

theorem foldl_V (xs : List Int) (acc : Int) (hacc : M.V acc) (h : ∀ x ∈ xs, M.V x) : M.V (xs.foldl M.op acc) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (M.closed _ _ hacc (h x (List.mem_cons_self ..))) (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem fold_V (xs : List Int) (h : ∀ x ∈ xs, M.V x) : M.V (fold M xs) := foldl_V M xs M.e M.he h

/-- `foldl` from an accumulator multiplies the accumulator on the left. -/
theorem foldl_acc (xs : List Int) (acc : Int) (hacc : M.V acc) (h : ∀ x ∈ xs, M.V x) :
    xs.foldl M.op acc = M.op acc (fold M xs) := by
  induction xs generalizing acc with
  | nil => simp [fold, M.rid acc hacc]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, M.V y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.foldl_cons]
    rw [ih _ (M.closed _ _ hacc hx) hxs]
    have e1 : fold M (x :: xs) = M.op x (fold M xs) := by
      simp only [fold, List.foldl_cons]
      rw [M.lid x hx]
      have := ih x hx hxs
      rw [this]
      -- ih for acc = x gives foldl op x xs = op x (fold xs)
      rfl
    rw [e1, M.assoc _ _ _ hacc hx (fold_V M xs hxs)]

theorem fold_cons (x : Int) (xs : List Int) (hx : M.V x) (h : ∀ y ∈ xs, M.V y) :
    fold M (x :: xs) = M.op x (fold M xs) := by
  simp only [fold, List.foldl_cons]
  rw [M.lid x hx]
  exact foldl_acc M xs x hx h

theorem fold_append (xs ys : List Int) (hx : ∀ x ∈ xs, M.V x) (hy : ∀ y ∈ ys, M.V y) :
    fold M (xs ++ ys) = M.op (fold M xs) (fold M ys) := by
  induction xs with
  | nil => simp [fold]; exact (M.lid _ (fold_V M ys hy)).symm
  | cons x xs ih =>
    have hx' : ∀ z ∈ xs, M.V z := fun z hz => hx z (List.mem_cons_of_mem _ hz)
    have hx0 := hx x (List.mem_cons_self ..)
    rw [List.cons_append, fold_cons M x _ hx0 (fun z hz => by
          rcases List.mem_append.mp hz with h | h
          · exact hx' z h
          · exact hy z h),
      ih hx', fold_cons M x xs hx0 hx', M.assoc _ _ _ hx0 (fold_V M xs hx') (fold_V M ys hy)]

theorem fold_perm (xs ys : List Int) (hp : xs.Perm ys) (hx : ∀ x ∈ xs, M.V x) : fold M xs = fold M ys := by
  induction hp with
  | nil => rfl
  | cons a p ih =>
    have ha := hx _ (List.mem_cons_self ..)
    have hp' : ∀ z ∈ _, M.V z := fun z hz => hx z (List.mem_cons_of_mem _ hz)
    rw [fold_cons M _ _ ha hp', fold_cons M _ _ ha (fun z hz => hx z (List.mem_cons_of_mem _ (p.symm.subset hz))), ih hp']
  | swap a b l =>
    have ha := hx a (by simp)
    have hb := hx b (by simp)
    have hl : ∀ z ∈ l, M.V z := fun z hz => hx z (by simp [hz])
    have hbl : ∀ z ∈ b :: l, M.V z := fun z hz => by
      simp at hz; rcases hz with h | h
      · exact h ▸ hb
      · exact hl z h
    have hal : ∀ z ∈ a :: l, M.V z := fun z hz => by
      simp at hz; rcases hz with h | h
      · exact h ▸ ha
      · exact hl z h
    rw [fold_cons M _ _ hb hal, fold_cons M _ _ ha hl, fold_cons M _ _ ha hbl, fold_cons M _ _ hb hl,
      ← M.assoc _ _ _ hb ha (fold_V M l hl), M.comm b a hb ha, M.assoc _ _ _ ha hb (fold_V M l hl)]
  | trans p1 p2 ih1 ih2 =>
    rename_i l1 l2 l3
    exact (ih1 hx).trans (ih2 (fun z hz => hx z (p1.symm.subset hz)))

end Proofs.TreeDpAlg
