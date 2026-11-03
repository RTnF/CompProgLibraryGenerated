import Proofs.TreeDpSpec

namespace Proofs.TreeDpMath
open Proofs.TreeDpAlg Proofs.TreeDpSpec

def par (parent : List Int) (v : Nat) : Nat := (parent.getD v 0).toNat

/-- The vertex the DP of `v` is entered from: `n` stands for "no vertex" at the root. -/
def pp (parent : List Int) (n root v : Nat) : Nat := if v = root then n else par parent v

def pos (ord : List Nat) (v : Nat) : Nat := ord.idxOf v

/-- A rooted tree given by CSR arrays, a parent array and a discovery order. -/
structure TS (head target : List Nat) (parent : List Int) (ord : List Nat) (n root : Nat) : Prop where
  rootlt : root < n
  ordlen : ord.length = n
  ordnd : ord.Nodup
  ordlt : ∀ x ∈ ord, x < n
  ordmem : ∀ x, x < n → x ∈ ord
  rootpar : parent.getD root 0 = (root : Int)
  parlt : ∀ w, w < n → w ≠ root → 0 ≤ parent.getD w 0 ∧ par parent w < n ∧ pos ord (par parent w) < pos ord w
  tgtlt : ∀ v, v < n → ∀ p ∈ arcs head v, tgt target p < n
  cls : ∀ v, v < n → ∀ p ∈ arcs head v,
    (tgt target p ≠ root ∧ parent.getD (tgt target p) 0 = (v : Int)) ∨ (v ≠ root ∧ tgt target p = par parent v)
  nodup : ∀ v, v < n → (nbs head target v).Nodup
  parArc : ∀ v, v < n → v ≠ root → par parent v ∈ nbs head target v
  chArc : ∀ w, w < n → w ≠ root → ∃ p ∈ arcs head (par parent w), tgt target p = w

/-- The arcs from `v` to its children. -/
def kidArcs (head target : List Nat) (parent : List Int) (v : Nat) : List Nat :=
  (arcs head v).filter fun p => decide (parent.getD (tgt target p) 0 = (v : Int))

def kidT (head target : List Nat) (parent : List Int) (v : Nat) : List Nat :=
  (kidArcs head target parent v).map (tgt target)

variable {head target : List Nat} {parent : List Int} {ord : List Nat} {n root : Nat}

theorem TS.parent_not_child (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (hr : v ≠ root) :
    parent.getD (par parent v) 0 ≠ (v : Int) := by
  intro h
  obtain ⟨h0, hlt, hpos⟩ := T.parlt v hv hr
  by_cases hpr : par parent v = root
  · rw [hpr, T.rootpar] at h
    exact hr (by exact_mod_cast h.symm)
  · obtain ⟨h0', hlt', hpos'⟩ := T.parlt (par parent v) hlt hpr
    have : par parent (par parent v) = v := by
      show (parent.getD (par parent v) 0).toNat = v
      rw [h]; simp
    rw [this] at hpos'
    omega

/-- The test `parent[w] == v` on an arc `v -> w` recognises exactly the child arcs. -/
theorem TS.child_iff (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (p : Nat) (hp : p ∈ arcs head v) :
    parent.getD (tgt target p) 0 = (v : Int) ↔ (tgt target p ≠ root ∧ parent.getD (tgt target p) 0 = (v : Int)) := by
  constructor
  · intro h
    rcases T.cls v hv p hp with hc | ⟨hr, hpv⟩
    · exact hc
    · rw [hpv] at h
      exact absurd h (T.parent_not_child v hv hr)
  · exact fun h => h.2

theorem TS.filter_nbs (T : TS head target parent ord n root) (v : Nat) (hv : v < n) :
    (nbs head target v).filter (fun x => decide (x ≠ pp parent n root v)) = kidT head target parent v := by
  unfold nbs kidT kidArcs
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p hp
  have hc := T.child_iff v hv p hp
  by_cases hvr : v = root
  · subst hvr
    simp only [pp, if_true, Function.comp, decide_eq_decide]
    rcases T.cls v hv p hp with ⟨h1, h2⟩ | ⟨h1, _⟩
    · constructor
      · intro _; exact h2
      · intro _; exact Nat.ne_of_lt (T.tgtlt v hv p hp)
    · exact absurd rfl h1
  · simp only [pp, if_neg hvr, Function.comp, decide_eq_decide]
    rcases T.cls v hv p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · intro _; exact h2
      · intro _ h3
        rw [h3] at h2
        exact T.parent_not_child v hv hvr h2
    · constructor
      · intro h; exact absurd h2 h
      · intro h
        rw [h2] at h
        exact absurd h (T.parent_not_child v hv hvr)

theorem pairwise_split (l : List Nat) (hl : l.Pairwise (· < ·)) (p : Nat) (hp : p ∈ l) :
    l = l.filter (fun q => decide (q < p)) ++ p :: l.filter (fun q => decide (p < q)) := by
  induction l with
  | nil => exact absurd hp (by simp)
  | cons a l ih =>
    have hal : ∀ b ∈ l, a < b := (List.pairwise_cons.mp hl).1
    have hl' : l.Pairwise (· < ·) := (List.pairwise_cons.mp hl).2
    by_cases hpa : p = a
    · subst hpa
      have h1 : (p :: l).filter (fun q => decide (q < p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · subst h; simp
        · have := hal b h; simp; omega
      have h2 : (p :: l).filter (fun q => decide (p < q)) = l := by
        rw [List.filter_cons_of_neg (by simp)]
        rw [List.filter_eq_self]
        intro b hb
        have := hal b hb; simpa using this
      rw [h1, h2]; rfl
    · have hpl : p ∈ l := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h hpa
        · exact h
      have hap := hal p hpl
      rw [List.filter_cons_of_pos (by simpa using hap), List.filter_cons_of_neg (by simp; omega)]
      have := ih hl' hpl
      simp only [List.cons_append]
      congr 1

theorem nodup_filter_eq (l : List Nat) (hl : l.Nodup) (a : Nat) :
    l.filter (fun x => decide (x = a)) = if a ∈ l then [a] else [] := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : b ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    by_cases hba : b = a
    · subst hba
      rw [List.filter_cons_of_pos (by simp)]
      rw [List.filter_eq_nil_iff.mpr (fun x hx => by
        have : x ≠ b := fun h => hb (h ▸ hx)
        simp [this])]
      simp
    · rw [List.filter_cons_of_neg (by simpa using hba), ih hl']
      by_cases hal : a ∈ l
      · simp [hal]
      · simp [hal, Ne.symm hba]

theorem TS.pos_lt (T : TS head target parent ord n root) (x : Nat) (hx : x < n) : pos ord x < n := by
  have := List.idxOf_lt_length_of_mem (T.ordmem _ hx)
  rw [T.ordlen] at this; exact this

theorem TS.kid_facts (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (p : Nat)
    (hp : p ∈ kidArcs head target parent v) :
    p ∈ arcs head v ∧ tgt target p < n ∧ tgt target p ≠ root ∧ par parent (tgt target p) = v ∧
      pp parent n root (tgt target p) = v ∧ pos ord v < pos ord (tgt target p) := by
  have hpa : p ∈ arcs head v := (List.mem_filter.mp hp).1
  have hchild : parent.getD (tgt target p) 0 = (v : Int) := by simpa using (List.mem_filter.mp hp).2
  have hxn := T.tgtlt v hv p hpa
  have hxr : tgt target p ≠ root := ((T.child_iff v hv p hpa).mp hchild).1
  have hpar : par parent (tgt target p) = v := by
    show (parent.getD (tgt target p) 0).toNat = v
    rw [hchild]; simp
  obtain ⟨_, _, hpos⟩ := T.parlt _ hxn hxr
  rw [hpar] at hpos
  exact ⟨hpa, hxn, hxr, hpar, by simp only [pp, if_neg hxr, hpar], hpos⟩

theorem dp_deriv (M : CM) (T : TS head target parent ord n root) (dp : List Int)
    (hdp : ∀ v, v < n → dp.getD v 0 = M.su (fold M ((kidT head target parent v).map fun x => dp.getD x 0))) :
    ∀ v, v < n → ∃ f, Ef M head target f (pp parent n root v) v = some (dp.getD v 0) := by
  have key : ∀ m v, v < n → n - pos ord v = m →
      ∃ f, Ef M head target f (pp parent n root v) v = some (dp.getD v 0) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro v hv hm
      have hkids : ∀ x ∈ kidT head target parent v, ∃ f, Ef M head target f v x = some (dp.getD x 0) := by
        intro x hx
        obtain ⟨p, hpk, rfl⟩ := List.mem_map.mp hx
        obtain ⟨_, hxn, hxr, hpar, hpp, hpos⟩ := T.kid_facts v hv p hpk
        have hxord := T.pos_lt _ hxn
        have := ih (n - pos ord (tgt target p)) (by omega) (tgt target p) hxn rfl
        rw [hpp] at this
        exact this
      obtain ⟨f, hf⟩ := ef_succ_of_vals M head target (pp parent n root v) v (fun x => dp.getD x 0)
        (by rw [T.filter_nbs v hv]; exact hkids)
      refine ⟨f + 1, ?_⟩
      rw [hf, T.filter_nbs v hv, hdp v hv]
  exact fun v hv => key _ v hv rfl

/-- The tails of the kid arcs before and after `p`. -/
def kb (head target : List Nat) (parent : List Int) (v p : Nat) : List Nat :=
  ((kidArcs head target parent v).filter fun q => decide (q < p)).map (tgt target)

def ka (head target : List Nat) (parent : List Int) (v p : Nat) : List Nat :=
  ((kidArcs head target parent v).filter fun q => decide (p < q)).map (tgt target)

theorem kidArcs_pairwise (head target : List Nat) (parent : List Int) (v : Nat) :
    (kidArcs head target parent v).Pairwise (· < ·) := by
  unfold kidArcs arcs
  exact (List.pairwise_lt_range').filter _

theorem kidT_split (head target : List Nat) (parent : List Int) (v p : Nat) (hp : p ∈ kidArcs head target parent v) :
    kidT head target parent v = kb head target parent v p ++ tgt target p :: ka head target parent v p := by
  have h := pairwise_split _ (kidArcs_pairwise head target parent v) p hp
  unfold kidT kb ka
  calc (kidArcs head target parent v).map (tgt target)
      = ((kidArcs head target parent v).filter (fun q => decide (q < p)) ++
          p :: (kidArcs head target parent v).filter (fun q => decide (p < q))).map (tgt target) := congrArg (List.map _) h
    _ = _ := by simp

theorem kidT_nodup (T : TS head target parent ord n root) (v : Nat) (hv : v < n) : (kidT head target parent v).Nodup := by
  have hsub : (kidT head target parent v).Sublist (nbs head target v) := by
    unfold kidT kidArcs nbs
    exact (List.filter_sublist).map _
  exact hsub.nodup (T.nodup v hv)

theorem TS.mem_nbs_lt (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (x : Nat)
    (hx : x ∈ nbs head target v) : x < n := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact T.tgtlt v hv p hp

theorem TS.kidT_lt (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (x : Nat)
    (hx : x ∈ kidT head target parent v) : x < n := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact (T.kid_facts v hv p hp).2.1

theorem fold_single (M : CM) (a : Int) (h : M.V a) : fold M [a] = a := by
  simp only [fold, List.foldl_cons, List.foldl_nil]
  exact M.lid a h

/-- The value contributed by the neighbour `x` of `v`: the value of the parent side, or the subtree value of a child. -/
def valf (parent : List Int) (n root : Nat) (dp up : List Int) (v x : Nat) : Int :=
  if x = pp parent n root v then up.getD v 0 else dp.getD x 0

theorem fold_except (M : CM) (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (p : Nat)
    (hp : p ∈ kidArcs head target parent v) (dp up pre suf : List Int)
    (hVdp : ∀ x, x < n → M.V (dp.getD x 0)) (hVup : M.V (up.getD v 0))
    (hup0 : v = root → up.getD v 0 = M.e)
    (hpre : pre.getD p 0 = fold M ((kb head target parent v p).map fun x => dp.getD x 0))
    (hsuf : suf.getD p 0 = fold M ((ka head target parent v p).map fun x => dp.getD x 0)) :
    fold M ((((nbs head target v).filter fun x => decide (x ≠ tgt target p)).map (valf parent n root dp up v))) =
      M.op (M.op (up.getD v 0) (pre.getD p 0)) (suf.getD p 0) := by
  obtain ⟨hpa, hwn, hwr, hwpar, hwpp, hwpos⟩ := T.kid_facts v hv p hp
  have hnd := T.nodup v hv
  have hppw : pp parent n root v ≠ tgt target p := by
    by_cases hvr : v = root
    · simp only [pp, if_pos hvr]; omega
    · simp only [pp, if_neg hvr]
      intro h
      obtain ⟨_, _, hposv⟩ := T.parlt v hv hvr
      rw [h] at hposv
      omega
  have hVval : ∀ x, x ∈ nbs head target v → M.V (valf parent n root dp up v x) := by
    intro x hx
    unfold valf
    by_cases hxp : x = pp parent n root v
    · rw [if_pos hxp]; exact hVup
    · rw [if_neg hxp]; exact hVdp x (T.mem_nbs_lt v hv x hx)
  have hperm := List.filter_append_perm (fun x => decide (x = pp parent n root v))
    ((nbs head target v).filter fun x => decide (x ≠ tgt target p))
  have step1 : fold M ((((nbs head target v).filter fun x => decide (x ≠ tgt target p))).map (valf parent n root dp up v)) =
      fold M ((((nbs head target v).filter fun x => decide (x ≠ tgt target p)).filter (fun x => decide (x = pp parent n root v)) ++
        ((nbs head target v).filter fun x => decide (x ≠ tgt target p)).filter (fun x => !decide (x = pp parent n root v))).map
          (valf parent n root dp up v)) :=
    fold_perm M _ _ (hperm.map _).symm (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hVval x (List.mem_filter.mp hx).1)
  have hA : ((nbs head target v).filter fun x => decide (x ≠ tgt target p)).filter (fun x => decide (x = pp parent n root v)) =
      (nbs head target v).filter (fun x => decide (x = pp parent n root v)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases hx : x = pp parent n root v
    · have : x ≠ tgt target p := fun h => hppw (hx ▸ h)
      simp [hx, this, hppw]
    · simp [hx]
  have hA2 : (nbs head target v).filter (fun x => decide (x = pp parent n root v)) =
      if v = root then [] else [pp parent n root v] := by
    rw [nodup_filter_eq _ hnd]
    by_cases hvr : v = root
    · rw [if_pos hvr]
      rw [if_neg]
      intro hmem
      have := T.mem_nbs_lt v hv _ hmem
      simp only [pp, if_pos hvr] at this
      omega
    · rw [if_neg hvr, if_pos]
      simp only [pp, if_neg hvr]
      exact T.parArc v hv hvr
  have hfoldA : fold M ((((nbs head target v).filter fun x => decide (x ≠ tgt target p)).filter
      (fun x => decide (x = pp parent n root v))).map (valf parent n root dp up v)) = up.getD v 0 := by
    rw [hA, hA2]
    by_cases hvr : v = root
    · rw [if_pos hvr]
      simp only [List.map_nil]
      rw [hup0 hvr]; rfl
    · rw [if_neg hvr]
      simp only [List.map_cons, List.map_nil, valf, if_pos rfl]
      exact fold_single M _ hVup
  have hB : ((nbs head target v).filter fun x => decide (x ≠ tgt target p)).filter (fun x => !decide (x = pp parent n root v)) =
      (kidT head target parent v).filter (fun x => decide (x ≠ tgt target p)) := by
    rw [← T.filter_nbs v hv, List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro x _
    simp [Bool.and_comm]
  have hkn := kidT_nodup T v hv
  have hsplit := kidT_split head target parent v p hp
  have hwk : ∀ x ∈ kb head target parent v p, x ≠ tgt target p := by
    intro x hx hxw
    rw [hsplit] at hkn
    have := List.nodup_append.mp hkn
    exact this.2.2 x hx (tgt target p) (List.mem_cons_self ..) hxw
  have hwa : ∀ x ∈ ka head target parent v p, x ≠ tgt target p := by
    intro x hx hxw
    rw [hsplit] at hkn
    have h1 := (List.nodup_append.mp hkn).2.1
    exact (List.nodup_cons.mp h1).1 (hxw ▸ hx)
  have hfilt : (kidT head target parent v).filter (fun x => decide (x ≠ tgt target p)) =
      kb head target parent v p ++ ka head target parent v p := by
    rw [hsplit, List.filter_append, List.filter_cons_of_neg (by simp)]
    rw [List.filter_eq_self.mpr (fun x hx => by simpa using hwk x hx),
      List.filter_eq_self.mpr (fun x hx => by simpa using hwa x hx)]
  have hmapB : ((kb head target parent v p ++ ka head target parent v p).map (valf parent n root dp up v)) =
      (kb head target parent v p ++ ka head target parent v p).map (fun x => dp.getD x 0) := by
    apply List.map_congr_left
    intro x hx
    have hxk : x ∈ kidT head target parent v := by
      rw [hsplit]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
    have hxnp : x ≠ pp parent n root v := by
      have := (List.mem_filter.mp (by rw [T.filter_nbs v hv]; exact hxk :
        x ∈ (nbs head target v).filter (fun x => decide (x ≠ pp parent n root v)))).2
      simpa using this
    simp [valf, hxnp]
  have hVkb : ∀ y ∈ (kb head target parent v p).map (fun x => dp.getD x 0), M.V y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    apply hVdp
    apply T.kidT_lt v hv
    rw [hsplit]; exact List.mem_append.mpr (Or.inl hx)
  have hVka : ∀ y ∈ (ka head target parent v p).map (fun x => dp.getD x 0), M.V y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    apply hVdp
    apply T.kidT_lt v hv
    rw [hsplit]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
  have hVa : M.V (up.getD v 0) := hVup
  have hAfold : ∀ (a : List Nat) (b : List Nat), True := fun _ _ => trivial
  rw [step1, List.map_append, fold_append M _ _ (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hVval x (List.mem_filter.mp (List.mem_filter.mp hx).1).1)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hVval x (List.mem_filter.mp (List.mem_filter.mp hx).1).1),
    hfoldA, hB, hfilt, hmapB, List.map_append,
    fold_append M _ _ hVkb hVka, ← hpre, ← hsuf]
  rw [M.assoc _ _ _ hVa (by rw [hpre]; exact fold_V M _ hVkb) (by rw [hsuf]; exact fold_V M _ hVka)]

theorem fold_all (M : CM) (T : TS head target parent ord n root) (v : Nat) (hv : v < n) (dp up : List Int)
    (hVdp : ∀ x, x < n → M.V (dp.getD x 0)) (hVup : M.V (up.getD v 0))
    (hup0 : v = root → up.getD v 0 = M.e) :
    fold M ((nbs head target v).map (valf parent n root dp up v)) =
      M.op (up.getD v 0) (fold M ((kidT head target parent v).map fun x => dp.getD x 0)) := by
  have hnd := T.nodup v hv
  have hVval : ∀ x, x ∈ nbs head target v → M.V (valf parent n root dp up v x) := by
    intro x hx
    unfold valf
    by_cases hxp : x = pp parent n root v
    · rw [if_pos hxp]; exact hVup
    · rw [if_neg hxp]; exact hVdp x (T.mem_nbs_lt v hv x hx)
  have hperm := List.filter_append_perm (fun x => decide (x = pp parent n root v)) (nbs head target v)
  have step1 : fold M ((nbs head target v).map (valf parent n root dp up v)) =
      fold M (((nbs head target v).filter (fun x => decide (x = pp parent n root v)) ++
        (nbs head target v).filter (fun x => !decide (x = pp parent n root v))).map (valf parent n root dp up v)) :=
    fold_perm M _ _ (hperm.map _).symm (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hVval x hx)
  have hA2 : (nbs head target v).filter (fun x => decide (x = pp parent n root v)) =
      if v = root then [] else [pp parent n root v] := by
    rw [nodup_filter_eq _ hnd]
    by_cases hvr : v = root
    · rw [if_pos hvr]
      rw [if_neg]
      intro hmem
      have := T.mem_nbs_lt v hv _ hmem
      simp only [pp, if_pos hvr] at this
      omega
    · rw [if_neg hvr, if_pos]
      simp only [pp, if_neg hvr]
      exact T.parArc v hv hvr
  have hfoldA : fold M (((nbs head target v).filter (fun x => decide (x = pp parent n root v))).map
      (valf parent n root dp up v)) = up.getD v 0 := by
    rw [hA2]
    by_cases hvr : v = root
    · rw [if_pos hvr]
      simp only [List.map_nil]
      rw [hup0 hvr]; rfl
    · rw [if_neg hvr]
      simp only [List.map_cons, List.map_nil, valf, if_pos rfl]
      exact fold_single M _ hVup
  have hB : (nbs head target v).filter (fun x => !decide (x = pp parent n root v)) = kidT head target parent v := by
    rw [← T.filter_nbs v hv]
    apply List.filter_congr
    intro x _
    simp
  have hmapB : (kidT head target parent v).map (valf parent n root dp up v) =
      (kidT head target parent v).map (fun x => dp.getD x 0) := by
    apply List.map_congr_left
    intro x hx
    have hxnp : x ≠ pp parent n root v := by
      have := (List.mem_filter.mp (by rw [T.filter_nbs v hv]; exact hx :
        x ∈ (nbs head target v).filter (fun x => decide (x ≠ pp parent n root v)))).2
      simpa using this
    simp [valf, hxnp]
  have hVk : ∀ y ∈ (kidT head target parent v).map (fun x => dp.getD x 0), M.V y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hVdp x (T.kidT_lt v hv x hx)
  rw [step1, List.map_append, fold_append M _ _ (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hVval x (List.mem_filter.mp hx).1)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hVval x (List.mem_filter.mp hx).1),
    hfoldA, hB, hmapB]

theorem up_deriv (M : CM) (T : TS head target parent ord n root) (dp up pre suf : List Int)
    (hdp : ∀ v, v < n → dp.getD v 0 = M.su (fold M ((kidT head target parent v).map fun x => dp.getD x 0)))
    (hVdp : ∀ x, x < n → M.V (dp.getD x 0)) (hVup : ∀ x, x < n → M.V (up.getD x 0))
    (hup0 : up.getD root 0 = M.e)
    (hpre : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      pre.getD p 0 = fold M ((kb head target parent v p).map fun x => dp.getD x 0))
    (hsuf : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      suf.getD p 0 = fold M ((ka head target parent v p).map fun x => dp.getD x 0))
    (hupe : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      up.getD (tgt target p) 0 = M.su (M.op (M.op (up.getD v 0) (pre.getD p 0)) (suf.getD p 0))) :
    ∀ w, w < n → w ≠ root → ∃ f, Ef M head target f w (par parent w) = some (up.getD w 0) := by
  have hdpd := dp_deriv M T dp hdp
  have key : ∀ m w, w < n → w ≠ root → pos ord w = m → ∃ f, Ef M head target f w (par parent w) = some (up.getD w 0) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro w hw hwr hm
      obtain ⟨hw0, hvn, hvpos⟩ := T.parlt w hw hwr
      -- the arc from the parent to w
      obtain ⟨p, hpa, hpw⟩ := T.chArc w hw hwr
      have hchild : parent.getD (tgt target p) 0 = (par parent w : Nat) := by
        rw [hpw]; unfold par; omega
      have hpk : p ∈ kidArcs head target parent (par parent w) := by
        unfold kidArcs
        exact List.mem_filter.mpr ⟨hpa, by simpa using hchild⟩
      have hvals : ∀ x ∈ (nbs head target (par parent w)).filter (fun x => decide (x ≠ w)),
          ∃ f, Ef M head target f (par parent w) x = some (valf parent n root dp up (par parent w) x) := by
        intro x hx
        have hxn := (List.mem_filter.mp hx).1
        have hxw : x ≠ w := by simpa using (List.mem_filter.mp hx).2
        by_cases hxp : x = pp parent n root (par parent w)
        · -- the parent of the parent
          have hvr : par parent w ≠ root := by
            intro h
            rw [hxp] at hxn
            have := T.mem_nbs_lt _ hvn _ hxn
            simp only [pp, if_pos h] at this
            omega
          have hxpar : x = par parent (par parent w) := by
            rw [hxp]; simp only [pp, if_neg hvr]
          have := ih (pos ord (par parent w)) (by omega) (par parent w) hvn hvr rfl
          rw [valf, if_pos hxp, hxpar]
          exact this
        · have hxk : x ∈ kidT head target parent (par parent w) := by
            rw [← T.filter_nbs _ hvn]
            exact List.mem_filter.mpr ⟨hxn, by simpa using hxp⟩
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxk
          obtain ⟨_, _, _, _, hpp, _⟩ := T.kid_facts _ hvn q hq
          obtain ⟨f, hf⟩ := hdpd (tgt target q) (T.kidT_lt _ hvn _ hxk)
          rw [hpp] at hf
          exact ⟨f, by rw [valf, if_neg hxp]; exact hf⟩
      obtain ⟨f, hf⟩ := ef_succ_of_vals M head target w (par parent w) (valf parent n root dp up (par parent w)) hvals
      refine ⟨f + 1, ?_⟩
      rw [hf]
      have hfe := fold_except M T (par parent w) hvn p hpk dp up pre suf hVdp (hVup _ hvn)
        (fun hr => by
          have : par parent w = root := hr
          rw [this]; exact hup0)
        (hpre _ hvn p hpk) (hsuf _ hvn p hpk)
      rw [hpw] at hfe
      rw [hfe]
      have := hupe _ hvn p hpk
      rw [hpw] at this
      rw [this]
  exact fun w hw hwr => key _ w hw hwr rfl

theorem full_deriv (M : CM) (T : TS head target parent ord n root) (dp up full' : List Int)
    (hdp : ∀ v, v < n → dp.getD v 0 = M.su (fold M ((kidT head target parent v).map fun x => dp.getD x 0)))
    (hVdp : ∀ x, x < n → M.V (dp.getD x 0)) (hVup : ∀ x, x < n → M.V (up.getD x 0))
    (hup0 : up.getD root 0 = M.e)
    (hderivUp : ∀ w, w < n → w ≠ root → ∃ f, Ef M head target f w (par parent w) = some (up.getD w 0))
    (hfull : ∀ v, v < n → full'.getD v 0 =
      M.su (M.op (up.getD v 0) (fold M ((kidT head target parent v).map fun x => dp.getD x 0)))) :
    ∀ v, v < n → ∃ f, Ef M head target f n v = some (full'.getD v 0) := by
  have hdpd := dp_deriv M T dp hdp
  intro v hv
  have hvals : ∀ x ∈ (nbs head target v).filter (fun x => decide (x ≠ n)),
      ∃ f, Ef M head target f v x = some (valf parent n root dp up v x) := by
    intro x hx
    have hxn := (List.mem_filter.mp hx).1
    by_cases hxp : x = pp parent n root v
    · have hvr : v ≠ root := by
        intro h
        rw [hxp] at hxn
        have := T.mem_nbs_lt _ hv _ hxn
        simp only [pp, if_pos h] at this
        omega
      have hxpar : x = par parent v := by
        rw [hxp]; simp only [pp, if_neg hvr]
      obtain ⟨f, hf⟩ := hderivUp v hv hvr
      exact ⟨f, by rw [valf, if_pos hxp, hxpar]; exact hf⟩
    · have hxk : x ∈ kidT head target parent v := by
        rw [← T.filter_nbs _ hv]
        exact List.mem_filter.mpr ⟨hxn, by simpa using hxp⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxk
      obtain ⟨_, _, _, _, hpp, _⟩ := T.kid_facts _ hv q hq
      obtain ⟨f, hf⟩ := hdpd (tgt target q) (T.kidT_lt _ hv _ hxk)
      rw [hpp] at hf
      exact ⟨f, by rw [valf, if_neg hxp]; exact hf⟩
  obtain ⟨f, hf⟩ := ef_succ_of_vals M head target n v (valf parent n root dp up v) hvals
  refine ⟨f + 1, ?_⟩
  rw [hf]
  have hfilt : (nbs head target v).filter (fun x => decide (x ≠ n)) = nbs head target v := by
    apply List.filter_eq_self.mpr
    intro x hx
    have := T.mem_nbs_lt v hv x hx
    simpa using Nat.ne_of_lt this
  rw [hfilt]
  have hfa := fold_all M T v hv dp up hVdp (hVup v hv) (fun hr => by rw [hr]; exact hup0)
  rw [hfa, hfull v hv]

end Proofs.TreeDpMath
