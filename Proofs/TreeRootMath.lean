namespace Proofs.TreeRootMath

/-- The model state of `tree_root`: the three result vectors, the order in which vertices were discovered (`L`, a ghost),
and the contents of the live part of the stack (`S`). -/
structure St where
  par : List Int
  dep : List Int
  cd : List Int
  L : List Nat
  S : List Nat

/-- Looking at the arc `p` leaving `v`. -/
def relax (target : List Nat) (cost : List Int) (v p : Nat) (st : St) : St :=
  if st.par.getD (target.getD p 0) 0 < 0 then
    { par := st.par.set (target.getD p 0) (v : Int)
      dep := st.dep.set (target.getD p 0) (st.dep.getD v 0 + 1)
      cd := st.cd.set (target.getD p 0) (st.cd.getD v 0 + cost.getD p 0)
      L := st.L ++ [target.getD p 0]
      S := st.S ++ [target.getD p 0] }
  else st

/-- The arcs leaving `v`. -/
def arcs (head : List Nat) (v : Nat) : List Nat := List.range' (head.getD v 0) (head.getD (v + 1) 0 - head.getD v 0)

/-- Popping the top `v` of the stack and looking at all arcs leaving it. -/
def procV (head target : List Nat) (cost : List Int) (v : Nat) (st : St) : St :=
  (arcs head v).foldl (fun s p => relax target cost v p s) { st with S := st.S.dropLast }

/-- One iteration of the main loop. -/
def step (head target : List Nat) (cost : List Int) (st : St) : St :=
  match st.S.getLast? with
  | none => st
  | some v => procV head target cost v st

/-- The state after `root` has been marked and pushed. -/
def initSt (par dep cd : List Int) (root : Nat) : St :=
  { par := par.set root (root : Int), dep := dep.set root 0, cd := cd.set root 0, L := [root], S := [root] }

def runL (head target : List Nat) (cost : List Int) (k : Nat) (st : St) : St :=
  (List.range k).foldl (fun s _ => step head target cost s) st

/-- Reachability from `root` along the arcs. -/
inductive Reach (head target : List Nat) (root : Nat) : Nat → Prop
  | base : Reach head target root root
  | arc (u p : Nat) : Reach head target root u → p ∈ arcs head u → Reach head target root (target.getD p 0)

theorem getD_set_same (l : List Int) (w : Nat) (x : Int) (h : w < l.length) : (l.set w x).getD w 0 = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (l : List Int) (w w' : Nat) (x : Int) (h : w' ≠ w) : (l.set w x).getD w' 0 = l.getD w' 0 := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem getD_set_ne_symm (l : List Int) (w w' : Nat) (x : Int) (h : w ≠ w') : (l.set w x).getD w' 0 = l.getD w' 0 :=
  getD_set_ne l w w' x (Ne.symm h)

/-- The invariant of the main loop. -/
structure InvB (head target : List Nat) (cost : List Int) (n root : Nat) (Cb : Nat) (st : St) : Prop where
  lenP : st.par.length = n
  lenD : st.dep.length = n
  lenC : st.cd.length = n
  Lnd : st.L.Nodup
  Llt : ∀ x ∈ st.L, x < n
  vis : ∀ v, v < n → (0 ≤ st.par.getD v 0 ↔ v ∈ st.L)
  Ssub : ∀ x ∈ st.S, x ∈ st.L
  Snd : st.S.Nodup
  edge : ∀ v ∈ st.L, v ≠ root →
    ∃ p, p ∈ arcs head (st.par.getD v 0).toNat ∧ target.getD p 0 = v ∧ (st.par.getD v 0).toNat ∈ st.L ∧
      st.dep.getD v 0 = st.dep.getD (st.par.getD v 0).toNat 0 + 1 ∧
      st.cd.getD v 0 = st.cd.getD (st.par.getD v 0).toNat 0 + cost.getD p 0
  rootv : root ∈ st.L ∧ st.par.getD root 0 = (root : Int) ∧ st.dep.getD root 0 = 0 ∧ st.cd.getD root 0 = 0
  reach : ∀ v ∈ st.L, Reach head target root v
  depL : ∀ i (hi : i < st.L.length), st.dep.getD st.L[i] 0 ≤ (i : Int) ∧ 0 ≤ st.dep.getD st.L[i] 0
  cdB : ∀ v ∈ st.L, ((st.cd.getD v 0).natAbs : Int) ≤ st.dep.getD v 0 * (Cb : Int)

/-- Every finished vertex other than `ex` has all its targets discovered. -/
def Clos (head target : List Nat) (st : St) (ex : Nat) : Prop :=
  ∀ u ∈ st.L, u ∉ st.S → u ≠ ex → ∀ p ∈ arcs head u, 0 ≤ st.par.getD (target.getD p 0) 0

theorem natAbs_add_le_int (a b : Int) : ((a + b).natAbs : Int) ≤ (a.natAbs : Int) + (b.natAbs : Int) := by
  omega

theorem relax_of_visited (target : List Nat) (cost : List Int) (v p : Nat) (st : St)
    (h : 0 ≤ st.par.getD (target.getD p 0) 0) : relax target cost v p st = st := by
  have h' : ¬ (st.par.getD (target.getD p 0) 0 < 0) := by omega
  simp only [relax, h']
  rfl

theorem relax_new (target : List Nat) (cost : List Int) (v p : Nat) (st : St)
    (h : st.par.getD (target.getD p 0) 0 < 0) : relax target cost v p st =
    { par := st.par.set (target.getD p 0) (v : Int)
      dep := st.dep.set (target.getD p 0) (st.dep.getD v 0 + 1)
      cd := st.cd.set (target.getD p 0) (st.cd.getD v 0 + cost.getD p 0)
      L := st.L ++ [target.getD p 0]
      S := st.S ++ [target.getD p 0] } := by
  simp only [relax, h]
  rfl

/-- Looking at one arc keeps the invariant. -/
theorem relax_invB (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St) (v p : Nat)
    (I : InvB head target cost n root Cb st) (hv : v ∈ st.L) (hp : p ∈ arcs head v)
    (hT : target.getD p 0 < n) (hC : (cost.getD p 0).natAbs ≤ Cb) :
    InvB head target cost n root Cb (relax target cost v p st) := by
  by_cases hvis : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st hvis]; exact I
  · have hneg : st.par.getD (target.getD p 0) 0 < 0 := by omega
    rw [relax_new target cost v p st hneg]
    have hwL : target.getD p 0 ∉ st.L := fun h => hvis ((I.vis _ hT).mpr h)
    have hvn : v < n := I.Llt v hv
    have hvw : v ≠ target.getD p 0 := fun h => hwL (h ▸ hv)
    have hwP : target.getD p 0 < st.par.length := by rw [I.lenP]; exact hT
    have hwD : target.getD p 0 < st.dep.length := by rw [I.lenD]; exact hT
    have hwC : target.getD p 0 < st.cd.length := by rw [I.lenC]; exact hT
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hdj := I.depL j hj
    rw [hjv] at hdj
    generalize hw : target.getD p 0 = w at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [I.lenP]
    · simp [I.lenD]
    · simp [I.lenC]
    · simp only [List.nodup_append]
      exact ⟨I.Lnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
        intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hwL ha⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact I.Llt x h
      · simp at h; subst h; exact hT
    · intro x hx
      simp only [List.mem_append, List.mem_singleton]
      by_cases hxw : x = w
      · subst hxw
        rw [getD_set_same _ _ _ hwP]
        simp
      · rw [getD_set_ne _ _ _ _ hxw]
        rw [I.vis x hx]
        simp [hxw]
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (I.Ssub x h)
      · exact Or.inr h
    · simp only [List.nodup_append]
      exact ⟨I.Snd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
        intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hwL (I.Ssub _ ha)⟩
    · intro x hx hxr
      simp only [List.mem_append, List.mem_singleton] at hx
      by_cases hxw : x = w
      · subst hxw
        rw [getD_set_same _ _ _ hwP]
        have hvn' : ((v : Int)).toNat = v := by omega
        rw [hvn']
        refine ⟨p, hp, hw, by simp [hv], ?_, ?_⟩
        · rw [getD_set_same _ _ _ hwD, getD_set_ne _ _ _ _ hvw]
        · rw [getD_set_same _ _ _ hwC, getD_set_ne _ _ _ _ hvw]
      · have hxL : x ∈ st.L := by
          rcases hx with h | h
          · exact h
          · exact absurd h hxw
        obtain ⟨q, hq, hqt, hqL, hd, hc⟩ := I.edge x hxL hxr
        have hxne : st.par.getD x 0 = ((st.par.getD x 0).toNat : Int) := by
          have := (I.vis x (I.Llt x hxL)).mpr hxL
          omega
        have huw : (st.par.getD x 0).toNat ≠ w := fun h => hwL (h ▸ hqL)
        rw [getD_set_ne st.par w x (v : Int) hxw]
        refine ⟨q, hq, hqt, List.mem_append.mpr (Or.inl hqL), ?_, ?_⟩
        · rw [getD_set_ne st.dep w x _ hxw, getD_set_ne st.dep w _ _ huw]; exact hd
        · rw [getD_set_ne st.cd w x _ hxw, getD_set_ne st.cd w _ _ huw]; exact hc
    · obtain ⟨h1, h2, h3, h4⟩ := I.rootv
      have hrw : root ≠ w := fun h => hwL (h ▸ h1)
      refine ⟨by simp [h1], ?_, ?_, ?_⟩
      · rw [getD_set_ne _ _ _ _ hrw]; exact h2
      · rw [getD_set_ne _ _ _ _ hrw]; exact h3
      · rw [getD_set_ne _ _ _ _ hrw]; exact h4
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with h | h
      · exact I.reach x h
      · subst h; exact hw ▸ Reach.arc v p (I.reach v hv) hp
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hil : i < st.L.length
      · have hgl : (st.L ++ [w])[i] = st.L[i] := List.getElem_append_left hil
        simp only [hgl]
        have hne : st.L[i] ≠ w := fun h => hwL (h ▸ List.getElem_mem hil)
        rw [getD_set_ne _ _ _ _ hne]
        exact I.depL i hil
      · have hieq : i = st.L.length := by omega
        subst hieq
        have hgl : (st.L ++ [w])[st.L.length] = w := by simp
        simp only [hgl]
        rw [getD_set_same _ _ _ hwD]
        omega
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      by_cases hxw : x = w
      · subst hxw
        rw [getD_set_same _ _ _ hwC, getD_set_same _ _ _ hwD]
        have h1 := I.cdB v hv
        have h2 := natAbs_add_le_int (st.cd.getD v 0) (cost.getD p 0)
        have h3 : ((cost.getD p 0).natAbs : Int) ≤ (Cb : Int) := by exact_mod_cast hC
        have : (st.dep.getD v 0 + 1) * (Cb : Int) = st.dep.getD v 0 * (Cb : Int) + (Cb : Int) := by
          rw [Int.add_mul, Int.one_mul]
        rw [this]
        omega
      · have hxL : x ∈ st.L := by
          rcases hx with h | h
          · exact h
          · exact absurd h hxw
        rw [getD_set_ne _ _ _ _ hxw, getD_set_ne _ _ _ _ hxw]
        exact I.cdB x hxL

theorem relax_visits (target : List Nat) (cost : List Int) (v p : Nat) (st : St) (hv : 0 ≤ (v : Int))
    (hP : target.getD p 0 < st.par.length) :
    0 ≤ (relax target cost v p st).par.getD (target.getD p 0) 0 := by
  by_cases h : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st h]; exact h
  · rw [relax_new target cost v p st (by omega)]
    show 0 ≤ (st.par.set (target.getD p 0) (v : Int)).getD (target.getD p 0) 0
    rw [getD_set_same _ _ _ hP]; exact hv

theorem relax_mono (target : List Nat) (cost : List Int) (v p : Nat) (st : St) (y : Nat)
    (h : 0 ≤ st.par.getD y 0) :
    0 ≤ (relax target cost v p st).par.getD y 0 := by
  by_cases hv : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st hv]; exact h
  · rw [relax_new target cost v p st (by omega)]
    show 0 ≤ (st.par.set (target.getD p 0) (v : Int)).getD y 0
    by_cases hy : y = target.getD p 0
    · subst hy; exact absurd h hv
    · rw [getD_set_ne _ _ _ _ hy]; exact h

theorem relax_ext (target : List Nat) (cost : List Int) (v p : Nat) (st : St) :
    ∃ ext, (relax target cost v p st).L = st.L ++ ext ∧ (relax target cost v p st).S = st.S ++ ext := by
  by_cases h : 0 ≤ st.par.getD (target.getD p 0) 0
  · exact ⟨[], by rw [relax_of_visited target cost v p st h]; simp⟩
  · exact ⟨[target.getD p 0], by rw [relax_new target cost v p st (by omega)]; exact ⟨rfl, rfl⟩⟩

theorem relax_len (target : List Nat) (cost : List Int) (v p : Nat) (st : St) :
    (relax target cost v p st).par.length = st.par.length := by
  by_cases h : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st h]
  · rw [relax_new target cost v p st (by omega)]; simp

theorem relax_clos (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St) (v p : Nat) (ex : Nat)
    (I : InvB head target cost n root Cb st) (hT : ∀ q, target.getD q 0 < n) (hc : Clos head target st ex) :
    Clos head target (relax target cost v p st) ex := by
  by_cases h : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st h]; exact hc
  · have hP : target.getD p 0 < st.par.length := by rw [I.lenP]; exact hT p
    have hwL : target.getD p 0 ∉ st.L := fun h' => h ((I.vis _ (hT p)).mpr h')
    rw [relax_new target cost v p st (by omega)]
    intro u hu hS hex q hq
    simp only [List.mem_append, List.mem_singleton] at hu hS
    have huw : u ≠ target.getD p 0 := fun e => hS (Or.inr e)
    have huL : u ∈ st.L := by
      rcases hu with hu | hu
      · exact hu
      · exact absurd hu huw
    have huS : u ∉ st.S := fun e => hS (Or.inl e)
    have hold := hc u huL huS hex q hq
    show 0 ≤ (st.par.set (target.getD p 0) (v : Int)).getD (target.getD q 0) 0
    by_cases hy : target.getD q 0 = target.getD p 0
    · rw [hy, getD_set_same _ _ _ hP]; exact Int.natCast_nonneg v
    · rw [getD_set_ne _ _ _ _ hy]; exact hold

theorem relax_cd_old (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St) (v p : Nat)
    (I : InvB head target cost n root Cb st) (hT : ∀ q, target.getD q 0 < n) (y : Nat) (hy : y ∈ st.L) :
    (relax target cost v p st).cd.getD y 0 = st.cd.getD y 0 := by
  by_cases h : 0 ≤ st.par.getD (target.getD p 0) 0
  · rw [relax_of_visited target cost v p st h]
  · have hwL : target.getD p 0 ∉ st.L := fun h' => h ((I.vis _ (hT p)).mpr h')
    rw [relax_new target cost v p st (by omega)]
    show (st.cd.set (target.getD p 0) (st.cd.getD v 0 + cost.getD p 0)).getD y 0 = st.cd.getD y 0
    exact getD_set_ne _ _ _ _ (fun e => hwL (e ▸ hy))

/-- Folding `relax` over a list of arcs of `v`. -/
theorem fold_relax (head target : List Nat) (cost : List Int) (n root Cb : Nat) (v ex : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb) :
    ∀ (q : List Nat) (st : St), (∀ p ∈ q, p ∈ arcs head v) → InvB head target cost n root Cb st → v ∈ st.L →
      Clos head target st ex →
      let r := q.foldl (fun s p => relax target cost v p s) st
      InvB head target cost n root Cb r ∧ Clos head target r ex ∧ v ∈ r.L ∧
      (∃ ext, r.L = st.L ++ ext ∧ r.S = st.S ++ ext) ∧
      (∀ y, 0 ≤ st.par.getD y 0 → 0 ≤ r.par.getD y 0) ∧
      (∀ p ∈ q, 0 ≤ r.par.getD (target.getD p 0) 0) ∧ r.par.length = st.par.length ∧
      (∀ y ∈ st.L, r.cd.getD y 0 = st.cd.getD y 0)
  | [], st, _, I, hv, hc => by
    refine ⟨I, hc, hv, ⟨[], by simp⟩, fun y h => h, by simp, rfl, fun y _ => rfl⟩
  | p :: q, st, hq, I, hv, hc => by
    simp only [List.foldl_cons]
    have hp : p ∈ arcs head v := hq p (List.mem_cons_self ..)
    have I1 := relax_invB head target cost n root Cb st v p I hv hp (hT p) (hC p)
    obtain ⟨e1, hL1, hS1⟩ := relax_ext target cost v p st
    have hv1 : v ∈ (relax target cost v p st).L := by rw [hL1]; exact List.mem_append.mpr (Or.inl hv)
    have c1 := relax_clos head target cost n root Cb st v p ex I hT hc
    obtain ⟨hI, hcl, hvr, ⟨e2, hL2, hS2⟩, hmono, hall, hlen, hcdp⟩ :=
      fold_relax head target cost n root Cb v ex hT hC q (relax target cost v p st)
        (fun p' hp' => hq p' (List.mem_cons_of_mem _ hp')) I1 hv1 c1
    refine ⟨hI, hcl, hvr, ⟨e1 ++ e2, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hL2, hL1]; simp
    · rw [hS2, hS1]; simp
    · intro y hy
      have hP : target.getD p 0 < st.par.length := by rw [I.lenP]; exact hT p
      exact hmono y (relax_mono target cost v p st y hy)
    · intro p' hp'
      rcases List.mem_cons.mp hp' with e | e
      · subst e
        have hP : target.getD p' 0 < st.par.length := by rw [I.lenP]; exact hT p'
        exact hmono _ (relax_visits target cost v p' st (Int.natCast_nonneg v) hP)
      · exact hall p' e
    · rw [hlen, relax_len]
    · intro y hy
      have hy1 : y ∈ (relax target cost v p st).L := by rw [hL1]; exact List.mem_append.mpr (Or.inl hy)
      rw [hcdp y hy1]
      exact relax_cd_old head target cost n root Cb st v p I (fun q => hT q) y hy

theorem InvB.L_len {head target : List Nat} {cost : List Int} {n root Cb : Nat} {st : St}
    (I : InvB head target cost n root Cb st) : st.L.length ≤ n := by
  have hsub : st.L ⊆ List.range n := fun x hx => List.mem_range.mpr (I.Llt x hx)
  have := List.Nodup.length_le_of_subset I.Lnd hsub
  simpa using this

theorem InvB.S_len {head target : List Nat} {cost : List Int} {n root Cb : Nat} {st : St}
    (I : InvB head target cost n root Cb st) : st.S.length ≤ n := by
  have hsub : st.S ⊆ List.range n := fun x hx => List.mem_range.mpr (I.Llt x (I.Ssub x hx))
  have := List.Nodup.length_le_of_subset I.Snd hsub
  simpa using this

/-- The depth of a discovered vertex is below `n`. -/
theorem InvB.dep_range {head target : List Nat} {cost : List Int} {n root Cb : Nat} {st : St}
    (I : InvB head target cost n root Cb st) {v : Nat} (hv : v ∈ st.L) :
    0 ≤ st.dep.getD v 0 ∧ st.dep.getD v 0 + 1 ≤ (n : Int) := by
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  have hd := I.depL i hi
  rw [hiv] at hd
  have := I.L_len
  omega

/-- A path cost to a discovered vertex plus one more arc stays within `n * Cb`. -/
theorem InvB.cd_range {head target : List Nat} {cost : List Int} {n root Cb : Nat} {st : St}
    (I : InvB head target cost n root Cb st) {v : Nat} (hv : v ∈ st.L) (c : Int) (hc : c.natAbs ≤ Cb) :
    ((st.cd.getD v 0 + c).natAbs : Int) ≤ (n : Int) * (Cb : Int) := by
  have h1 := I.cdB v hv
  obtain ⟨h2, h3⟩ := I.dep_range hv
  have h4 := natAbs_add_le_int (st.cd.getD v 0) c
  have h5 : ((c.natAbs : Nat) : Int) ≤ (Cb : Int) := by exact_mod_cast hc
  have h6 : (st.dep.getD v 0 + 1) * (Cb : Int) ≤ (n : Int) * (Cb : Int) :=
    Int.mul_le_mul_of_nonneg_right h3 (Int.natCast_nonneg Cb)
  have h7 : (st.dep.getD v 0 + 1) * (Cb : Int) = st.dep.getD v 0 * (Cb : Int) + (Cb : Int) := by
    rw [Int.add_mul, Int.one_mul]
  omega

theorem InvB.pop {head target : List Nat} {cost : List Int} {n root Cb : Nat} {st : St}
    (I : InvB head target cost n root Cb st) :
    InvB head target cost n root Cb { st with S := st.S.dropLast } := by
  rcases List.eq_nil_or_concat st.S with h | ⟨S0, b, h0'⟩
  · exact { I with
      Ssub := fun x hx => by simp [h] at hx
      Snd := by rw [h]; exact List.nodup_nil }
  · have h : st.S = S0 ++ [b] := by rw [h0']; simp
    have hdl : st.S.dropLast = S0 := by rw [h]; simp
    exact { I with
      Ssub := fun x hx => I.Ssub x (by
        have h0 : x ∈ S0 := hdl ▸ hx
        rw [h]; exact List.mem_append.mpr (Or.inl h0))
      Snd := by
        have h0 := I.Snd
        rw [h] at h0
        show st.S.dropLast.Nodup
        rw [hdl]
        exact (List.nodup_append.mp h0).1 }

/-- The full invariant between iterations. -/
structure Inv (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St) : Prop where
  B : InvB head target cost n root Cb st
  C : Clos head target st n

theorem step_inv (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb) (st : St)
    (I : Inv head target cost n root Cb st) :
    Inv head target cost n root Cb (step head target cost st) ∧
    (st.S = [] → step head target cost st = st) ∧
    (st.S ≠ [] → (step head target cost st).L.length + st.S.length =
      st.L.length + (step head target cost st).S.length + 1) ∧
    (st.S ≠ [] → ∃ v S0 ext, st.S = S0 ++ [v] ∧ (step head target cost st).L = st.L ++ ext ∧
      (step head target cost st).S = S0 ++ ext ∧ step head target cost st = procV head target cost v st ∧
      (∀ y ∈ st.L, (step head target cost st).cd.getD y 0 = st.cd.getD y 0)) := by
  unfold step
  cases hl : st.S.getLast? with
  | none =>
    have : st.S = [] := List.getLast?_eq_none_iff.mp hl
    exact ⟨I, fun _ => rfl, fun h => absurd this h, fun h => absurd this h⟩
  | some v =>
    obtain ⟨S0, hS0⟩ := List.getLast?_eq_some_iff.mp hl
    have hvL : v ∈ st.L := I.B.Ssub v (by rw [hS0]; simp)
    let st1 : St := { st with S := st.S.dropLast }
    have hdl : st.S.dropLast = S0 := by rw [hS0]; simp
    have I1 : InvB head target cost n root Cb st1 :=
      { I.B with
        Ssub := fun x hx => I.B.Ssub x (by
          have h0 : x ∈ S0 := hdl ▸ hx
          rw [hS0]; exact List.mem_append.mpr (Or.inl h0))
        Snd := by
          have h0 := I.B.Snd
          rw [hS0] at h0
          show st.S.dropLast.Nodup
          rw [hdl]
          exact (List.nodup_append.mp h0).1 }
    have c1 : Clos head target st1 v := by
      intro u hu hS hne q hq
      have hS' : u ∉ S0 := fun h => hS (by show u ∈ st.S.dropLast; rw [hdl]; exact h)
      have : u ∉ st.S := by
        intro hin
        rw [hS0] at hin
        rcases List.mem_append.mp hin with h | h
        · exact hS' h
        · exact hne (by simpa using h)
      exact I.C u hu this (Nat.ne_of_lt (I.B.Llt u hu)) q hq
    obtain ⟨hI, hcl, hvr, ⟨ext, hL, hSx⟩, hmono, hall, hlen, hcdall⟩ :=
      fold_relax head target cost n root Cb v v hT hC (arcs head v) st1 (fun p hp => hp) I1 hvL c1
    have hSl : st.S.length = S0.length + 1 := by rw [hS0]; simp
    have e1 : (List.foldl (fun s p => relax target cost v p s) { st with S := st.S.dropLast } (arcs head v)).L =
        st.L ++ ext := hL
    have e2 : (List.foldl (fun s p => relax target cost v p s) { st with S := st.S.dropLast } (arcs head v)).S =
        st.S.dropLast ++ ext := hSx
    refine ⟨⟨hI, ?_⟩, fun h => by rw [hS0] at h; simp at h, fun _ => ?_, fun _ => ⟨v, S0, ext, hS0, ?_, ?_, rfl, ?_⟩⟩
    · intro u hu hS _ q hq
      by_cases huv : u = v
      · subst huv
        exact hall q hq
      · exact hcl u hu hS huv q hq
    · show (procV head target cost v st).L.length + st.S.length = st.L.length + (procV head target cost v st).S.length + 1
      unfold procV
      rw [e1, e2, hdl]
      simp only [List.length_append]
      omega
    · show (procV head target cost v st).L = st.L ++ ext
      unfold procV
      exact e1
    · show (procV head target cost v st).S = S0 ++ ext
      unfold procV
      rw [e2, hdl]
    · intro y hy
      show (procV head target cost v st).cd.getD y 0 = st.cd.getD y 0
      unfold procV
      exact hcdall y hy

theorem initInv (head target : List Nat) (cost : List Int) (n root Cb : Nat) (par dep cd : List Int)
    (hroot : root < n) (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n)
    (hneg : ∀ v, v < n → par.getD v 0 < 0) :
    Inv head target cost n root Cb (initSt par dep cd root) := by
  have hrP : root < par.length := by omega
  have hrD : root < dep.length := by omega
  have hrC : root < cd.length := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [initSt, hP]
  · simp [initSt, hD]
  · simp [initSt, hCd]
  · simp [initSt]
  · intro x hx; simp [initSt] at hx; omega
  · intro x hx
    show 0 ≤ (par.set root (root : Int)).getD x 0 ↔ x ∈ [root]
    by_cases hxr : x = root
    · subst hxr; rw [getD_set_same _ _ _ hrP]; simp
    · rw [getD_set_ne _ _ _ _ hxr]
      have := hneg x hx
      simp only [List.mem_singleton, hxr, iff_false]; omega
  · intro x hx; simpa [initSt] using hx
  · simp [initSt]
  · intro x hx hne; simp [initSt] at hx; exact absurd hx hne
  · refine ⟨by simp [initSt], ?_, ?_, ?_⟩
    · show (par.set root (root : Int)).getD root 0 = (root : Int)
      rw [getD_set_same _ _ _ hrP]
    · show (dep.set root 0).getD root 0 = 0
      rw [getD_set_same _ _ _ hrD]
    · show (cd.set root 0).getD root 0 = 0
      rw [getD_set_same _ _ _ hrC]
  · intro x hx; simp [initSt] at hx; subst hx; exact Reach.base
  · intro i hi
    simp [initSt] at hi
    subst hi
    show (dep.set root 0).getD root 0 ≤ ((0 : Nat) : Int) ∧ 0 ≤ (dep.set root 0).getD root 0
    rw [getD_set_same _ _ _ hrD]; omega
  · intro x hx
    simp [initSt] at hx; subst hx
    show (((cd.set x 0).getD x 0).natAbs : Int) ≤ (dep.set x 0).getD x 0 * (Cb : Int)
    rw [getD_set_same _ _ _ hrC, getD_set_same _ _ _ hrD]; simp
  · intro u hu hS
    simp [initSt] at hu hS; exact absurd hu hS

/-- The invariant of the first `k` iterations, with the counting needed for termination. -/
structure InvK (head target : List Nat) (cost : List Int) (n root Cb : Nat) (k : Nat) (st : St) : Prop where
  I : Inv head target cost n root Cb st
  le : st.L.length ≤ st.S.length + k
  eq : st.S ≠ [] → st.L.length = st.S.length + k

theorem runL_succ (head target : List Nat) (cost : List Int) (k : Nat) (st : St) :
    runL head target cost (k + 1) st = step head target cost (runL head target cost k st) := by
  unfold runL
  rw [List.range_succ, List.foldl_append]
  rfl

theorem runL_inv (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb) (st : St)
    (I0 : InvK head target cost n root Cb 0 st) : ∀ k, InvK head target cost n root Cb k (runL head target cost k st) := by
  intro k
  induction k with
  | zero => exact I0
  | succ k ih =>
    rw [runL_succ]
    have ih' : InvK head target cost n root Cb k (runL head target cost k st) := ih
    obtain ⟨hI, h1, h2, _⟩ := step_inv head target cost n root Cb hT hC _ ih'.I
    refine ⟨hI, ?_, ?_⟩
    · by_cases hS : (runL head target cost k st).S = []
      · rw [h1 hS]; have := ih'.le; omega
      · have := h2 hS; have := ih'.eq hS; omega
    · intro hne
      by_cases hS : (runL head target cost k st).S = []
      · rw [h1 hS] at hne ⊢; exact absurd hS hne
      · have := h2 hS; have := ih'.eq hS; omega

theorem final_S_nil (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St)
    (I : InvK head target cost n root Cb n st) : st.S = [] := by
  refine Classical.byContradiction (fun hne => ?_)
  have h := I.eq hne
  have hsub : st.L ⊆ List.range n := fun x hx => List.mem_range.mpr (I.I.B.Llt x hx)
  have := List.Nodup.length_le_of_subset I.I.B.Lnd hsub
  have hs : 0 < st.S.length := List.length_pos_iff.mpr hne
  simp at this
  omega

/-- Reachable vertices are exactly the discovered ones. -/
theorem reach_mem (head target : List Nat) (cost : List Int) (n root Cb : Nat) (st : St)
    (hT : ∀ q, target.getD q 0 < n) (I : Inv head target cost n root Cb st) (hS : st.S = []) :
    ∀ v, Reach head target root v → v ∈ st.L := by
  intro v hv
  induction hv with
  | base => exact I.B.rootv.1
  | arc u p _ hp ih =>
    have hc := I.C u ih (by rw [hS]; simp) (Nat.ne_of_lt (I.B.Llt u ih)) p hp
    exact (I.B.vis _ (hT p)).mp hc

theorem runL_final_S (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb)
    (par dep cd : List Int) (hroot : root < n) (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n)
    (hneg : ∀ v, v < n → par.getD v 0 < 0) :
    (runL head target cost n (initSt par dep cd root)).S = [] ∧
    Inv head target cost n root Cb (runL head target cost n (initSt par dep cd root)) := by
  have I0 : InvK head target cost n root Cb 0 (initSt par dep cd root) :=
    ⟨initInv head target cost n root Cb par dep cd hroot hP hD hCd hneg, by simp [initSt], fun _ => by simp [initSt]⟩
  have K := runL_inv head target cost n root Cb hT hC _ I0 n
  exact ⟨final_S_nil head target cost n root Cb _ K, K.I⟩

/-- The specification of `tree_root`. -/
theorem tree_root_spec (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb)
    (par dep cd : List Int) (hroot : root < n) (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n)
    (hneg : ∀ v, v < n → par.getD v 0 < 0) :
    let r := runL head target cost n (initSt par dep cd root)
    r.par.length = n ∧ r.dep.length = n ∧ r.cd.length = n ∧
    r.par.getD root 0 = (root : Int) ∧ r.dep.getD root 0 = 0 ∧ r.cd.getD root 0 = 0 ∧
    (∀ v, v < n → (0 ≤ r.par.getD v 0 ↔ Reach head target root v)) ∧
    (∀ v, v < n → 0 ≤ r.par.getD v 0 → v ≠ root →
      ∃ p, p ∈ arcs head (r.par.getD v 0).toNat ∧ target.getD p 0 = v ∧
        0 ≤ r.par.getD (r.par.getD v 0).toNat 0 ∧
        r.dep.getD v 0 = r.dep.getD (r.par.getD v 0).toNat 0 + 1 ∧
        r.cd.getD v 0 = r.cd.getD (r.par.getD v 0).toNat 0 + cost.getD p 0) ∧
    (∀ v, v < n → 0 ≤ r.par.getD v 0 →
      0 ≤ r.dep.getD v 0 ∧ r.dep.getD v 0 < n ∧ ((r.cd.getD v 0).natAbs : Int) ≤ r.dep.getD v 0 * (Cb : Int)) := by
  intro r
  have I0 : InvK head target cost n root Cb 0 (initSt par dep cd root) :=
    ⟨initInv head target cost n root Cb par dep cd hroot hP hD hCd hneg, by simp [initSt], fun _ => by simp [initSt]⟩
  have K := runL_inv head target cost n root Cb hT hC _ I0 n
  have hS := final_S_nil head target cost n root Cb _ K
  have B := K.I.B
  obtain ⟨h1, h2, h3, h4⟩ := B.rootv
  refine ⟨B.lenP, B.lenD, B.lenC, h2, h3, h4, ?_, ?_, ?_⟩
  · intro v hv
    constructor
    · intro h; exact B.reach v ((B.vis v hv).mp h)
    · intro h; exact (B.vis v hv).mpr (reach_mem head target cost n root Cb _ hT K.I hS v h)
  · intro v hv hp hne
    have hvL : v ∈ r.L := (B.vis v hv).mp hp
    obtain ⟨q, hq, hqt, hqL, hd, hc⟩ := B.edge v hvL hne
    exact ⟨q, hq, hqt, (B.vis _ (B.Llt _ hqL)).mpr hqL, hd, hc⟩
  · intro v hv hp
    have hvL : v ∈ r.L := (B.vis v hv).mp hp
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hvL
    have hd := B.depL i hi
    rw [hiv] at hd
    have hlen : r.L.length ≤ n := by
      have hsub : r.L ⊆ List.range n := fun x hx => List.mem_range.mpr (B.Llt x hx)
      have := List.Nodup.length_le_of_subset B.Lnd hsub
      simpa using this
    have hd' : r.dep.getD v 0 ≤ (i : Int) ∧ 0 ≤ r.dep.getD v 0 := hd
    refine ⟨hd'.2, by omega, B.cdB v hvL⟩

/-- The vertices popped from the stack so far, in order (a ghost for the cost accounting). -/
def stepD (st : St) (D : List Nat) : List Nat :=
  match st.S.getLast? with
  | none => D
  | some v => D ++ [v]

structure GInv (st : St) (D : List Nat) : Prop where
  nd : D.Nodup
  inL : ∀ x ∈ D, x ∈ st.L
  notS : ∀ x ∈ D, x ∉ st.S

theorem ginv_init (par dep cd : List Int) (root : Nat) : GInv (initSt par dep cd root) [] :=
  ⟨List.nodup_nil, fun x hx => by simp at hx, fun x hx => by simp at hx⟩

theorem ginv_step (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb) (st : St) (D : List Nat)
    (I : Inv head target cost n root Cb st) (G : GInv st D) :
    GInv (step head target cost st) (stepD st D) := by
  obtain ⟨I', h1, h2, h3⟩ := step_inv head target cost n root Cb hT hC st I
  by_cases hS : st.S = []
  · have hg : st.S.getLast? = none := by rw [hS]; rfl
    unfold stepD
    rw [hg, h1 hS]
    exact G
  · obtain ⟨v, S0, ext, hS0, hL, hSx, _⟩ := h3 hS
    have hg : st.S.getLast? = some v := by rw [hS0]; simp
    unfold stepD
    rw [hg]
    show GInv (step head target cost st) (D ++ [v])
    have hnd := I'.B.Lnd
    rw [hL] at hnd
    have hdis := (List.nodup_append.mp hnd).2.2
    have hvS : v ∈ st.S := by rw [hS0]; simp
    have hvL : v ∈ st.L := I.B.Ssub v hvS
    have hS0nd := I.B.Snd
    rw [hS0] at hS0nd
    have hvS0 : v ∉ S0 := fun h => (List.nodup_append.mp hS0nd).2.2 v h v (by simp) rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨G.nd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
        intro a ha b hb hab
        simp at hb; subst hb; subst hab
        exact G.notS a ha hvS⟩
    · intro x hx
      rw [hL]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append.mpr (Or.inl (G.inL x h))
      · simp at h; subst h; exact List.mem_append.mpr (Or.inl hvL)
    · intro x hx hxS
      rw [hSx] at hxS
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp hxS with h' | h'
        · exact G.notS x h (by rw [hS0]; exact List.mem_append.mpr (Or.inl h'))
        · exact hdis x (G.inL x h) x h' rfl
      · simp at h; subst h
        rcases List.mem_append.mp hxS with h' | h'
        · exact hvS0 h'
        · exact hdis x hvL x h' rfl

/-- The farthest vertex found so far, updated when a vertex is popped. -/
def stepF (st : St) (F : Nat) : Nat :=
  match st.S.getLast? with
  | none => F
  | some v => if st.cd.getD F 0 < st.cd.getD v 0 then v else F

structure GInv2 (st : St) (D : List Nat) (F : Nat) : Prop where
  g : GInv st D
  cover : ∀ x ∈ st.L, x ∈ D ∨ x ∈ st.S
  Fin : F ∈ st.L
  Fmax : ∀ x ∈ D, st.cd.getD x 0 ≤ st.cd.getD F 0

theorem ginv2_init (par dep cd : List Int) (root : Nat) :
    GInv2 (initSt par dep cd root) [] root :=
  ⟨ginv_init par dep cd root, fun x hx => Or.inr (by simpa [initSt] using hx), by simp [initSt],
    fun x hx => by simp at hx⟩

theorem ginv2_step (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb) (st : St) (D : List Nat) (F : Nat)
    (I : Inv head target cost n root Cb st) (G : GInv2 st D F) :
    GInv2 (step head target cost st) (stepD st D) (stepF st F) := by
  have G1 := ginv_step head target cost n root Cb hT hC st D I G.g
  obtain ⟨I', h1, h2, h3⟩ := step_inv head target cost n root Cb hT hC st I
  by_cases hS : st.S = []
  · have hg : st.S.getLast? = none := by rw [hS]; rfl
    have hD : stepD st D = D := by unfold stepD; rw [hg]
    have hF : stepF st F = F := by unfold stepF; rw [hg]
    have hst := h1 hS
    rw [hD, hF, hst]
    exact G
  · obtain ⟨v, S0, ext, hS0, hL, hSx, hst, hcd⟩ := h3 hS
    have hg : st.S.getLast? = some v := by rw [hS0]; simp
    have hD : stepD st D = D ++ [v] := by unfold stepD; rw [hg]
    have hvS : v ∈ st.S := by rw [hS0]; simp
    have hvL : v ∈ st.L := I.B.Ssub v hvS
    have hFcd : (step head target cost st).cd.getD F 0 = st.cd.getD F 0 := hcd F G.Fin
    have hvcd : (step head target cost st).cd.getD v 0 = st.cd.getD v 0 := hcd v hvL
    refine ⟨G1, ?_, ?_, ?_⟩
    · intro x hx
      rw [hL] at hx
      rcases List.mem_append.mp hx with h | h
      · rcases G.cover x h with h' | h'
        · left; rw [hD]; exact List.mem_append.mpr (Or.inl h')
        · rw [hS0] at h'
          rcases List.mem_append.mp h' with h'' | h''
          · right; rw [hSx]; exact List.mem_append.mpr (Or.inl h'')
          · left; rw [hD]; exact List.mem_append.mpr (Or.inr h'')
      · right; rw [hSx]; exact List.mem_append.mpr (Or.inr h)
    · rw [hL]
      unfold stepF
      rw [hg]
      show (if st.cd.getD F 0 < st.cd.getD v 0 then v else F) ∈ st.L ++ ext
      by_cases hlt : st.cd.getD F 0 < st.cd.getD v 0
      · rw [if_pos hlt]; exact List.mem_append.mpr (Or.inl hvL)
      · rw [if_neg hlt]; exact List.mem_append.mpr (Or.inl G.Fin)
    · intro x hx
      rw [hD] at hx
      have hxL : x ∈ st.L := by
        rcases List.mem_append.mp hx with h | h
        · exact G.g.inL x h
        · simp at h; subst h; exact hvL
      have hxcd : (step head target cost st).cd.getD x 0 = st.cd.getD x 0 := hcd x hxL
      unfold stepF
      rw [hg]
      show (step head target cost st).cd.getD x 0 ≤
        (step head target cost st).cd.getD (if st.cd.getD F 0 < st.cd.getD v 0 then v else F) 0
      by_cases hlt : st.cd.getD F 0 < st.cd.getD v 0
      · rw [if_pos hlt, hvcd, hxcd]
        rcases List.mem_append.mp hx with h | h
        · have := G.Fmax x h; omega
        · simp at h; subst h; omega
      · rw [if_neg hlt, hFcd, hxcd]
        rcases List.mem_append.mp hx with h | h
        · exact G.Fmax x h
        · simp at h; subst h; omega

theorem sum_nodup_le (f : Nat → Nat) : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) →
    (l.map f).sum ≤ ((List.range n).map f).sum := by
  intro n
  induction n with
  | zero =>
    intro l _ hl
    have : l = [] := List.eq_nil_iff_forall_not_mem.mpr (fun x hx => by have := hl x hx; omega)
    subst this; simp
  | succ n ih =>
    intro l hnd hl
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hn : n ∈ l
    · have perm := List.perm_cons_erase hn
      have hs : (l.map f).sum = f n + ((l.erase n).map f).sum := by
        have := List.Perm.sum_nat (List.Perm.map f perm)
        simpa using this
      have hnd' : (l.erase n).Nodup := hnd.erase n
      have hl' : ∀ x ∈ l.erase n, x < n := by
        intro x hx
        have := (List.Nodup.mem_erase_iff hnd).mp hx
        have := hl x this.2
        omega
      have := ih (l.erase n) hnd' hl'
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
      omega
    · have hl' : ∀ x ∈ l, x < n := by
        intro x hx
        have := hl x hx
        have : x ≠ n := fun h => hn (h ▸ hx)
        omega
      have := ih l hnd hl'
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
      omega

theorem sum_outdeg (H : List Nat) (n : Nat) (hmono : ∀ i, i < n → H.getD i 0 ≤ H.getD (i + 1) 0) :
    ((List.range n).map (fun x => H.getD (x + 1) 0 - H.getD x 0)).sum + H.getD 0 0 = H.getD n 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    have := ih (fun i hi => hmono i (by omega))
    have h2 := hmono n (by omega)
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    omega

/-- The farthest vertex: reachable, with the largest `cost_depth` among the reachable vertices. -/
def FarSpec (head target : List Nat) (n root : Nat) (r : St) (F : Nat) : Prop :=
  F < n ∧ Reach head target root F ∧ ∀ v, v < n → Reach head target root v → r.cd.getD v 0 ≤ r.cd.getD F 0

theorem far_spec (head target : List Nat) (cost : List Int) (n root Cb : Nat) (hT : ∀ q, target.getD q 0 < n)
    (r : St) (D : List Nat) (F : Nat) (I : Inv head target cost n root Cb r) (G : GInv2 r D F) (hS : r.S = []) :
    FarSpec head target n root r F := by
  refine ⟨I.B.Llt F G.Fin, I.B.reach F G.Fin, ?_⟩
  intro v hv hr
  have hvL := reach_mem head target cost n root Cb r hT I hS v hr
  rcases G.cover v hvL with h | h
  · exact G.Fmax v h
  · rw [hS] at h; simp at h

/-- What `tree_root` establishes about the final state `r`. -/
def TreeSpec (head target : List Nat) (cost : List Int) (n root Cb : Nat) (r : St) : Prop :=
    r.par.length = n ∧ r.dep.length = n ∧ r.cd.length = n ∧
    r.par.getD root 0 = (root : Int) ∧ r.dep.getD root 0 = 0 ∧ r.cd.getD root 0 = 0 ∧
    (∀ v, v < n → (0 ≤ r.par.getD v 0 ↔ Reach head target root v)) ∧
    (∀ v, v < n → 0 ≤ r.par.getD v 0 → v ≠ root →
      ∃ p, p ∈ arcs head (r.par.getD v 0).toNat ∧ target.getD p 0 = v ∧
        0 ≤ r.par.getD (r.par.getD v 0).toNat 0 ∧
        r.dep.getD v 0 = r.dep.getD (r.par.getD v 0).toNat 0 + 1 ∧
        r.cd.getD v 0 = r.cd.getD (r.par.getD v 0).toNat 0 + cost.getD p 0) ∧
    (∀ v, v < n → 0 ≤ r.par.getD v 0 →
      0 ≤ r.dep.getD v 0 ∧ r.dep.getD v 0 < n ∧ ((r.cd.getD v 0).natAbs : Int) ≤ r.dep.getD v 0 * (Cb : Int))

theorem tree_root_spec2 (head target : List Nat) (cost : List Int) (n root Cb : Nat)
    (hT : ∀ q, target.getD q 0 < n) (hC : ∀ q, (cost.getD q 0).natAbs ≤ Cb)
    (par dep cd : List Int) (hroot : root < n) (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n)
    (hneg : ∀ v, v < n → par.getD v 0 < 0) :
    TreeSpec head target cost n root Cb (runL head target cost n (initSt par dep cd root)) :=
  tree_root_spec head target cost n root Cb hT hC par dep cd hroot hP hD hCd hneg

end Proofs.TreeRootMath
