namespace Proofs.TopoSortMath

/-- The targets of the edges leaving `v` in the CSR arrays `head`/`target`. -/
def outL (head target : List Nat) (v : Nat) : List Nat :=
  (target.drop (head.getD v 0)).take (head.getD (v + 1) 0 - head.getD v 0)

/-- The number of edges from vertices outside `S` into `w`. -/
def inCnt (head target : List Nat) (n : Nat) (S : List Nat) (w : Nat) : Nat :=
  ((List.range n).map (fun u => if S.contains u then 0 else (outL head target u).count w)).sum

/-- Lowering the counter of `w`; the vertex joins the queue when its counter reaches 0. -/
def decr (w : Nat) (st : List Nat × List Nat) : List Nat × List Nat :=
  (st.1.set w (st.1.getD w 0 - 1), if st.1.getD w 0 - 1 = 0 then st.2 ++ [w] else st.2)

/-- Processing the edges leaving `v`. -/
def procV (head target : List Nat) (v : Nat) (st : List Nat × List Nat) : List Nat × List Nat :=
  (outL head target v).foldl (fun s w => decr w s) st

/-- The `qh`-th iteration of the main loop. -/
def stepQ (head target : List Nat) (qh : Nat) (st : List Nat × List Nat) : List Nat × List Nat :=
  if qh < st.2.length then procV head target (st.2.getD qh 0) st else st

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem sum_zero_map {α : Type} (l : List α) : (l.map (fun _ => 0)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem sum_ite_eq (v c : Nat) : ∀ n, v < n → ((List.range n).map (fun u => if u = v then c else 0)).sum = c := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hv : v < n
    · have := ih hv
      have hne : n ≠ v := Nat.ne_of_gt hv
      rw [this]
      simp [hne]
    · have hvn : v = n := by omega
      subst hvn
      have : ((List.range v).map (fun u => if u = v then c else 0)).sum = 0 := by
        have : (List.range v).map (fun u => if u = v then c else 0) = (List.range v).map (fun _ => 0) := by
          apply List.map_congr_left
          intro u hu
          have := List.mem_range.mp hu
          simp [Nat.ne_of_lt this]
        rw [this]
        exact sum_zero_map _
      simp [this]

theorem inCnt_cons (head target : List Nat) (n : Nat) (S : List Nat) (v : Nat) (hv : v < n) (hnot : v ∉ S) (w : Nat) :
    inCnt head target n S w = inCnt head target n (S ++ [v]) w + (outL head target v).count w := by
  unfold inCnt
  rw [← sum_ite_eq v ((outL head target v).count w) n hv, ← sum_map_add]
  congr 1
  apply List.map_congr_left
  intro u hu
  by_cases huv : u = v
  · subst huv
    simp [hnot]
  · by_cases hS : S.contains u = true
    · simp [hS, huv]
    · simp [hS, huv]


/-- The invariant of Kahn's algorithm: `S` is a prefix of the queue (the vertices already counted as processed), `rest` the
targets of the current vertex that were not yet subtracted. -/
structure Inv (head target : List Nat) (n : Nat) (S rest : List Nat) (st : List Nat × List Nat) : Prop where
  len : st.1.length = n
  lt : ∀ x ∈ st.2, x < n
  nodup : st.2.Nodup
  pre : S.length ≤ st.2.length ∧ S = st.2.take S.length
  cnt : ∀ w, w < n → st.1.getD w 0 = inCnt head target n S w + rest.count w
  mem : ∀ w, w < n → (w ∈ st.2 ↔ st.1.getD w 0 = 0)
  jprop : ∀ j (hj : j < st.2.length), ∀ u, u < n → st.2[j] ∈ outL head target u → u ∈ st.2.take j

theorem getD_set_same (l : List Nat) (w x : Nat) (h : w < l.length) : (l.set w x).getD w 0 = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (l : List Nat) (w w' x : Nat) (h : w' ≠ w) : (l.set w x).getD w' 0 = l.getD w' 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

theorem le_sum_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
  | [], x, h => by simp at h
  | a :: t, x, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := le_sum_mem t x h; omega

theorem inCnt_zero_out (head target : List Nat) (n : Nat) (S : List Nat) (w : Nat) (h : inCnt head target n S w = 0) :
    ∀ u, u < n → u ∉ S → (outL head target u).count w = 0 := by
  intro u hu hS
  unfold inCnt at h
  have hmem : (if S.contains u then 0 else (outL head target u).count w) ∈
      (List.range n).map (fun u => if S.contains u then 0 else (outL head target u).count w) :=
    List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩
  have hz : ∀ x ∈ (List.range n).map (fun u => if S.contains u then 0 else (outL head target u).count w), x = 0 := by
    intro x hx
    have := le_sum_mem _ _ hx
    omega
  have := hz _ hmem
  have hc : S.contains u = false := by simpa using hS
  simp [hc] at this
  exact this hS


theorem decr_inv (head target : List Nat) (n : Nat) (S : List Nat) (w : Nat) (rest : List Nat) (st : List Nat × List Nat)
    (hw : w < n) (I : Inv head target n S (w :: rest) st) : Inv head target n S rest (decr w st) := by
  have hc := I.cnt w hw
  have hcw : List.count w (w :: rest) = List.count w rest + 1 := List.count_cons_self
  have hc1 : 1 ≤ st.1.getD w 0 := by omega
  have hwl : w < st.1.length := by rw [I.len]; exact hw
  have hnotin : w ∉ st.2 := by
    intro h
    have := (I.mem w hw).mp h
    omega
  have hSsub : ∀ u, u ∈ S → u ∈ st.2 := by
    intro u hu
    have := I.pre.2
    rw [this] at hu
    exact List.mem_of_mem_take hu
  have hdec : decr w st = (st.1.set w (st.1.getD w 0 - 1), if st.1.getD w 0 - 1 = 0 then st.2 ++ [w] else st.2) := rfl
  obtain ⟨L, hL⟩ : ∃ L, L = st.1.set w (st.1.getD w 0 - 1) := ⟨_, rfl⟩
  have Lw : L.getD w 0 = st.1.getD w 0 - 1 := by rw [hL]; exact getD_set_same _ _ _ hwl
  have Lne : ∀ w', w' ≠ w → L.getD w' 0 = st.1.getD w' 0 := by intro w' h; rw [hL]; exact getD_set_ne _ _ _ _ h
  have lenNew : L.length = n := by rw [hL, List.length_set]; exact I.len
  have cntNew : ∀ w', w' < n → L.getD w' 0 = inCnt head target n S w' + rest.count w' := by
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      rw [Lw]
      omega
    · rw [Lne w' hww, I.cnt w' hw', List.count_cons_of_ne (Ne.symm hww)]
  rw [hdec, ← hL]
  by_cases hz : st.1.getD w 0 - 1 = 0
  · rw [if_pos hz]
    have hin0 : inCnt head target n S w = 0 := by omega
    refine ⟨lenNew, ?_, ?_, ?_, cntNew, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact I.lt x h
      · have : x = w := by simpa using h
        omega
    · rw [List.nodup_append]
      refine ⟨I.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      have : b = w := by simpa using hb
      subst this
      intro hab
      subst hab
      exact hnotin ha
    · refine ⟨by have := I.pre.1; simp; omega, ?_⟩
      rw [List.take_append_of_le_length I.pre.1]
      exact I.pre.2
    · intro w' hw'
      rw [cntNew w' hw']
      by_cases hww : w' = w
      · subst hww
        simp [hin0]
        omega
      · have e1 := I.cnt w' hw'
        rw [List.count_cons_of_ne (Ne.symm hww)] at e1
        have e2 := I.mem w' hw'
        constructor
        · intro h
          rcases List.mem_append.mp h with h | h
          · have := e2.mp h
            omega
          · exact absurd (by simpa using h) hww
        · intro h
          exact List.mem_append.mpr (Or.inl (e2.mpr (by omega)))
    · intro j hj u hu hmem
      by_cases hjl : j < st.2.length
      · simp only [List.getElem_append_left hjl] at hmem
        rw [List.take_append_of_le_length (Nat.le_of_lt hjl)]
        exact I.jprop j hjl u hu hmem
      · have hjeq : j = st.2.length := by
          have : j < st.2.length + 1 := by simpa using hj
          omega
        subst hjeq
        have hget : (st.2 ++ [w])[st.2.length]'hj = w := by simp
        simp only [hget] at hmem
        rw [List.take_left]
        by_cases hu2 : u ∈ st.2
        · exact hu2
        · exfalso
          have hS : u ∉ S := fun h => hu2 (hSsub u h)
          have h0 := inCnt_zero_out head target n S w hin0 u hu hS
          have := List.count_pos_iff.mpr hmem
          omega
  · rw [if_neg hz]
    refine ⟨lenNew, I.lt, I.nodup, I.pre, cntNew, ?_, I.jprop⟩
    intro w' hw'
    rw [cntNew w' hw']
    by_cases hww : w' = w
    · subst hww
      constructor
      · intro h; exact absurd h hnotin
      · intro h; omega
    · have e1 := I.cnt w' hw'
      rw [List.count_cons_of_ne (Ne.symm hww)] at e1
      have e2 := I.mem w' hw'
      constructor
      · intro h
        have := e2.mp h
        omega
      · intro h
        exact e2.mpr (by omega)


/-- Subtracting a list of targets one by one. -/
theorem procV_fold (head target : List Nat) (n : Nat) (S : List Nat) :
    ∀ (rest : List Nat) (st : List Nat × List Nat), (∀ x ∈ rest, x < n) → Inv head target n S rest st →
      Inv head target n S [] (rest.foldl (fun s w => decr w s) st)
  | [], st, _, I => I
  | w :: rest, st, hr, I => by
    simp only [List.foldl_cons]
    exact procV_fold head target n S rest _ (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      (decr_inv head target n S w rest st (hr w (List.mem_cons_self ..)) I)

theorem outL_lt (head target : List Nat) (n : Nat) (hT : ∀ x ∈ target, x < n) (v : Nat) :
    ∀ x ∈ outL head target v, x < n := by
  intro x hx
  exact hT x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- The invariant between two iterations of the main loop. -/
abbrev Inv0 (head target : List Nat) (n h : Nat) (st : List Nat × List Nat) : Prop :=
  Inv head target n (st.2.take h) [] st

theorem step_pre (head target : List Nat) (n : Nat) (qh : Nat) (st : List Nat × List Nat)
    (I : Inv0 head target n qh st) (hq : qh < st.2.length) :
    Inv head target n (st.2.take (qh + 1)) (outL head target st.2[qh]) st := by
  have hS1 : st.2.take (qh + 1) = st.2.take qh ++ [st.2[qh]] := by
    rw [List.take_succ]
    simp [hq]
  have hvn : st.2[qh] < n := I.lt _ (List.getElem_mem hq)
  have hnot : st.2[qh] ∉ st.2.take qh := by
    intro h
    have hnd := I.nodup
    rw [← List.take_append_drop qh st.2] at hnd
    have dis := (List.nodup_append.mp hnd).2.2
    have hmem : st.2[qh] ∈ st.2.drop qh := by
      rw [List.drop_eq_getElem_cons hq]
      exact List.mem_cons_self ..
    exact dis _ h _ hmem rfl
  refine ⟨I.len, I.lt, I.nodup, ⟨?_, ?_⟩, ?_, I.mem, I.jprop⟩
  · simp [List.length_take]; omega
  · simp [List.length_take]
  · intro w hw
    rw [I.cnt w hw, hS1, inCnt_cons head target n (st.2.take qh) st.2[qh] hvn hnot w]
    simp

theorem stepQ_inv (head target : List Nat) (n : Nat) (hT : ∀ x ∈ target, x < n) (qh : Nat) (st : List Nat × List Nat)
    (I : Inv0 head target n qh st) : Inv0 head target n (qh + 1) (stepQ head target qh st) := by
  unfold stepQ
  by_cases hq : qh < st.2.length
  · rw [if_pos hq]
    have hv : st.2.getD qh 0 = st.2[qh] := by simp [List.getD_eq_getElem?_getD, hq]
    have hS1 : st.2.take (qh + 1) = st.2.take qh ++ [st.2[qh]] := by
      rw [List.take_succ]
      simp [hq]
    have hvn : st.2[qh] < n := I.lt _ (List.getElem_mem hq)
    have hnot : st.2[qh] ∉ st.2.take qh := by
      intro h
      have hnd := I.nodup
      rw [← List.take_append_drop qh st.2] at hnd
      have dis := (List.nodup_append.mp hnd).2.2
      have hmem : st.2[qh] ∈ st.2.drop qh := by
        rw [List.drop_eq_getElem_cons hq]
        exact List.mem_cons_self ..
      exact dis _ h _ hmem rfl
    have J : Inv head target n (st.2.take (qh + 1)) (outL head target st.2[qh]) st := by
      have hlen : (st.2.take qh).length = qh := List.length_take_of_le (by omega)
      refine ⟨I.len, I.lt, I.nodup, ⟨?_, ?_⟩, ?_, I.mem, I.jprop⟩
      · simp [List.length_take]; omega
      · simp [List.length_take]
      · intro w hw
        rw [I.cnt w hw, hS1, inCnt_cons head target n (st.2.take qh) st.2[qh] hvn hnot w]
        simp
    rw [hv]
    have K := procV_fold head target n (st.2.take (qh + 1)) (outL head target st.2[qh]) st (outL_lt head target n hT _) J
    unfold procV
    unfold Inv0
    have hp := K.pre
    rw [show (st.2.take (qh + 1)).length = qh + 1 from List.length_take_of_le (by omega)] at hp
    rw [← hp.2]
    exact K
  · rw [if_neg hq]
    have h1 : st.2.take (qh + 1) = st.2.take qh := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    unfold Inv0
    rw [h1]
    exact I


/-- Running the main loop for `qh = 0 .. k-1`. -/
def kahnL (head target : List Nat) (k : Nat) (st : List Nat × List Nat) : List Nat × List Nat :=
  (List.range k).foldl (fun s qh => stepQ head target qh s) st

theorem kahnL_inv (head target : List Nat) (n : Nat) (hT : ∀ x ∈ target, x < n) (st : List Nat × List Nat)
    (I : Inv0 head target n 0 st) : ∀ k, Inv0 head target n k (kahnL head target k st) := by
  intro k
  induction k with
  | zero => exact I
  | succ k ih =>
    unfold kahnL
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact stepQ_inv head target n hT k _ ih

theorem inCnt_zero_of (head target : List Nat) (n : Nat) (S : List Nat) (w : Nat)
    (h : ∀ u, u < n → u ∉ S → (outL head target u).count w = 0) : inCnt head target n S w = 0 := by
  unfold inCnt
  have : (List.range n).map (fun u => if S.contains u then 0 else (outL head target u).count w) =
      (List.range n).map (fun _ => 0) := by
    apply List.map_congr_left
    intro u hu
    have hu' := List.mem_range.mp hu
    by_cases hS : S.contains u = true
    · simp only [hS, if_true]
    · have : u ∉ S := by simpa using hS
      simp only [hS, if_false]
      exact h u hu' this
  rw [this]
  exact sum_zero_map _

theorem Inv.ord_len (head target : List Nat) (n : Nat) (S rest : List Nat) (st : List Nat × List Nat)
    (I : Inv head target n S rest st) : st.2.length ≤ n := by
  have hsub : st.2 ⊆ List.range n := fun x hx => List.mem_range.mpr (I.lt x hx)
  have := List.Nodup.length_le_of_subset I.nodup hsub
  simpa using this

theorem outL_getD (head target : List Nat) (v d : Nat) (hd : d < (outL head target v).length) :
    (outL head target v).getD d 0 = target.getD (head.getD v 0 + d) 0 := by
  unfold outL at *
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  have : d < head[v + 1]?.getD 0 - head[v]?.getD 0 := by
    simp only [List.length_take, List.length_drop, List.getD_eq_getElem?_getD] at hd
    omega
  rw [if_pos this]

theorem fold_take_succ {α β : Type} (f : β → α → β) (l : List α) (s : β) (d : Nat) (hd : d < l.length) :
    (l.take (d + 1)).foldl f s = f ((l.take d).foldl f s) l[d] := by
  have h : l.take (d + 1) = l.take d ++ [l[d]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hd]
    rfl
  rw [h, List.foldl_append]
  rfl

/-- The final facts: the queue is a prefix of a topological order, and every vertex outside it has a predecessor outside it. -/
theorem kahn_final (head target : List Nat) (n : Nat) (hT : ∀ x ∈ target, x < n) (st : List Nat × List Nat)
    (I : Inv0 head target n 0 st) :
    let r := kahnL head target n st
    r.2.Nodup ∧ (∀ x ∈ r.2, x < n) ∧ r.2.length ≤ n ∧
    (∀ j (hj : j < r.2.length), ∀ u, u < n → r.2[j] ∈ outL head target u → u ∈ r.2.take j) ∧
    (∀ w, w < n → w ∉ r.2 → ∃ u, u < n ∧ u ∉ r.2 ∧ w ∈ outL head target u) := by
  intro r
  have K := kahnL_inv head target n hT st I n
  have hlen : r.2.length ≤ n := by
    have hsub : r.2 ⊆ List.range n := fun x hx => List.mem_range.mpr (K.lt x hx)
    have := List.Nodup.length_le_of_subset K.nodup hsub
    simpa using this
  have htake : r.2.take n = r.2 := List.take_of_length_le hlen
  unfold Inv0 at K
  rw [htake] at K
  refine ⟨K.nodup, K.lt, hlen, K.jprop, ?_⟩
  intro w hw hnot
  have hne : r.1.getD w 0 ≠ 0 := fun h => hnot ((K.mem w hw).mpr h)
  have hc := K.cnt w hw
  have hc' : r.1.getD w 0 = inCnt head target n r.2 w := by simpa using hc
  have hpos : inCnt head target n r.2 w ≠ 0 := by omega
  by_cases hex : ∃ u, u < n ∧ u ∉ r.2 ∧ w ∈ outL head target u
  · exact hex
  · exfalso
    apply hpos
    apply inCnt_zero_of
    intro u hu hS
    by_cases hm : w ∈ outL head target u
    · exact absurd ⟨u, hu, hS, hm⟩ hex
    · exact List.count_eq_zero.mpr hm


/-- Well-formed CSR offsets. -/
structure HeadOK (head target : List Nat) (n : Nat) : Prop where
  len : head.length = n + 1
  zero : head.getD 0 0 = 0
  mono : ∀ i, i < n → head.getD i 0 ≤ head.getD (i + 1) 0
  last : head.getD n 0 = target.length

theorem HeadOK.le (head target : List Nat) (n : Nat) (H : HeadOK head target n) :
    ∀ j, j ≤ n → ∀ i, i ≤ j → head.getD i 0 ≤ head.getD j 0 := by
  intro j
  induction j with
  | zero => intro _ i hi; have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    intro hj i hi
    by_cases h : i = j + 1
    · subst h; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) i (by omega)) (H.mono j (by omega))

theorem flat_out (head target : List Nat) (n : Nat) (H : HeadOK head target n) :
    ∀ k, k ≤ n → (List.range k).flatMap (outL head target) = target.take (head.getD k 0) := by
  intro k
  induction k with
  | zero => intro _; rw [H.zero]; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.flatMap_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hm := H.mono k (by omega)
    have hle : head.getD (k + 1) 0 ≤ target.length := by
      have : head.getD (k + 1) 0 ≤ head.getD n 0 := HeadOK.le head target n H n (Nat.le_refl _) (k + 1) hk
      rw [H.last] at this
      exact this
    unfold outL
    rw [← List.take_add]
    congr 1
    omega


theorem inCnt_nil (head target : List Nat) (n : Nat) (H : HeadOK head target n) (w : Nat) :
    inCnt head target n [] w = target.count w := by
  have h := flat_out head target n H n (Nat.le_refl _)
  rw [H.last, List.take_length] at h
  have hc := congrArg (List.count w) h
  rw [List.count_flatMap] at hc
  unfold inCnt
  simpa [Function.comp_def] using hc

/-- The state after counting the in-degrees and enqueueing the vertices without predecessors. -/
def initSt (target : List Nat) (n : Nat) : List Nat × List Nat :=
  ((List.range n).map (fun w => target.count w), (List.range n).filter (fun w => target.count w = 0))

theorem outL_sub (head target : List Nat) (v : Nat) : ∀ x ∈ outL head target v, x ∈ target := by
  intro x hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem init_inv (head target : List Nat) (n : Nat) (H : HeadOK head target n) (hT : ∀ x ∈ target, x < n) :
    Inv0 head target n 0 (initSt target n) := by
  unfold Inv0 initSt
  have hgd : ∀ w, w < n → ((List.range n).map (fun w => target.count w)).getD w 0 = target.count w := by
    intro w hw
    simp [List.getD_eq_getElem?_getD, hw]
  refine ⟨by simp, ?_, ?_, ⟨by simp, by simp⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact List.mem_range.mp (List.mem_filter.mp hx).1
  · exact (List.nodup_range).filter _
  · intro w hw
    rw [hgd w hw]
    show List.count w target = inCnt head target n (List.take 0 _) w + List.count w []
    rw [List.take_zero, inCnt_nil head target n H w]
    simp
  · intro w hw
    rw [hgd w hw]
    simp [List.mem_filter, hw]
  · intro j hj u hu hmem
    exfalso
    have hx := (List.mem_filter.mp (List.getElem_mem hj)).2
    have hz := of_decide_eq_true hx
    have := List.count_pos_iff.mpr (outL_sub head target u _ hmem)
    omega

end Proofs.TopoSortMath
