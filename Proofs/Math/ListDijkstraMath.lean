import Proofs.Cpp.Lib.Basic
import Proofs.Math.ParentChain

/-! # Dijkstra's algorithm with a lazy priority queue (the math of `ListGraph::dijkstra`)

`out x` lists the edges `(to, cost)` of vertex `x`. The state is the distance array `d`, the parent array `par`
and the queue `Q` of pairs `(key, vertex)`. One step pops a pair with the least key; when the key equals the
distance of the vertex, every edge of the vertex is relaxed (`relax`), pushing the improved pairs. The ghost
state is the list `D` of the processed ("done") vertices, in order, and the last popped key `L`. -/

namespace Proofs.ListDijkstraMath

open Proofs.Cpp Proofs.ParentChain

/-- The edges are valid: endpoints in `[0, n)` and nonnegative costs. -/
def Valid (n : Nat) (out : Nat → List (Int × Int)) : Prop :=
  ∀ x < n, ∀ e ∈ out x, 0 ≤ e.1 ∧ e.1 < n ∧ 0 ≤ e.2

/-- The position of `x` in the processing order (`D.length` for a vertex not yet processed). -/
def rank (D : List Nat) (x : Nat) : Nat := if x ∈ D then D.idxOf x else D.length

/-- Relaxing the edge `e = (y, c)` from `v` (as the loop body of `dijkstra`: the new distance is stored, then read
back for the pushed pair). -/
def relax (v : Int) (st : Array Int × Array Int × List (Int × Int)) (e : Int × Int) :
    Array Int × Array Int × List (Int × Int) :=
  if Cpp.get st.1 v + e.2 < Cpp.get st.1 e.1 then
    (Cpp.set st.1 e.1 (Cpp.get st.1 v + e.2), Cpp.set st.2.1 e.1 v,
      st.2.2 ++ [(Cpp.get (Cpp.set st.1 e.1 (Cpp.get st.1 v + e.2)) e.1, e.1)])
  else st

structure Inv (n s : Nat) (U : Int) (out : Nat → List (Int × Int)) (d par : Array Int) (Q : List (Int × Int))
    (D : List Nat) (L : Int) : Prop where
  sn : s < n
  dsz : d.size = n
  psz : par.size = n
  dnn : ∀ x < n, 0 ≤ d[x]!
  dle : ∀ x < n, d[x]! ≤ U
  ds : d[s]! = 0
  ps : par[s]! = -1
  qok : ∀ q ∈ Q, 0 ≤ q.2 ∧ q.2 < n ∧ d[q.2.toNat]! ≤ q.1 ∧ L ≤ q.1 ∧ q.1 < U
  reach : ∀ x < n, d[x]! < U → x ∈ D ∨ (d[x]!, (x : Int)) ∈ Q
  dD : ∀ x ∈ D, x < n ∧ d[x]! ≤ L ∧ ∀ e ∈ out x, d[e.1.toNat]! ≤ d[x]! + e.2
  nodup : D.Nodup
  parOk : ∀ x < n, x ≠ s → d[x]! < U → ∃ u ∈ D, par[x]! = (u : Int) ∧
    (∃ c, ((x : Int), c) ∈ out u ∧ d[x]! = d[u]! + c) ∧ D.idxOf u < rank D x
  uniq : ∀ x < n, Q.count (d[x]!, (x : Int)) ≤ 1
  stale : ∀ x ∈ D, ∀ q ∈ Q, q.2 = (x : Int) → d[x]! < q.1
  Lu : L < U

/-- The initial state: `d = U` except `d[s] = 0`, no parents, the queue `[(0, s)]`. -/
theorem inv_init (n s : Nat) (U : Int) (out : Nat → List (Int × Int)) (hs : s < n) (hU : 0 < U) :
    Inv n s U out (Cpp.set (Array.replicate n U) (s : Int) 0) (Array.replicate n (-1)) [(0, (s : Int))] [] 0 := by
  have hsz : (s : Int).toNat < (Array.replicate n U).size := by simp; omega
  refine ⟨hs, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, List.nodup_nil, ?_,
    fun x _ => le_trans (List.count_le_length) (by simp), fun x hx => by simp at hx, hU⟩
  · intro x hx; rw [getElemBang_set _ _ _ _ hsz]; split <;> simp [hx] ; omega
  · intro x hx; rw [getElemBang_set _ _ _ _ hsz]; split
    · omega
    · simp [hx]
  · rw [getElemBang_set _ _ _ _ hsz]; simp
  · simp [hs]
  · intro q hq; simp at hq; subst hq; simp
    rw [getElemBang_set _ _ _ _ hsz]; simp; exact ⟨hs, hU⟩
  · intro x hx h
    rw [getElemBang_set _ _ _ _ hsz] at h ⊢
    by_cases e : x = s
    · subst e; simp
    · simp [e, hx] at h
  · intro x hx; simp at hx
  · intro x hx hne h
    rw [getElemBang_set _ _ _ _ hsz] at h
    have e : ¬ x = (s : Int).toNat := by simpa using hne
    simp [hx] at h; omega

theorem idxOf_append_mem {u : Nat} {D L : List Nat} (hu : u ∈ D) : (D ++ L).idxOf u = D.idxOf u := by
  induction D with
  | nil => simp at hu
  | cons a D ih =>
    simp only [List.cons_append, List.idxOf_cons]
    by_cases e : a = u
    · simp [e]
    · have : u ∈ D := by simp at hu; rcases hu with h | h; exact absurd h.symm e; exact h
      simp [e, ih this]

theorem idxOf_append_self {v : Nat} {D : List Nat} (h : v ∉ D) : (D ++ [v]).idxOf v = D.length := by
  induction D with
  | nil => simp
  | cons a D ih =>
    simp only [List.cons_append, List.idxOf_cons, List.length_cons]
    have ha : a ≠ v := fun e => h (by simp [e])
    have hD : v ∉ D := fun e => h (by simp [e])
    simp [ha, ih hD]

theorem perm_count_le {Q Q' : List (Int × Int)} {a b : Int × Int} (h : Q.Perm (a :: Q')) :
    Q'.count b ≤ Q.count b := by
  rw [h.count_eq]; simp [List.count_cons]

theorem perm_count_self {Q Q' : List (Int × Int)} {a : Int × Int} (h : Q.Perm (a :: Q')) :
    Q'.count a + 1 = Q.count a := by
  rw [h.count_eq]; simp [List.count_cons]

theorem perm_mem_of_ne {α : Type} {Q Q' : List α} {a b : α} (h : Q.Perm (a :: Q')) (hb : b ∈ Q) (hne : b ≠ a) :
    b ∈ Q' := by
  have := h.mem_iff.mp hb
  simp at this
  rcases this with e | e
  · exact absurd e hne
  · exact e

theorem perm_mem {α : Type} {Q Q' : List α} {a b : α} (h : Q.Perm (a :: Q')) (hb : b ∈ Q') : b ∈ Q :=
  h.mem_iff.mpr (by simp [hb])

/-- A stale pair (its key exceeds the distance): dropping it keeps the invariant, with the new last key. -/
theorem inv_stale {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q Q' : List (Int × Int)}
    {D : List Nat} {L k : Int} {v : Int} (hI : Inv n s U out d par Q D L) (hQ : Q.Perm ((k, v) :: Q'))
    (hmin : ∀ q ∈ Q, k ≤ q.1) (hst : d[v.toNat]! < k) : Inv n s U out d par Q' D k := by
  have hkv : (k, v) ∈ Q := hQ.mem_iff.mpr List.mem_cons_self
  obtain ⟨_, _, _, hLk, hkU⟩ := hI.qok _ hkv
  refine ⟨hI.sn, hI.dsz, hI.psz, hI.dnn, hI.dle, hI.ds, hI.ps, ?_, ?_, ?_, hI.nodup, hI.parOk,
    fun x hx => le_trans (perm_count_le hQ) (hI.uniq x hx),
    fun x hx q hq => hI.stale x hx q (perm_mem hQ hq), hkU⟩
  · intro q hq
    obtain ⟨h1, h2, h3, _, h5⟩ := hI.qok q (perm_mem hQ hq)
    exact ⟨h1, h2, h3, hmin q (perm_mem hQ hq), h5⟩
  · intro x hx h
    rcases hI.reach x hx h with h' | h'
    · exact Or.inl h'
    · refine Or.inr (perm_mem_of_ne hQ h' ?_)
      intro e
      simp at e
      obtain ⟨e1, e2⟩ := e
      subst e2
      simp at hst
      omega
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := hI.dD x hx
    exact ⟨h1, by omega, h3⟩

/-- During the relaxation of the edges of `v` (distance `k`) from `(d, par, Q')`: `done` are the edges relaxed so
far and `(d', par', Q'')` the current state. -/
structure RInv (n : Nat) (U : Int) (out : Nat → List (Int × Int)) (d par : Array Int) (Q' : List (Int × Int))
    (k : Int) (v : Nat) (done : List (Int × Int)) (d' par' : Array Int) (Q'' : List (Int × Int)) : Prop where
  dsz : d'.size = n
  psz : par'.size = n
  dv : d'[v]! = k
  cases : ∀ x < n, (d'[x]! = d[x]! ∧ par'[x]! = par[x]!) ∨
    (d'[x]! < d[x]! ∧ par'[x]! = (v : Int) ∧ (∃ c, ((x : Int), c) ∈ out v ∧ d'[x]! = k + c) ∧ ((d'[x]!, (x : Int)) ∈ Q''))
  qext : ∀ q ∈ Q'', q ∈ Q' ∨ (0 ≤ q.2 ∧ q.2 < n ∧ d'[q.2.toNat]! ≤ q.1 ∧ k ≤ q.1 ∧ q.1 < U)
  qsub : ∀ q ∈ Q', q ∈ Q''
  proc : ∀ e ∈ done, d'[e.1.toNat]! ≤ k + e.2
  qlen : Q''.length ≤ Q'.length + done.length
  uniq : ∀ x < n, Q''.count (d'[x]!, (x : Int)) ≤ 1
  qge : ∀ q ∈ Q'', 0 ≤ q.2 → q.2 < n → d'[q.2.toNat]! ≤ q.1
  pushes : ∀ q ∈ Q'', q ∉ Q' → q.2 ≠ (v : Int) ∧ ∃ x < n, q.2 = (x : Int) ∧ d'[x]! < d[x]!

theorem RInv.dle {n : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q' : List (Int × Int)}
    {k : Int} {v : Nat} {done : List (Int × Int)} {d' par' : Array Int} {Q'' : List (Int × Int)}
    (h : RInv n U out d par Q' k v done d' par' Q'') (x : Nat) (hx : x < n) : d'[x]! ≤ d[x]! := by
  rcases h.cases x hx with ⟨e, _⟩ | ⟨e, _⟩ <;> omega

theorem rinv_step {n : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q' : List (Int × Int)}
    {k : Int} {v : Nat} {done : List (Int × Int)} {d' par' : Array Int} {Q'' : List (Int × Int)}
    (hdle : ∀ x < n, d[x]! ≤ U)
    (h : RInv n U out d par Q' k v done d' par' Q'') (e : Int × Int) (he : e ∈ out v)
    (hy0 : 0 ≤ e.1) (hyn : e.1 < n) (hc : 0 ≤ e.2) :
    RInv n U out d par Q' k v (done ++ [e]) (relax (v : Int) (d', par', Q'') e).1 (relax (v : Int) (d', par', Q'') e).2.1
      (relax (v : Int) (d', par', Q'') e).2.2 := by
  obtain ⟨y, c⟩ := e
  simp only at hy0 hyn hc
  have hyz : (y.toNat : Int) = y := Int.toNat_of_nonneg hy0
  have hysz : y.toNat < d'.size := by rw [h.dsz]; omega
  have hpsz : y.toNat < par'.size := by rw [h.psz]; omega
  unfold relax
  simp only [get_eq, Int.toNat_natCast, h.dv]
  by_cases hlt : k + c < d'[y.toNat]!
  · simp only [hlt, ↓reduceIte]
    have hkey : (Cpp.set d' y (k + c))[y.toNat]! = k + c := by
      rw [getElemBang_set _ _ _ _ hysz]; simp
    rw [hkey]
    have hyv : y.toNat ≠ v := by
      intro e; rw [e, h.dv] at hlt; omega
    have hdy := h.dle y.toNat (by omega)
    -- no copy of the new pair is in the queue: every copy of `y` has a key at least `d'[y]`
    have hnot : ((k + c, y) : Int × Int) ∉ Q'' := by
      intro hm
      have := h.qge _ hm hy0 hyn
      simp at this; omega
    have hset : ∀ x, (Cpp.set d' y (k + c))[x]! = if x = y.toNat then k + c else d'[x]! :=
      fun x => getElemBang_set _ _ _ _ hysz
    refine ⟨by simp [h.dsz], by simp [h.psz], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getElemBang_set _ _ _ _ hysz, ite_eq_right_iff.mpr (fun e => absurd e.symm hyv)]; exact h.dv
    · intro x hx
      rw [getElemBang_set _ _ _ _ hysz, getElemBang_set _ _ _ _ hpsz]
      by_cases ex : x = y.toNat
      · subst ex
        simp only [↓reduceIte]
        refine Or.inr ⟨by omega, by simp, ⟨c, by rw [hyz]; exact he, rfl⟩, ?_⟩
        rw [hyz]; simp
      · simp only [ex, ↓reduceIte]
        rcases h.cases x hx with h1 | ⟨h1, h2, h3, h4⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2, h3, List.mem_append_left _ h4⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · rcases h.qext q hq with h1 | ⟨h1, h2, h3, h4, h5⟩
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, ?_, h4, h5⟩
          rw [getElemBang_set _ _ _ _ hysz]
          split
          · rename_i e; rw [e] at h3; omega
          · exact h3
      · simp at hq; subst hq
        refine Or.inr ⟨hy0, hyn, ?_, by omega, ?_⟩
        · rw [getElemBang_set _ _ _ _ hysz]; simp
        · have := hdle y.toNat (by omega); omega
    · intro q hq; exact List.mem_append_left _ (h.qsub q hq)
    · intro e' he'
      rw [getElemBang_set _ _ _ _ hysz]
      rcases List.mem_append.mp he' with he' | he'
      · have := h.proc e' he'
        split
        · rename_i e; rw [e] at this; omega
        · exact this
      · simp at he'; subst he'; simp
    · simp; have := h.qlen; omega
    · intro x hx
      rw [hset x, List.count_append]
      by_cases ex : x = y.toNat
      · subst ex; simp only [↓reduceIte, hyz]
        rw [List.count_eq_zero_of_not_mem hnot]; simp
      · simp only [ex, ↓reduceIte]
        have hne : (y : Int) ≠ (x : Int) := by intro e; apply ex; omega
        have := h.uniq x hx
        simp [List.count_cons, hne]; omega
    · intro q hq h0 hn
      rw [hset]
      rcases List.mem_append.mp hq with hq | hq
      · have := h.qge q hq h0 hn
        split
        · rename_i e; rw [e] at this; omega
        · exact this
      · simp at hq; subst hq; simp
    · intro q hq hq'
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨h1, x, hx, h2, h3⟩ := h.pushes q hq hq'
        refine ⟨h1, x, hx, h2, ?_⟩
        rw [hset]; split
        · rename_i e; subst e; omega
        · exact h3
      · simp at hq; subst hq
        refine ⟨by simp; omega, y.toNat, by omega, by simp; omega, ?_⟩
        rw [hset]; simp; omega
  · simp only [hlt, ↓reduceIte]
    have hge := hlt
    refine ⟨h.dsz, h.psz, h.dv, h.cases, h.qext, h.qsub, ?_, by simp; have := h.qlen; omega,
      h.uniq, h.qge, h.pushes⟩
    intro e' he'
    rcases List.mem_append.mp he' with he' | he'
    · exact h.proc e' he'
    · simp at he'; subst he'; simp; omega

theorem rinv_fold {n : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q' : List (Int × Int)}
    {k : Int} {v : Nat} (hdle : ∀ x < n, d[x]! ≤ U)
    (hval : ∀ e ∈ out v, 0 ≤ e.1 ∧ e.1 < n ∧ 0 ≤ e.2) (es done : List (Int × Int)) (hes : done ++ es = out v)
    (st : Array Int × Array Int × List (Int × Int)) (h : RInv n U out d par Q' k v done st.1 st.2.1 st.2.2) :
    RInv n U out d par Q' k v (out v) (es.foldl (relax (v : Int)) st).1 (es.foldl (relax (v : Int)) st).2.1
      (es.foldl (relax (v : Int)) st).2.2 := by
  induction es generalizing done st with
  | nil => simp at hes; subst hes; exact h
  | cons e es ih =>
    simp only [List.foldl_cons]
    have he : e ∈ out v := by rw [← hes]; simp
    obtain ⟨h1, h2, h3⟩ := hval e he
    exact ih (done ++ [e]) (by rw [← hes]; simp) _ (rinv_step hdle h e he h1 h2 h3)

/-- Processing a vertex `v ∉ D` popped with its distance `k`: after relaxing all its edges it is done. -/
theorem inv_fresh {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : Valid n out) {d par : Array Int}
    {Q Q' : List (Int × Int)} {D : List Nat} {L k : Int} {v : Nat} (hI : Inv n s U out d par Q D L)
    (hQ : Q.Perm ((k, (v : Int)) :: Q')) (hmin : ∀ q ∈ Q, k ≤ q.1) (hdv : d[v]! = k) (hvD : v ∉ D) :
    let r := (out v).foldl (relax (v : Int)) (d, par, Q')
    Inv n s U out r.1 r.2.1 r.2.2 (D ++ [v]) k ∧ r.2.2.length ≤ Q'.length + (out v).length := by
  intro r
  have hkv : (k, (v : Int)) ∈ Q := hQ.mem_iff.mpr List.mem_cons_self
  obtain ⟨hv0, hvn, _, hLk, hkU⟩ := hI.qok _ hkv
  have hvn' : v < n := by omega
  have hk0 : 0 ≤ k := by have := hI.dnn v hvn'; omega
  have h0 : RInv n U out d par Q' k v [] d par Q' :=
    ⟨hI.dsz, hI.psz, hdv, fun x _ => Or.inl ⟨rfl, rfl⟩, fun q hq => Or.inl hq, fun q hq => hq,
      fun e he => by simp at he, by simp, fun x hx => le_trans (perm_count_le hQ) (hI.uniq x hx),
      fun q hq _ _ => (hI.qok q (perm_mem hQ hq)).2.2.1, fun q hq hq' => absurd hq hq'⟩
  have hR : RInv n U out d par Q' k v (out v) r.1 r.2.1 r.2.2 :=
    rinv_fold hI.dle (hV v hvn') (out v) [] (by simp) (d, par, Q') h0
  -- the done vertices and the start are not updated
  have hDfix : ∀ x ∈ D, r.1[x]! = d[x]! ∧ r.2.1[x]! = par[x]! := by
    intro x hx
    obtain ⟨hxn, hxL, _⟩ := hI.dD x hx
    rcases hR.cases x hxn with h | ⟨h1, _, ⟨c, hc, h3⟩, _⟩
    · exact h
    · have := (hV v hvn' _ hc).2.2; simp at this; omega
  have hupd : ∀ x < n, r.1[x]! < d[x]! → x ∉ D ∧ x ≠ v := by
    intro x hx hlt
    refine ⟨fun hxD => by rw [(hDfix x hxD).1] at hlt; omega, fun e => ?_⟩
    subst e; rw [hR.dv] at hlt; omega
  have hsfix : r.1[s]! = d[s]! ∧ r.2.1[s]! = par[s]! := by
    rcases hR.cases s hI.sn with h | ⟨h1, _, ⟨c, hc, h3⟩, _⟩
    · exact h
    · have := (hV v hvn' _ hc).2.2; simp at this; rw [hI.ds] at h1; omega
  have hidx : ∀ u ∈ D, (D ++ [v]).idxOf u = D.idxOf u := fun u hu => idxOf_append_mem hu
  have hrank : ∀ x, rank D x ≤ rank (D ++ [v]) x := by
    intro x
    unfold rank
    by_cases hx : x ∈ D
    · simp [hx, hidx x hx]
    · by_cases e : x = v
      · subst e; simp [hx, idxOf_append_self hx]
      · have : x ∉ D ++ [v] := by simp [hx, e]
        simp [hx, this]
  -- the popped pair was the only copy of `(k, v)`
  have hnotkv : ((k, (v : Int)) : Int × Int) ∉ Q' := by
    intro hm
    have h1 := perm_count_self hQ (a := (k, (v : Int)))
    have h2 := hI.uniq v hvn'
    rw [hdv] at h2
    have := List.count_pos_iff.mpr hm
    omega
  refine ⟨⟨hI.sn, hR.dsz, hR.psz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR.uniq, ?_, hkU⟩,
    by have := hR.qlen; simpa using this⟩
  · intro x hx
    rcases hR.cases x hx with ⟨h1, _⟩ | ⟨_, _, ⟨c, hc, h3⟩, _⟩
    · rw [h1]; exact hI.dnn x hx
    · have := (hV v hvn' _ hc).2.2; simp at this; omega
  · intro x hx; have := hR.dle x hx; have := hI.dle x hx; omega
  · rw [hsfix.1]; exact hI.ds
  · rw [hsfix.2]; exact hI.ps
  · intro q hq
    rcases hR.qext q hq with h1 | h1
    · obtain ⟨a1, a2, a3, _, a5⟩ := hI.qok q (perm_mem hQ h1)
      have := hR.dle q.2.toNat (by omega)
      exact ⟨a1, a2, by omega, hmin q (perm_mem hQ h1), a5⟩
    · exact h1
  · intro x hx hlt
    rcases hR.cases x hx with ⟨h1, _⟩ | ⟨_, _, _, h4⟩
    · rw [h1] at hlt ⊢
      rcases hI.reach x hx hlt with h | h
      · exact Or.inl (by simp [h])
      · by_cases e : (d[x]!, (x : Int)) = (k, (v : Int))
        · simp at e; exact Or.inl (by simp [e.2])
        · exact Or.inr (hR.qsub _ (perm_mem_of_ne hQ h e))
    · exact Or.inr h4
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h1, h2, h3⟩ := hI.dD x hx
      refine ⟨h1, by rw [(hDfix x hx).1]; omega, fun e he => ?_⟩
      have := h3 e he
      obtain ⟨_, a2, _⟩ := hV x h1 e he
      have := hR.dle e.1.toNat (by omega)
      rw [(hDfix x hx).1]; omega
    · simp at hx; subst hx
      refine ⟨hvn', by rw [hR.dv], fun e he => ?_⟩
      rw [hR.dv]; exact hR.proc e he
  · rw [List.nodup_append]
    exact ⟨hI.nodup, by simp, fun a ha b hb => by simp at hb; subst hb; exact fun e => hvD (e ▸ ha)⟩
  · intro x hx hxs hlt
    rcases hR.cases x hx with ⟨h1, h2⟩ | ⟨h1, h2, ⟨c, hc, h3⟩, _⟩
    · rw [h1] at hlt
      obtain ⟨u, hu, hpu, ⟨c, hc, hdc⟩, hlt'⟩ := hI.parOk x hx hxs hlt
      refine ⟨u, by simp [hu], by rw [h2]; exact hpu, ⟨c, hc, ?_⟩, ?_⟩
      · rw [h1, (hDfix u hu).1]; exact hdc
      · rw [hidx u hu]; exact Nat.lt_of_lt_of_le hlt' (hrank x)
    · obtain ⟨hxD, hxv⟩ := hupd x hx h1
      refine ⟨v, by simp, h2, ⟨c, hc, by rw [hR.dv]; exact h3⟩, ?_⟩
      have : x ∉ D ++ [v] := by simp [hxD, hxv]
      unfold rank
      simp [this, idxOf_append_self hvD]
  · intro x hx q hq hqx
    by_cases hq' : q ∈ Q'
    · rcases List.mem_append.mp hx with hx | hx
      · rw [(hDfix x hx).1]; exact hI.stale x hx q (perm_mem hQ hq') hqx
      · simp at hx; subst hx
        rw [hR.dv]
        have := (hI.qok q (perm_mem hQ hq')).2.2.1
        rw [hqx] at this; simp at this
        rw [hdv] at this
        by_contra hle
        have e : q = (k, (x : Int)) := by
          obtain ⟨q1, q2⟩ := q; simp at hqx this ⊢; exact ⟨by omega, hqx⟩
        exact hnotkv (e ▸ hq')
    · obtain ⟨h1, y, hy, h2, h3⟩ := hR.pushes q hq hq'
      rcases List.mem_append.mp hx with hx | hx
      · have e : y = x := by rw [hqx] at h2; exact_mod_cast h2.symm
        subst e
        exact absurd hx (hupd y hy h3).1
      · simp at hx; subst hx; exact absurd hqx h1

/-- A pair popped with the distance of its vertex is never of a done vertex. -/
theorem not_redone {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int}
    {Q : List (Int × Int)} {D : List Nat} {L k : Int} {v : Nat} (hI : Inv n s U out d par Q D L)
    (hkv : (k, (v : Int)) ∈ Q) (hdv : d[v]! = k) : v ∉ D := by
  intro hvD
  have := hI.stale v hvD _ hkv rfl
  simp at this; omega

/-! ## The result -/

/-- A walk from `s` to `t` with total cost `w`. -/
inductive Walk (out : Nat → List (Int × Int)) (s : Nat) : Nat → Int → Prop
  | nil : Walk out s s 0
  | cons {u : Nat} {w : Int} (t : Nat) (c : Int) : Walk out s u w → ((t : Int), c) ∈ out u → Walk out s t (w + c)

theorem walk_lt {n s : Nat} {out : Nat → List (Int × Int)} (hV : Valid n out) (hs : s < n) {t : Nat} {w : Int}
    (h : Walk out s t w) : t < n := by
  induction h with
  | nil => exact hs
  | cons t c _ hc ih => have := (hV _ ih _ hc).2.1; omega

/-- At the end (empty queue), the distance of every vertex is at most the cost of every walk to it. -/
theorem final_le {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : Valid n out) {d par : Array Int}
    {D : List Nat} {L : Int} (hI : Inv n s U out d par [] D L) {t : Nat} {w : Int} (h : Walk out s t w) :
    d[t]! ≤ w := by
  induction h with
  | nil => rw [hI.ds]
  | @cons u w t c hw hc ih =>
    have hu := walk_lt hV hI.sn hw
    have hc0 := (hV u hu _ hc).2.2
    have htn := (hV u hu _ hc).2.1
    by_cases hlt : d[u]! < U
    · rcases hI.reach u hu hlt with hD | hq
      · have := (hI.dD u hD).2.2 _ hc
        simp at this; omega
      · simp at hq
    · have := hI.dle t (by simpa using htn); omega

/-- A walk given backwards: the list starts at its end `t` and ends at `s`; `w` is its cost. -/
inductive WalkB (out : Nat → List (Int × Int)) (s : Nat) : List Int → Int → Prop
  | one : WalkB out s [(s : Int)] 0
  | cons (x : Int) (u : Nat) (rest : List Int) (w c : Int) :
      WalkB out s ((u : Int) :: rest) w → (x, c) ∈ out u → WalkB out s (x :: (u : Int) :: rest) (w + c)

/-- At the end, a vertex with a distance below `U` has a parent chain that reaches `-1` through `s`, and the chain
is a walk from `s` (backwards) whose cost is the distance. -/
theorem final_chain {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : Valid n out) {d par : Array Int}
    {D : List Nat} {L : Int} (hI : Inv n s U out d par [] D L) (x : Nat) (hx : x < n) (hlt : d[x]! < U) :
    ∃ C : List Int, Chain par x C ∧ WalkB out s C d[x]! := by
  have hxD : x ∈ D := by
    rcases hI.reach x hx hlt with h | h
    · exact h
    · simp at h
  -- strong induction on the position in D
  suffices H : ∀ m, ∀ x, x ∈ D → D.idxOf x < m → x < n → d[x]! < U →
      ∃ C : List Int, Chain par x C ∧ WalkB out s C d[x]! from
    H (D.idxOf x + 1) x hxD (by omega) hx hlt
  intro m
  induction m with
  | zero => intro x _ h; omega
  | succ m ih =>
    intro x hxD hm hx hlt
    by_cases hxs : x = s
    · subst hxs
      refine ⟨[(x : Int)], Chain.step _ _ (by omega) ?_, by rw [hI.ds]; exact WalkB.one⟩
      have : Cpp.get par (x : Int) = -1 := hI.ps
      rw [this]; exact Chain.stop
    · obtain ⟨u, hu, hpu, ⟨c, hc, hdc⟩, hrk⟩ := hI.parOk x hx hxs hlt
      have hun := (hI.dD u hu).1
      have hc0 := (hV u hun _ hc).2.2
      have hrx : rank D x = D.idxOf x := by unfold rank; simp [hxD]
      rw [hrx] at hrk
      obtain ⟨C, hC, hW⟩ := ih u hu (by omega) hun (by omega)
      refine ⟨(x : Int) :: C, Chain.step _ _ (by omega) ?_, ?_⟩
      · have : Cpp.get par (x : Int) = (u : Int) := hpu
        rw [this]; exact hC
      · obtain ⟨rest, rfl, _⟩ := chain_cons hC (by omega)
        rw [hdc]
        exact WalkB.cons _ _ _ _ _ hW hc

/-! ## The measure -/

/-- `Σ_{x < k, x ∉ D} (deg x + 1)`. -/
def rest (out : Nat → List (Int × Int)) (D : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rest out D k + if k ∈ D then 0 else (out k).length + 1

theorem rest_step (out : Nat → List (Int × Int)) (D : List Nat) (v : Nat) (hv : v ∉ D) (k : Nat) :
    rest out D k = rest out (D ++ [v]) k + if v < k then (out v).length + 1 else 0 := by
  induction k with
  | zero => simp [rest]
  | succ k ih =>
    simp only [rest, ih]
    by_cases e : k = v
    · subst e; simp [hv]
    · have : (k ∈ D ++ [v]) ↔ k ∈ D := by simp [e]
      by_cases hkD : k ∈ D
      · simp [hkD, e]; split <;> split <;> omega
      · simp [hkD, e]; split <;> split <;> omega

/-- The measure of a state: it decreases by at least 1 in every iteration of the main loop. -/
def meas (n : Nat) (out : Nat → List (Int × Int)) (Q : List (Int × Int)) (D : List Nat) : Nat :=
  Q.length + rest out D n

theorem meas_pop {n : Nat} {out : Nat → List (Int × Int)} {Q Q' : List (Int × Int)} {a : Int × Int} {D : List Nat}
    (hQ : Q.Perm (a :: Q')) : meas n out Q' D + 1 = meas n out Q D := by
  unfold meas; rw [hQ.length_eq]; simp; omega

theorem meas_fresh {n : Nat} {out : Nat → List (Int × Int)} {Q Q' Q'' : List (Int × Int)} {a : Int × Int}
    {D : List Nat} {v : Nat} (hQ : Q.Perm (a :: Q')) (hv : v < n) (hvD : v ∉ D)
    (hlen : Q''.length ≤ Q'.length + (out v).length) : meas n out Q'' (D ++ [v]) + 1 ≤ meas n out Q D := by
  unfold meas
  rw [hQ.length_eq, rest_step out D v hvD n]; simp only [hv, ↓reduceIte]
  simp; omega

/-- The done vertices seen from the state: a finite distance whose pair is not in the queue. -/
theorem mem_D_iff {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q : List (Int × Int)}
    {D : List Nat} {L : Int} (hI : Inv n s U out d par Q D L) {x : Nat} (hx : x < n) :
    x ∈ D ↔ (d[x]! < U ∧ (d[x]!, (x : Int)) ∉ Q) := by
  constructor
  · intro hD
    refine ⟨by have := (hI.dD x hD).2.1; have := hI.Lu; omega, fun hm => ?_⟩
    have := hI.stale x hD _ hm rfl; simp at this
  · intro ⟨h1, h2⟩
    rcases hI.reach x hx h1 with h | h
    · exact h
    · exact absurd h h2

/-- `rest` computed from the state. -/
def restS (U : Int) (out : Nat → List (Int × Int)) (d : Array Int) (Q : List (Int × Int)) : Nat → Nat
  | 0 => 0
  | k + 1 => restS U out d Q k + if d[k]! < U ∧ (d[k]!, (k : Int)) ∉ Q then 0 else (out k).length + 1

theorem rest_eq {n s : Nat} {U : Int} {out : Nat → List (Int × Int)} {d par : Array Int} {Q : List (Int × Int)}
    {D : List Nat} {L : Int} (hI : Inv n s U out d par Q D L) (k : Nat) (hk : k ≤ n) :
    rest out D k = restS U out d Q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rest, restS, ih (by omega)]
    have := mem_D_iff hI (x := k) (by omega)
    by_cases h : k ∈ D
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

end Proofs.ListDijkstraMath
