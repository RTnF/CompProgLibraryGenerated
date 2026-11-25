import Proofs.Math.LowlinkFinal
import Proofs.Math.LowlinkScan

namespace Proofs.LowlinkMultigraph

open Proofs.PrimMath (Rtc)
open Proofs.LowlinkGraph
open Proofs.LowlinkGraph.LlFinal (EV)

abbrev Edge := Nat × Nat

/-- Each occurrence represents one undirected edge, regardless of its orientation in the input. -/
def Adj (edges : List Edge) (a b : Nat) : Prop := (a, b) ∈ edges ∨ (b, a) ∈ edges

def Simple (edges : List Edge) (a b : Nat) : Prop := a ≠ b ∧ Adj edges a b

def copies (edges : List Edge) (u v : Nat) : Nat :=
  edges.countP (fun e => decide (e = (u, v) ∨ e = (v, u)))

theorem copies_pos (edges : List Edge) (u v : Nat) : 0 < copies edges u v ↔ Adj edges u v := by
  rw [copies, List.countP_pos_iff]
  constructor
  · rintro ⟨e, he, h⟩
    rcases of_decide_eq_true h with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · intro h
    rcases h with hl | hr
    · exact ⟨(u, v), hl, by simp⟩
    · exact ⟨(v, u), hr, by simp⟩

theorem copies_parallel (before after : List Edge) (u v : Nat) :
    2 ≤ copies (before ++ (u, v) :: after) u v ↔ Adj (before ++ after) u v := by
  rw [← copies_pos]
  unfold copies
  simp only [List.countP_append, List.countP_cons, true_or, decide_true, ite_true]
  omega

theorem copies_swap (edges : List Edge) (u v : Nat) : copies edges u v = copies edges v u := by
  simp [copies, or_comm]

theorem rtc_drop_loops {R S : Nat → Nat → Prop}
    (h : ∀ a b, a ≠ b → (R a b ↔ S a b)) {a b : Nat} :
    Rtc R a b ↔ Rtc S a b := by
  have go : ∀ {R S : Nat → Nat → Prop}, (∀ a b, a ≠ b → R a b → S a b) →
      Rtc R a b → Rtc S a b := by
    intro R S step path
    induction path with
    | refl => exact Rtc.refl _
    | @tail x y _ last ih =>
      by_cases hxy : x = y
      · subst y; exact ih
      · exact Rtc.tail ih (step x y hxy last)
  exact ⟨go (fun x y hxy => (h x y hxy).mp), go (fun x y hxy => (h x y hxy).mpr)⟩

theorem rtc_simple (edges : List Edge) (a b : Nat) :
    Rtc (Simple edges) a b ↔ Rtc (Adj edges) a b :=
  rtc_drop_loops (fun _ _ hne => by simp [Simple, hne])

theorem rtc_delete_vertex (edges : List Edge) (v a b : Nat) :
    Rtc (EV (Simple edges) v) a b ↔ Rtc (EV (Adj edges) v) a b :=
  rtc_drop_loops (fun _ _ hne => by simp [EV, Simple, hne])

/-- Consider two other neighbours after removing `v`. A loop at `v` does not count as a neighbour. -/
theorem articulation_iff {edges : List Edge} {n : Nat} {par : Nat → Option Nat}
    {ord low fin sep : Nat → Nat} (L : LlFinal n (Simple edges) par ord low fin sep)
    {v : Nat} (hv : v < n) :
    Art par sep v ↔ ∃ a b, v ≠ a ∧ v ≠ b ∧ Adj edges v a ∧ Adj edges v b ∧
      ¬ Rtc (EV (Adj edges) v) a b := by
  rw [L.art_iff hv]
  constructor
  · rintro ⟨a, b, ⟨ha, hea⟩, ⟨hb, heb⟩, hcut⟩
    exact ⟨a, b, ha, hb, hea, heb, fun path => hcut ((rtc_delete_vertex edges v a b).mpr path)⟩
  · rintro ⟨a, b, ha, hb, hea, heb, hcut⟩
    exact ⟨a, b, ⟨ha, hea⟩, ⟨hb, heb⟩, fun path => hcut ((rtc_delete_vertex edges v a b).mp path)⟩

/-- If no other copy remains after removing one occurrence, the remaining graph is the simple projection
with that endpoint pair deleted, up to self-loops. -/
theorem rtc_delete_unique (before after : List Edge) (p v a b : Nat)
    (hunique : ¬ Adj (before ++ after) p v) :
    Rtc (Adj (before ++ after)) a b ↔
      Rtc (LlFinal.EB (Simple (before ++ (p, v) :: after)) p v) a b := by
  apply rtc_drop_loops
  intro x y hxy
  simp only [LlFinal.EB, Simple]
  have moved : Adj (before ++ (p, v) :: after) x y ↔
      Adj (before ++ after) x y ∨ ((x = p ∧ y = v) ∨ (x = v ∧ y = p)) := by
    simp only [Adj, List.mem_append, List.mem_cons, Prod.mk.injEq]
    grind
  rw [moved]
  constructor
  · intro h
    refine ⟨⟨hxy, Or.inl h⟩, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hunique h
    · exact hunique (h.elim Or.inr Or.inl)
  · rintro ⟨⟨_, h | he⟩, hn⟩
    · exact h
    · exact False.elim (hn he)

/-- A tree edge occurrence is a bridge exactly when its endpoint pair is a bridge in the simple projection
and no other occurrence remains. This includes parallel edges listed in reverse orientation. -/
theorem bridge_iff {n : Nat} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}
    (before after : List Edge) (p v : Nat)
    (L : LlFinal n (Simple (before ++ (p, v) :: after)) par ord low fin sep)
    (hp : par v = some p) :
    ¬ Rtc (Adj (before ++ after)) p v ↔
      low v = ord v ∧ ¬ Adj (before ++ after) p v := by
  constructor
  · intro hcut
    have hsingle : ¬ Adj (before ++ after) p v := fun h => hcut (Rtc.single h)
    exact ⟨(L.bridge_iff v p hp).mpr (fun path =>
      hcut ((rtc_delete_unique before after p v p v hsingle).mpr path)), hsingle⟩
  · rintro ⟨hlo, hsingle⟩ path
    exact (L.bridge_iff v p hp).mp hlo ((rtc_delete_unique before after p v p v hsingle).mp path)

theorem non_tree_path {n : Nat} {adj : Nat → Nat → Prop} {par : Nat → Option Nat}
    {ord low fin sep : Nat → Nat} (L : LlFinal n adj par ord low fin sep) {u v : Nat}
    (edge : adj u v) (hu : par u ≠ some v) (hv : par v ≠ some u) :
    Rtc (LlFinal.EB adj u v) u v := by
  have step : ∀ a b, PR par a b → LlFinal.EB adj u v a b := by
    intro a b hab
    refine ⟨(L.par_lt b a hab).2.2.1, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hv hab
    · exact hu hab
  have hlt := L.adj_lt u v edge
  have hne : ord u ≠ ord v := fun h => L.adj_irrefl u (L.ord_inj u v hlt.1 hlt.2 h ▸ edge)
  by_cases hor : ord u < ord v
  · exact Rtc.mono step (L.anc_of_adj (L.adj_sym u v edge) hor)
  · exact Rtc.symm (L.EB_symm u v) (Rtc.mono step (L.anc_of_adj edge (by omega)))

/-- If a child can reach an earlier vertex by a back edge, that vertex is its parent or an ancestor of
its parent. This relates the DFS comparison with the parent's order to the projected bridge theorem. -/
theorem parent_order_lt_low {n : Nat} {adj : Nat → Nat → Prop} {par : Nat → Option Nat}
    {ord low fin sep : Nat → Nat} (L : LlFinal n adj par ord low fin sep) {p v : Nat}
    (hp : par v = some p) : ord p < low v ↔ low v = ord v := by
  have ht := L.par_lt v p hp
  constructor
  · intro hlt
    rcases L.low_mem v ht.1 with he | ⟨x, w, hx, hadj, _, hw⟩
    · exact he
    by_cases h : low v = ord v
    · exact h
    have hlow := L.low_le v ht.1
    have := L.desc_ord_ll (L.wit_anc hp hx hadj (show ord w < ord v by omega))
    omega
  · intro he
    rw [he]
    exact ht.2.2.2

/-- Classify any removed occurrence, including loops and non-tree edges. -/
theorem occurrence_bridge_iff {n : Nat} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}
    (before after : List Edge) (u v : Nat)
    (L : LlFinal n (Simple (before ++ (u, v) :: after)) par ord low fin sep) :
    ¬ Rtc (Adj (before ++ after)) u v ↔ ¬ Adj (before ++ after) u v ∧
      ((par v = some u ∧ low v = ord v) ∨ (par u = some v ∧ low u = ord u)) := by
  let adj := Simple (before ++ (u, v) :: after)
  have swap : Rtc (LlFinal.EB adj u v) u v ↔ Rtc (LlFinal.EB adj v u) v u := by
    have same : ∀ a b, LlFinal.EB adj u v a b ↔ LlFinal.EB adj v u a b := by
      intro a b
      simp [LlFinal.EB, or_comm]
    exact ⟨fun h => Rtc.symm (L.EB_symm v u) (Rtc.mono (fun a b => (same a b).mp) h),
      fun h => Rtc.symm (L.EB_symm u v) (Rtc.mono (fun a b => (same a b).mpr) h)⟩
  constructor
  · intro hcut
    have hsingle : ¬ Adj (before ++ after) u v := fun h => hcut (Rtc.single h)
    have hproj : ¬ Rtc (LlFinal.EB adj u v) u v :=
      fun path => hcut ((rtc_delete_unique before after u v u v hsingle).mpr path)
    refine ⟨hsingle, ?_⟩
    by_cases hpv : par v = some u
    · exact Or.inl ⟨hpv, (L.bridge_iff v u hpv).mpr hproj⟩
    by_cases hpu : par u = some v
    · exact Or.inr ⟨hpu, (L.bridge_iff u v hpu).mpr (fun path => hproj (swap.mpr path))⟩
    have hne : u ≠ v := by
      intro he
      subst v
      exact hcut (Rtc.refl _)
    have he : adj u v := ⟨hne, Or.inl (by simp)⟩
    exact False.elim (hproj (non_tree_path L he hpu hpv))
  · rintro ⟨hsingle, h | h⟩ path
    · exact ((bridge_iff before after u v L h.1).mpr ⟨h.2, hsingle⟩) path
    · apply (L.bridge_iff u v h.1).mp h.2
      exact swap.mp ((rtc_delete_unique before after u v u v hsingle).mp path)

/-- Express the articulation predicate in terms of the two tests used by recursive DFS.
A root needs two children. An internal vertex needs one child whose low is at least its order. -/
theorem articulation_tests {n : Nat} {adj : Nat → Nat → Prop} {par : Nat → Option Nat}
    {ord low fin sep : Nat → Nat} (L : LlFinal n adj par ord low fin sep) {v : Nat} (hv : v < n) :
    Art par sep v ↔
      (par v = none ∧ ∃ a b, a ≠ b ∧ par a = some v ∧ par b = some v) ∨
      (par v ≠ none ∧ ∃ a, par a = some v ∧ ord v ≤ low a) := by
  constructor
  · rintro (⟨hr, htwo⟩ | ⟨hnr, hone⟩)
    · obtain ⟨a, b, hne, ha, hb⟩ := L.sep_two hv htwo
      exact Or.inl ⟨hr, a, b, hne, ha.1, hb.1⟩
    · exact Or.inr ⟨hnr, L.sep_pos hv hone⟩
  · rintro (⟨hr, a, b, hne, ha, hb⟩ | ⟨hnr, a, ha, hlow⟩)
    · exact Or.inl ⟨hr, L.sep_ge_two hv hne ⟨ha, L.root_child_low hr ha⟩ ⟨hb, L.root_child_low hr hb⟩⟩
    · refine Or.inr ⟨hnr, ?_⟩
      rw [L.sep_eq v hv]
      exact List.length_pos_of_mem ((LlFinal.mem_cntL n par ord low v a).mpr
        ⟨(L.par_lt a v ha).1, ha, hlow⟩)

/-- An extra copy of the incoming edge caps the low value at the parent's order.
The projected low value is computed with all edges to the parent excluded. -/
def effectiveLow (projected : Int) (cap : Option Int) : Int :=
  match cap with
  | none => projected
  | some parentOrd => min projected parentOrd

theorem effective_update (projected order : Int) (cap : Option Int) :
    min (effectiveLow projected cap) order = effectiveLow (min projected order) cap := by
  cases cap <;> simp [effectiveLow] <;> omega

theorem effective_loop (projected order : Int) (cap : Option Int) (hle : projected ≤ order) :
    min (effectiveLow projected cap) order = effectiveLow projected cap := by
  rw [effective_update]
  simp [Int.min_eq_left hle]

/-- At a recursive return, parallel edges entering the child affect only the bridge test. The
parent's own cap, if it has one, is preserved during the low update. -/
theorem effective_return (parentOrd parentLow childLow : Int) (parentCap : Option Int)
    (childParallel : Bool) (hle : parentLow ≤ parentOrd) :
    let child := effectiveLow childLow (if childParallel then some parentOrd else none)
    min (effectiveLow parentLow parentCap) child = effectiveLow (min parentLow childLow) parentCap ∧
      (parentOrd ≤ child ↔ parentOrd ≤ childLow) ∧
      (parentOrd < child ↔ childParallel = false ∧ parentOrd < childLow) := by
  cases parentCap <;> cases childParallel <;> simp [effectiveLow] <;> omega

/-- Scan a previously visited neighbour. The real and projected lows agree after applying the cap
from the number of occurrences of the parent's endpoint already scanned in this row. -/
theorem effective_scan (v p w projected parentOrd edgeOrd : Int) (seenCopies : Nat) (hpv : p ≠ v)
    (hp : w = p → edgeOrd = parentOrd) (hv : w = v → projected ≤ edgeOrd) :
    let old := effectiveLow projected (if 2 ≤ seenCopies then some parentOrd else none)
    let scanned := if w = p ∧ seenCopies = 0 then old else min old edgeOrd
    let projected' := if w = p ∨ w = v then projected else min projected edgeOrd
    let count' := seenCopies + if w = p then 1 else 0
    scanned = effectiveLow projected' (if 2 ≤ count' then some parentOrd else none) := by
  by_cases hwp : w = p
  · subst w
    rw [hp rfl]
    simp only [true_or, true_and, ite_true]
    by_cases hzero : seenCopies = 0
    · subst seenCopies
      rfl
    · have htw : 2 ≤ seenCopies + 1 := by omega
      by_cases hprev : 2 ≤ seenCopies <;> simp [hzero, htw, hprev, effectiveLow] <;> omega
  · by_cases hwv : w = v
    · simpa [Ne.symm hpv, hwv] using effective_loop projected edgeOrd
        (if 2 ≤ seenCopies then some parentOrd else none) (hv hwv)
    · simpa [hwp, hwv] using effective_update projected edgeOrd
        (if 2 ≤ seenCopies then some parentOrd else none)

/-- The C++ flag records whether a reverse tree edge has already been skipped. Advancing the row
preserves this representation and the corresponding low value together. -/
theorem visited_edge_step (v p w projected parentOrd edgeOrd : Int) (before : List Int)
    (skipped : Bool) (hskipped : skipped = decide (0 < before.count p)) (hpv : p ≠ v)
    (hp : w = p → edgeOrd = parentOrd) (hv : w = v → projected ≤ edgeOrd) :
    let old := effectiveLow projected (if 2 ≤ before.count p then some parentOrd else none)
    let skip := decide (w = p) && !skipped
    let after := before ++ [w]
    (if skip then (true, old) else (skipped, min old edgeOrd)) =
      (decide (0 < after.count p),
        effectiveLow (if w = p ∨ w = v then projected else min projected edgeOrd)
          (if 2 ≤ after.count p then some parentOrd else none)) := by
  have hcount : (before ++ [w]).count p = before.count p + if w = p then 1 else 0 := by
    by_cases h : w = p <;> simp [List.count_append, h]
  have hskip : (decide (w = p) && !skipped) = true ↔ w = p ∧ before.count p = 0 := by
    rw [hskipped]
    simp [List.count_eq_zero]
  simp only [hcount, hskip]
  by_cases h : w = p
  · have hpos : 0 < before.count p + 1 := by omega
    by_cases hnone : before.count p = 0
    · simp [h, hnone]
    · have hpos' : 0 < before.count p := by omega
      have he := effective_scan v p w projected parentOrd edgeOrd (before.count p) hpv hp hv
      simpa [h, hnone, hpos, hskipped, hpos'] using he
  · have he := effective_scan v p w projected parentOrd edgeOrd (before.count p) hpv hp hv
    simp only [h, false_and, ite_false, Nat.add_zero] at he ⊢
    rw [hskipped, he]

/-- The local state of the incoming-edge scan: whether its first copy was skipped, and the low value. -/
def parentStep (parent parentOrd : Nat) (state : Bool × Nat) (target : Nat) : Bool × Nat :=
  if target = parent then
    (true, if state.1 then min state.2 parentOrd else state.2)
  else
    state

/-- A fresh row skips exactly one matching edge. With a previously skipped copy,
every further matching edge is processed. -/
theorem parent_scan (targets : List Nat) (parent parentOrd : Nat) (skipped : Bool) (low : Nat) :
    targets.foldl (parentStep parent parentOrd) (skipped, low) =
      (skipped || decide (0 < targets.count parent),
        if (if skipped then 1 else 2) ≤ targets.count parent then min low parentOrd else low) := by
  induction targets generalizing skipped low with
  | nil => cases skipped <;> simp
  | cons target rest ih =>
    by_cases h : target = parent
    · subst target
      cases skipped <;> simp only [List.foldl_cons, parentStep, Bool.false_eq_true,
        ↓reduceIte, List.count_cons_self, ih, Bool.false_or, Bool.true_or]
      · have hpos : 0 < rest.count parent + 1 := by omega
        have heq : 2 ≤ rest.count parent + 1 ↔ 1 ≤ rest.count parent := by omega
        simp [hpos, heq]
      · have hpos : 1 ≤ rest.count parent + 1 := by omega
        simp only [hpos, ↓reduceIte]
        split <;> congr 1 <;> omega
    · have countEq : (target :: rest).count parent = rest.count parent := by
        simp [h]
      rw [countEq, List.foldl_cons]
      simpa [parentStep, h] using ih skipped low

section Rows

open Proofs.LowlinkInv (AdjH GH)

/-- The proof's CSR view keeps the input order and all parallel arcs, and omits loops.
The C++ traversal still reads the original rows. -/
def rows (n : Nat) (targets : Nat → List Nat) : List (List Nat) :=
  (List.range n).map (fun v => (targets v).filter (fun w => decide (w ≠ v)))

def offsets (rs : List (List Nat)) (v : Nat) : Nat := ((rs.take v).flatten).length
def endpoints (rs : List (List Nat)) (i : Nat) : Nat := (rs.flatten[i]?).getD 0

theorem row_get (n : Nat) (targets : Nat → List Nat) (v : Nat) (hv : v < n) :
    (rows n targets)[v]'(by simpa [rows] using hv) =
      (targets v).filter (fun w => decide (w ≠ v)) := by
  simp [rows]

theorem offsets_succ (rs : List (List Nat)) (v : Nat) (h : v < rs.length) :
    offsets rs (v + 1) = offsets rs v + rs[v].length := by
  unfold offsets
  rw [List.take_succ_eq_append_getElem h, List.flatten_append, List.length_append]
  simp

theorem endpoint_get (rs : List (List Nat)) (v i : Nat) (hv : v < rs.length)
    (hi : i < rs[v].length) :
    endpoints rs (offsets rs v + i) = rs[v][i] := by
  have ht : rs.take (v + 1) ++ rs.drop (v + 1) = rs := List.take_append_drop _ _
  rw [List.take_succ_eq_append_getElem hv, List.append_assoc] at ht
  have hf : rs.flatten = (rs.take v).flatten ++ (rs[v] ++ (rs.drop (v + 1)).flatten) := by
    simpa only [List.flatten_append, List.singleton_append, List.flatten_cons] using
      (congrArg List.flatten ht).symm
  unfold endpoints
  rw [hf, List.getElem?_append_right (by simp [offsets])]
  simp only [offsets, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  rfl

/-- The next non-loop in the C++ row is the next unscanned arc in the projected CSR row.
The two cursors differ by the number of loops already passed. -/
theorem row_cursor (n : Nat) (targets : Nat → List Nat) (v w : Nat) (hv : v < n)
    (before after : List Nat) (split : targets v = before ++ w :: after) (hne : w ≠ v) :
    let rs := rows n targets
    let q := offsets rs v + (before.filter (fun t => decide (t ≠ v))).length
    q < offsets rs (v + 1) ∧ endpoints rs q = w := by
  have hrow : v < (rows n targets).length := by simpa [rows] using hv
  have hlist := row_get n targets v hv
  rw [split] at hlist
  simp only [List.filter_append, List.filter_cons, decide_eq_true hne, ite_true] at hlist
  let before' := before.filter (fun t => decide (t ≠ v))
  let after' := after.filter (fun t => decide (t ≠ v))
  change (rows n targets)[v] = before' ++ w :: after' at hlist
  have hi : before'.length < (rows n targets)[v].length := by rw [hlist]; simp
  change offsets (rows n targets) v + before'.length < offsets (rows n targets) (v + 1) ∧
    endpoints (rows n targets) (offsets (rows n targets) v + before'.length) = w
  constructor
  · rw [offsets_succ _ _ hrow]
    omega
  · rw [endpoint_get _ _ _ hrow hi]
    have hx : (rows n targets)[v][before'.length]? = some w := by
      rw [hlist, List.getElem?_append_right (Nat.le_refl _)]
      simp
    simpa [List.getElem?_eq_getElem hi] using hx

theorem adj_rows (rs : List (List Nat)) (v w : Nat) :
    AdjH (offsets rs) (endpoints rs) v w ↔ ∃ hv : v < rs.length, w ∈ rs[v] := by
  by_cases hv : v < rs.length
  · simp only [AdjH, offsets_succ rs v hv]
    constructor
    · rintro ⟨i, hlo, hhi, he⟩
      let j := i - offsets rs v
      have hj : j < rs[v].length := by omega
      have hidx : i = offsets rs v + j := by omega
      refine ⟨hv, List.mem_iff_getElem.mpr ⟨j, hj, ?_⟩⟩
      rwa [hidx, endpoint_get rs v j hv hj] at he
    · rintro ⟨_, hw⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
      exact ⟨offsets rs v + j, by omega, by omega, endpoint_get rs v j hv hj⟩
  · have hin : rs.length ≤ v := by omega
    have hflat : offsets rs (v + 1) = offsets rs v := by
      simp [offsets, List.take_of_length_le hin, List.take_of_length_le (show rs.length ≤ v + 1 by omega)]
    constructor
    · rintro ⟨q, hlo, hhi, _⟩
      rw [hflat] at hhi
      omega
    · rintro ⟨hin, _⟩
      exact False.elim (hv hin)

theorem adj_view (n : Nat) (targets : Nat → List Nat) (v w : Nat) :
    AdjH (offsets (rows n targets)) (endpoints (rows n targets)) v w ↔
      v < n ∧ w ∈ targets v ∧ w ≠ v := by
  rw [adj_rows]
  constructor
  · rintro ⟨hv, hw⟩
    have hv' : v < n := by simpa [rows] using hv
    exact ⟨hv', by simpa [row_get n targets v hv'] using hw⟩
  · rintro ⟨hv, hw, hne⟩
    exact ⟨by simpa [rows] using hv, by simpa [row_get n targets v hv] using And.intro hw hne⟩

/-- A symmetric adjacency list represents the same graph as its CSR view.
Symmetry here concerns reachability, so duplicate arcs can remain in the rows. -/
theorem graph_view (edges : List Edge) (n : Nat) (targets : Nat → List Nat)
    (hmem : ∀ v w, v ≠ w → ((v < n ∧ w ∈ targets v) ↔ Adj edges v w))
    (hrange : ∀ v w, Adj edges v w → w < n) :
    GH n (offsets (rows n targets)) (endpoints (rows n targets)) ∧
      ∀ v w, AdjH (offsets (rows n targets)) (endpoints (rows n targets)) v w ↔ Simple edges v w := by
  have view : ∀ v w, AdjH (offsets (rows n targets)) (endpoints (rows n targets)) v w ↔
      Simple edges v w := by
    intro v w
    rw [adj_view]
    exact ⟨fun ⟨hv, hw, hne⟩ => ⟨Ne.symm hne, (hmem v w (Ne.symm hne)).mp ⟨hv, hw⟩⟩,
      fun ⟨hne, he⟩ => ⟨((hmem v w hne).mpr he).1, ((hmem v w hne).mpr he).2, Ne.symm hne⟩⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, view⟩
  · intro v hv
    rw [offsets_succ _ _ (by simpa [rows] using hv)]
    exact Nat.le_add_right _ _
  · intro v w h
    obtain ⟨hne, he⟩ := (view v w).mp h
    exact ⟨((hmem v w hne).mpr he).1, hrange v w he⟩
  · intro v w h
    obtain ⟨hne, he⟩ := (view v w).mp h
    exact (view w v).mpr ⟨Ne.symm hne, he.elim Or.inr Or.inl⟩
  · intro v h
    exact ((view v v).mp h).1 rfl

/-- One copy of each non-loop edge is present in each of its endpoints' rows.
The multiplicities of loops do not affect the projection. -/
structure RowsRepresent (edges : List Edge) (n : Nat) (targets : Nat → List Nat) : Prop where
  range : ∀ v w, Adj edges v w → w < n
  count : ∀ v w, v < n → v ≠ w → (targets v).count w = copies edges v w

theorem RowsRepresent.view {edges : List Edge} {n : Nat} {targets : Nat → List Nat}
    (H : RowsRepresent edges n targets) :
    GH n (offsets (rows n targets)) (endpoints (rows n targets)) ∧
      AdjH (offsets (rows n targets)) (endpoints (rows n targets)) = Simple edges := by
  obtain ⟨G, same⟩ := graph_view edges n targets (fun v w hne => by
    constructor
    · rintro ⟨hv, hm⟩
      rw [← copies_pos, ← H.count v w hv hne]
      exact List.count_pos_iff.mpr hm
    · intro he
      have hv := H.range w v (he.elim Or.inr Or.inl)
      refine ⟨hv, List.count_pos_iff.mp ?_⟩
      rw [H.count v w hv hne]
      exact (copies_pos edges v w).mpr he) H.range
  exact ⟨G, funext fun v => funext fun w => propext (same v w)⟩

theorem RowsRepresent.final {edges : List Edge} {n : Nat} {targets : Nat → List Nat}
    (H : RowsRepresent edges n targets) {st : Proofs.LowlinkInv.St}
    (I : Proofs.LowlinkInv.MInv n (offsets (rows n targets)) (endpoints (rows n targets)) st)
    (hsp : st.sp = 0) (hall : ∀ v, v < n → v ∈ st.Vis) :
    LlFinal n (Simple edges) (Proofs.LowlinkFinal.parO st.P)
      (fun v => (st.O v).toNat) (fun v => (st.L v).toNat) (fun v => (st.Fi v).toNat)
      (fun v => (st.Sp v).toNat) := by
  rw [← H.view.2]
  exact Proofs.LowlinkFinal.final_of_inv H.view.1 I hsp hall

/-- At a final state of the machine, the recursive implementation's bridge test compares the parent's
order with the child's capped low value. It detects deletion of a single occurrence. -/
theorem final_bridge_test (before after : List Edge) (p v n : Nat) (targets : Nat → List Nat)
    (H : RowsRepresent (before ++ (p, v) :: after) n targets) {st : Proofs.LowlinkInv.St}
    (I : Proofs.LowlinkInv.MInv n (offsets (rows n targets)) (endpoints (rows n targets)) st)
    (hsp : st.sp = 0) (hall : ∀ x, x < n → x ∈ st.Vis) (hp : st.P v = (p : Int)) :
    st.O p < effectiveLow (st.L v) (if 2 ≤ (targets v).count p then some (st.O p) else none) ↔
      ¬ Rtc (Adj (before ++ after)) p v := by
  have L := H.final I hsp hall
  have hp' := Proofs.LowlinkFinal.parO_some.mpr hp
  have ht := L.par_lt v p hp'
  have hp0 := (I.ord_lt_len (hall p ht.2.1)).1
  have hv0 := (I.ord_lt_len (hall v ht.1)).1
  have hl0 := (I.low_le v (hall v ht.1)).1
  have hne : v ≠ p := by
    intro he
    subst v
    exact (Nat.lt_irrefl _ ht.2.2.2)
  have hcnt : 2 ≤ (targets v).count p ↔ Adj (before ++ after) p v := by
    rw [H.count v p ht.1 hne, copies_swap _ v p, copies_parallel]
  have hproj : st.O p < st.L v ↔ (st.L v).toNat = (st.O v).toNat := by
    have he : st.O p < st.L v ↔ (st.O p).toNat < (st.L v).toNat := by omega
    exact he.trans (parent_order_lt_low L hp')
  rw [bridge_iff before after p v L hp']
  by_cases hdup : 2 ≤ (targets v).count p
  · have he := hcnt.mp hdup
    simp [hdup, effectiveLow, he, Int.min_le_right]
  · have he := mt hcnt.mpr hdup
    simp [hdup, effectiveLow, he, hproj]

end Rows

section Scan

open Proofs.LowlinkInv Proofs.LowlinkScan

/-- Update the projected low for a scanned arc whose endpoint has already been visited. Edges
to the parent are represented by the separate cap in the real low. -/
def scanProjected (st : St) (v w : Nat) : Nat → Int :=
  if st.P v = (w : Int) then st.L else upd st.L v (min (st.L v) (st.O w))

theorem scan_projected_inv {n : Nat} {hd tg : Nat → Nat} {st : St} (I : MInv n hd tg st)
    {v w q : Nat} (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (hq : (q : Int) = st.It v) (hnext : (q : Int) < (hd (v + 1) : Int))
    (hw : tg q = w) (hseen : w ∈ st.Vis) :
    MInv n hd tg (scanS st v (scanProjected st v w)) := by
  have htop' := I.sk_mem (st.sp - 1) (by omega)
  rw [htop] at htop'
  have hlow := (I.low_le v htop'.1).1
  have hord := (I.ord_lt_len hseen).1
  apply inv_scan I (scanProjected st v w) htop'.1 htop'.2 hq hnext hw hord
  · intro u
    by_cases he : u = v
    · subst u
      simp only [scanProjected]
      split
      · exact Int.le_refl _
      · rw [upd_same]
        exact Int.min_le_left _ _
    · simp only [scanProjected]
      split <;> simp [upd_ne _ _ _ _ he]
  · intro u hu
    simp only [scanProjected]
    split
    · rfl
    · exact upd_ne _ _ _ _ hu
  · simp only [scanProjected]
    split
    · exact hlow
    · rw [upd_same]
      omega
  · by_cases hp : st.P v = (w : Int)
    · exact Or.inl (by simp [scanProjected, hp])
    · simp only [scanProjected, hp, ite_false, upd_same]
      by_cases hel : st.L v ≤ st.O w
      · exact Or.inl (Int.min_eq_left hel)
      · exact Or.inr ⟨hp, Int.min_eq_right (by omega)⟩
  · intro hp
    simp only [scanProjected, hp, ite_false, upd_same]
    exact Int.min_le_right _ _

end Scan

end Proofs.LowlinkMultigraph
