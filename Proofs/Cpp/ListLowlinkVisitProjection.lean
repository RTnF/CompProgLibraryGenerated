import Proofs.Cpp.ListLowlinkWork
import Proofs.Math.ListLowlinkMultigraph
import Proofs.Math.LowlinkRoot

namespace Proofs.Cpp.ListLowlink

open Proofs.LowlinkInv Proofs.LowlinkRoot Proofs.LowlinkPush Proofs.LowlinkScan Proofs.LowlinkPop
open Proofs.LowlinkMultigraph

/-- The C++ discovery bits, visit numbers and counter represent the DFS machine's visiting order. -/
structure VisitProjection (used : Array Bool) (ord : Array Int) (count : Int) (st : St) : Prop where
  marked : ∀ j : Nat, used[j]! = true ↔ j ∈ st.Vis
  numbered : ∀ j ∈ st.Vis, ord[j]! = st.O j
  counter : count = st.Vis.length

private theorem ordinal_at {n : Nat} {hd tg : Nat → Nat} {st : St} (I : MInv n hd tg st)
    (i : Nat) (hi : i < st.Vis.length) : st.O st.Vis[i] = (i : Int) := by
  have h := I.vis_ord i hi
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h

/-- When the recursion appends freshly visited vertices to the abstract machine's visiting order,
the generated discovery log and its preserved entries transfer the three arrays' invariants. -/
theorem visit_projection_append {n : Nat} {hd tg : Nat → Nat} {st st' : St}
    {used used' : Array Bool} {ord low ord' low' : Array Int} {count count' : Int} {xs : List Nat}
    (A : VisitProjection used ord count st) (I : MInv n hd tg st) (I' : MInv n hd tg st')
    (hvis : st'.Vis = st.Vis ++ xs) (D : Discovery n used used' count count' ord' xs)
    (frame : Cells n used ord low ord' low') :
    VisitProjection used' ord' count' st' := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · rw [D.marked, A.marked, hvis, List.mem_append]
  · intro j hj
    rw [hvis] at hj
    rcases List.mem_append.mp hj with ho | hf
    · obtain ⟨k, hk, hj'⟩ := List.mem_iff_getElem.mp ho
      have hbig : k < st'.Vis.length := by rw [hvis, List.length_append]; omega
      have hj'' : st'.Vis[k] = j := by
        simp only [hvis, List.getElem_append_left hk, hj']
      have hord := ordinal_at I k hk
      have hord' := ordinal_at I' k hbig
      rw [hj'] at hord
      rw [hj''] at hord'
      exact (frame.preserves j ((A.marked j).mpr ho)).1.trans
        ((A.numbered j ho).trans (hord.trans hord'.symm))
    · obtain ⟨k, hk, hj'⟩ := List.mem_iff_getElem.mp hf
      have hbig : st.Vis.length + k < st'.Vis.length := by rw [hvis, List.length_append]; omega
      have hj'' : st'.Vis[st.Vis.length + k] = j := by
        simp only [hvis, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hj']
      have hd := D.numbered k hk
      rw [hj', A.counter] at hd
      have ho := ordinal_at I' (st.Vis.length + k) hbig
      rw [hj'', Int.natCast_add] at ho
      exact hd.trans ho.symm
  · rw [D.counter, A.counter, hvis, List.length_append, Int.natCast_add]


/-- Both ways to enter a DFS frame change the visit arrays the same way. -/
theorem visit_projection_enter {n v : Nat} {hd tg : Nat → Nat} {st st' : St}
    {used : Array Bool} {ord : Array Int} {count : Int}
    (A : VisitProjection used ord count st) (I : MInv n hd tg st) (I' : MInv n hd tg st')
    (hvis : st'.Vis = st.Vis ++ [v]) (hv : v < n) (hu : used.size = n) (ho : ord.size = n)
    (hnew : used[v]! = false) :
    VisitProjection (set used v true) (set ord v count) (count + 1) st' := by
  apply visit_projection_append A I I' hvis (Discovery.single n v used count ord hv hu ho hnew)
  exact Cells.enter n v used ord ord count count hv hnew ho ho

theorem enter_root {n v : Nat} {hd tg : Nat → Nat} {st : St}
    {used : Array Bool} {ord : Array Int} {count : Int}
    (G : GH n hd tg) (I : MInv n hd tg st) (A : VisitProjection used ord count st)
    (hsp : st.sp = 0) (hv : v < n) (hu : used.size = n) (ho : ord.size = n)
    (hnew : used[v]! = false) :
    MInv n hd tg (rootS hd st v) ∧
      VisitProjection (set used v true) (set ord v count) (count + 1) (rootS hd st v) := by
  have hvVis : v ∉ st.Vis := by rw [← A.marked v, hnew]; decide
  have hord : st.O v < 0 := by rw [I.unv_ord v hvVis]; decide
  have inv := inv_root G I hsp hv hord
  exact ⟨inv, visit_projection_enter A I inv rfl hv hu ho hnew⟩

theorem enter_child {n v w q : Nat} {hd tg : Nat → Nat} {st : St}
    {used : Array Bool} {ord : Array Int} {count : Int}
    (G : GH n hd tg) (I : MInv n hd tg st) (A : VisitProjection used ord count st)
    (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (hq : (q : Int) = st.It v) (hit : (q : Int) < (hd (v + 1) : Int)) (hw : tg q = w)
    (hu : used.size = n) (ho : ord.size = n) (hnew : used[w]! = false) :
    MInv n hd tg (pushS hd st v w) ∧
      VisitProjection (set used w true) (set ord w count) (count + 1) (pushS hd st v w) := by
  have hseen := (I.sk_mem (st.sp - 1) (by omega)).1
  rw [htop] at hseen
  have hbase := (I.it_rng v hseen).1
  have hvw : AdjH hd tg v w := ⟨q, by omega, by omega, hw⟩
  have hwn := (G.adj_lt _ _ hvw).2
  have hwVis : w ∉ st.Vis := by rw [← A.marked w, hnew]; decide
  have horder : st.O w < 0 := by rw [I.unv_ord w hwVis]; decide
  have inv := inv_push G I hsp htop hq hit hw horder
  exact ⟨inv, visit_projection_enter A I inv rfl hwn hu ho hnew⟩


def advanceVisited (st : St) (v w : Nat) : St :=
  if v = w then st else scanS st v (scanProjected st v w)

theorem advance_visited_inv {n v w : Nat} {hd tg : Nat → Nat} {st : St}
    {used : Array Bool} {ord : Array Int} {count : Int}
    (I : MInv n hd tg st) (A : VisitProjection used ord count st)
    (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v) (hw : used[w]! = true)
    (hnext : v ≠ w → ∃ q : Nat, (q : Int) = st.It v ∧ (q : Int) < (hd (v + 1) : Int) ∧ tg q = w) :
    MInv n hd tg (advanceVisited st v w) ∧ VisitProjection used ord count (advanceVisited st v w) := by
  by_cases he : v = w
  · simpa [advanceVisited, he] using And.intro I A
  · obtain ⟨q, hq, hlt, hs⟩ := hnext he
    simp only [advanceVisited, he, ite_false]
    exact ⟨scan_projected_inv I hsp htop hq hlt hs ((A.marked w).mp hw), ⟨A.marked, A.numbered, A.counter⟩⟩

theorem pop_projection {n v : Nat} {hd tg : Nat → Nat} {st : St}
    {used : Array Bool} {ord : Array Int} {count : Int}
    (I : MInv n hd tg st) (A : VisitProjection used ord count st)
    (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (hcursor : st.It v = (hd (v + 1) : Int)) :
    MInv n hd tg (popS st v) ∧ VisitProjection used ord count (popS st v) :=
  ⟨inv_pop I hsp htop hcursor, ⟨A.marked, A.numbered, A.counter⟩⟩

/-- The low and reverse-edge flag after reading a visited endpoint agree with the projected
scan. Loops preserve the abstract cursor and the low. -/
theorem advance_visited_low {n v w : Nat} {hd tg : Nat → Nat} {st : St}
    {used : Array Bool} {order : Array Int} {count : Int}
    (I : MInv n hd tg st) (A : VisitProjection used order count st)
    (hv : used[v]! = true) (hw : used[w]! = true)
    (before : List Int) (flag : Bool)
    (hflag : flag = decide (0 < before.count (st.P v))) :
    let p := st.P v
    let parentOrd := st.O p.toNat
    let realLow := effectiveLow (st.L v) (if 2 ≤ before.count p then some parentOrd else none)
    let skip := decide ((w : Int) = p) && !flag
    let after := before ++ [(w : Int)]
    (if skip then (true, realLow) else (flag, min realLow order[w]!)) =
      (decide (0 < after.count p),
        effectiveLow ((advanceVisited st v w).L v)
          (if 2 ≤ after.count p then some parentOrd else none)) := by
  have hvV := (A.marked v).mp hv
  have hright : (advanceVisited st v w).L v =
      if (w : Int) = st.P v ∨ (w : Int) = (v : Int) then st.L v else min (st.L v) order[w]! := by
    have ho := A.numbered w ((A.marked w).mp hw)
    by_cases he : v = w
    · subst w
      simp [advanceVisited]
    · have hwv : (w : Int) ≠ (v : Int) := by omega
      by_cases hpar : (w : Int) = st.P v
      · simp only [advanceVisited, he, ite_false, scanS, scanProjected,
          ite_eq_left hpar.symm, ite_eq_left (Or.inl hpar)]
      · simp only [advanceVisited, he, hwv, scanS, scanProjected, hpar, Ne.symm hpar,
          ite_false, false_or, upd_same, ho]
  have hpv : st.P v ≠ (v : Int) := fun h => (Int.lt_irrefl _) ((I.par_ok v v h).2.2)
  have hand := visited_edge_step (v : Int) (st.P v) (w : Int) (st.L v) (st.O (st.P v).toNat)
    order[w]! before flag hflag hpv (fun h => by
      have he : (st.P v).toNat = w := by rw [← h]; simp
      rw [he]
      exact A.numbered w ((A.marked w).mp hw))
    (fun h => by
      have he : w = v := by omega
      subst w
      rw [A.numbered v hvV]
      exact (I.low_le v hvV).2)
  simpa only [hright] using hand


/-- When a child returns, the generated caller updates the same parent low and separating-child
test as the projected pop. The extra copies of the parent arc affect only the bridge test. -/
theorem pop_child_values {n p v : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hpar : st.P v = (p : Int))
    (parentCap : Option Int) (parallel : Bool) :
    let childLow := effectiveLow (st.L v) (if parallel then some (st.O p) else none)
    let after := popS st v
    effectiveLow (after.L p) parentCap = min (effectiveLow (st.L p) parentCap) childLow ∧
      after.Sp p = st.Sp p + (if st.O p ≤ childLow then 1 else 0) ∧
      after.L v = st.L v ∧ after.Sp v = st.Sp v ∧
      (st.O p < childLow ↔ parallel = false ∧ st.O p < after.L v) := by
  obtain ⟨hp, _, horder⟩ := I.par_ok p v hpar
  have hdiff : st.P v ≠ (v : Int) := by
    intro he
    rw [hpar] at he
    have h : p = v := by omega
    subst p
    exact (Int.lt_irrefl _) horder
  obtain ⟨hlow, hsep, hbridge⟩ := effective_return (st.O p) (st.L p) (st.L v) parentCap parallel (I.low_le p hp).2
  simp only [popS, ite_eq_left hpar, ite_eq_right hdiff]
  exact ⟨hlow.symm, by simp [hsep], trivial, trivial, hbridge⟩


/-- Once a DFS frame has returned, its values used by the output predicates are immutable. -/
def PreservesFinished (before after : St) : Prop :=
  ∀ x : Nat, 0 ≤ before.Fi x →
    after.O x = before.O x ∧ after.L x = before.L x ∧ after.P x = before.P x ∧
      after.Sp x = before.Sp x ∧ after.Fi x = before.Fi x

theorem PreservesFinished.trans {a b c : St}
    (ab : PreservesFinished a b) (bc : PreservesFinished b c) : PreservesFinished a c := by
  intro x hx
  obtain ⟨ho, hl, hp, hs, hf⟩ := ab x hx
  obtain ⟨ho', hl', hp', hs', hf'⟩ := bc x (by rwa [hf])
  exact ⟨ho'.trans ho, hl'.trans hl, hp'.trans hp, hs'.trans hs, hf'.trans hf⟩

theorem root_preserves_finished {n v : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hnew : v ∉ st.Vis) : PreservesFinished st (rootS hd st v) := by
  intro x hx
  have hne : x ≠ v := by
    intro he
    subst x
    rw [I.fin_unv v hnew] at hx
    omega
  simp [rootS, upd_ne _ _ _ _ hne]

theorem child_preserves_finished {n v w : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hnew : w ∉ st.Vis) : PreservesFinished st (pushS hd st v w) := by
  intro x hx
  have hne : x ≠ w := by
    intro he
    subst x
    rw [I.fin_unv w hnew] at hx
    omega
  simp [pushS, upd_ne _ _ _ _ hne]

theorem scan_preserves_finished {v w : Nat} {st : St} (hv : st.Fi v < 0) :
    PreservesFinished st (advanceVisited st v w) := by
  intro x hx
  have hne : x ≠ v := by intro h; subst x; omega
  unfold advanceVisited
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [scanS, scanProjected]
    split <;> simp [upd_ne _ _ _ _ hne]

theorem pop_preserves_finished {n v : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v) :
    PreservesFinished st (popS st v) := by
  intro x hx
  have hv := (I.sk_mem (st.sp - 1) (by omega)).2
  rw [htop] at hv
  have hne : x ≠ v := by intro h; subst x; omega
  have hpar : st.P v ≠ (x : Int) := by
    intro he
    by_cases hn : st.sp = 1
    · have hz : st.sp - 1 = 0 := by omega
      rw [hz] at htop
      have hr := I.sk_root hsp
      rw [htop, he] at hr
      omega
    · have hstep : st.sp - 2 + 1 = st.sp - 1 := by omega
      have hp := I.sk_par (st.sp - 2) (by omega)
      rw [hstep, htop] at hp
      have hx' : x = st.Sk (st.sp - 2) := by
        unfold Pr at hp
        omega
      have hf := (I.sk_mem (st.sp - 2) (by omega)).2
      rw [hx'] at hx
      omega
  simp [popS, hpar, upd_ne _ _ _ _ hne]

end Proofs.Cpp.ListLowlink
