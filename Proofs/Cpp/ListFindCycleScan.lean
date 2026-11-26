import Proofs.Cpp.ListFindCycleWitness

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

abbrev SearchResult (E : Type) := Array Int × Array E × Array E
abbrev RowState (E : Type) := Option (SearchResult E) × SearchResult E

def rowStep (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (edge : E) (s : RowState E) :
    M (ForInStep (RowState E)) := do
  tick
  let visited := s.2.1
  let parents := s.2.2.1
  let cycle := s.2.2.2
  let dest := Field.get (member := "to") edge
  if decide (size cycle ≠ 0) then
    return .done (none, visited, parents, cycle)
  else if !(decide (get visited dest ≠ 0)) then
    let child ← cp.ListGraph.find_cycle_dfs_rec fuel' g dest visited (set parents dest edge) cycle
    return .yield (none, child.1, child.2.1, child.2.2)
  else if decide (get visited dest = 1) then
    tick
    let out ← forIn forever (cycle.push edge, node) (collectStep parents dest)
    tickN out.1.size
    let result := (visited, parents, out.1.reverse)
    return .done (some result, result)
  else
    return .yield (none, visited, parents, cycle)

def finishRow (node : Int) (s : RowState E) : SearchResult E :=
  match s.1 with
  | some r => r
  | none => (set s.2.1 node 2, s.2.2.1, s.2.2.2)

/-- Factor the generated method into the recursive call, the row scan and its two possible exits. -/
theorem dfs_scan (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (visited : Array Int)
    (parents cycle : Array E) :
    cp.ListGraph.find_cycle_dfs_rec (fuel' + 1) g node visited parents cycle = (do
      tick
      let s ← forIn (get g.adj node).toList (none, set visited node 1, parents, cycle) (rowStep g fuel' node)
      return finishRow node s) := by
  rw [cp.ListGraph.find_cycle_dfs_rec]
  dsimp only
  rw [← Array.forIn_toList]
  conv_lhs =>
    enter [2, _, 1, 3, e, s]
    change rowStep g fuel' node e s
  conv_lhs =>
    enter [2, _, 2, s]
    tactic =>
      show _ = (pure (finishRow node s) : M (SearchResult E))
      unfold finishRow
      cases s.1 <;> rfl

private theorem run_tick (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem run_tickN (d t : Nat) : (tickN d).run t = some ((), t + d) := rfl
private theorem run_pure {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

theorem rowStep_found (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (edge : E)
    (s : RowState E) (cycle_found : s.2.2.2.size ≠ 0) (t : Nat) :
    (rowStep g fuel' node edge s).run t = some (.done (none, s.2), t + 1) := by
  have h := (show size s.2.2.2 ≠ 0 by simpa [size] using cycle_found)
  unfold rowStep
  dsimp only
  rw [ite_eq_left (decide_eq_true h)]
  rfl

theorem rowStep_white (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (edge : E)
    (out : Option (SearchResult E)) (visited : Array Int) (parents : Array E)
    (white : get visited (Field.get (member := "to") edge) = 0) (t : Nat) :
    (rowStep g fuel' node edge (out, visited, parents, Array.empty)).run t =
      ((cp.ListGraph.find_cycle_dfs_rec fuel' g (Field.get (member := "to") edge) visited
        (set parents (Field.get (member := "to") edge) edge) Array.empty).run (t + 1)).map
          (fun p => (.yield (none, p.1), p.2)) := by
  unfold rowStep
  dsimp only
  have hempty : size (Array.empty : Array E) = 0 := rfl
  simp only [hempty, white, ne_self_iff_false, decide_false, Bool.false_eq_true, ite_false,
    Bool.not_false, ite_true, StateT.run_bind, run_tick, some_bind, run_pure]
  cases (cp.ListGraph.find_cycle_dfs_rec fuel' g (Field.get (member := "to") edge) visited
    (set parents (Field.get (member := "to") edge) edge) Array.empty).run (t + 1) <;> rfl

theorem rowStep_black (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (edge : E)
    (out : Option (SearchResult E)) (visited : Array Int) (parents : Array E)
    (black : get visited (Field.get (member := "to") edge) = 2) (t : Nat) :
    (rowStep g fuel' node edge (out, visited, parents, Array.empty)).run t =
      some (.yield (none, visited, parents, Array.empty), t + 1) := by
  unfold rowStep
  dsimp only
  have hempty : size (Array.empty : Array E) = 0 := rfl
  simp only [hempty, black, ne_self_iff_false, decide_false, Bool.false_eq_true, ite_false]
  rfl

theorem rowStep_gray (g : cp.ListGraph Cost E) (fuel' : Nat) (edge : E)
    (out : Option (SearchResult E)) (visited : Array Int) (parents : Array E)
    (spine : Nat → Int) (first depth t : Nat)
    (dest_eq : Field.get (member := "to") edge = spine first) (gray : get visited (spine first) = 1)
    (distinct : ∀ d, 0 < d → d ≤ depth → spine (first + d) ≠ spine first)
    (parent_from : ∀ d, d < depth →
      Field.get (member := "from") (get parents (spine (first + (d + 1)))) = spine (first + d))
    (enough : depth < fuel) :
    let result := (visited, parents, (edge :: parentsBack parents spine first depth).toArray.reverse)
    (rowStep g fuel' (spine (first + depth)) edge (out, visited, parents, Array.empty)).run t =
      some (.done (some result, result), t + 4 + 3 * depth) := by
  unfold rowStep
  dsimp only
  have hempty : size (Array.empty : Array E) = 0 := rfl
  have hstay : ¬ (!decide ((1 : Int) ≠ 0)) = true := by decide
  simp only [hempty, ne_self_iff_false, decide_false, Bool.false_eq_true, ite_false, dest_eq, gray,
    hstay, decide_true, ite_true, StateT.run_bind, run_tick, some_bind, run_pure, run_tickN]
  have hcollect : (forIn forever (Array.empty.push edge, spine (first + depth))
        (collectStep parents (spine first))).run (t + 1 + 1) =
      some (([edge].toArray ++ (parentsBack parents spine first depth).toArray, spine first),
        t + 1 + 1 + 2 * depth + 1) :=
    collect_parents parents spine first depth distinct parent_from fuel enough _ _
  rw [hcollect]
  simp only [some_bind, Array.size_append, List.size_toArray, parentsBack_length, List.length_singleton]
  have hclock : t + 1 + 1 + 2 * depth + 1 + (1 + depth) = t + 4 + 3 * depth := by omega
  rw [hclock]
  simp

theorem scan_after_cycle (g : cp.ListGraph Cost E) (fuel' : Nat) (node : Int) (row : List E)
    (s : SearchResult E) (cycle_found : s.2.2.size ≠ 0) (t : Nat) :
    (forIn row (none, s) (rowStep g fuel' node)).run t =
      some ((none, s), t + if row.isEmpty then 0 else 1) := by
  cases row with
  | nil => rfl
  | cons e row =>
    rw [List.forIn_cons, StateT.run_bind, rowStep_found g fuel' node e (none, s) cycle_found]
    rfl

end Proofs.Cpp.ListFindCycle

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListFindCycle

/-- After finding a cycle, later root calls retain the exact edge values and parent array.
They mark their root black without following any edge, and read at most the first arc. -/
theorem retain_cycle {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]
    (fuel : Nat) (g : cp.ListGraph Cost E) (node : Int) (visited : Array Int)
    (parents cycle : Array E) (hc : cycle.size ≠ 0) (t : Nat) :
    (cp.ListGraph.find_cycle_dfs_rec (fuel + 1) g node visited parents cycle).run t =
      some ((set (set visited node 1) node 2, parents, cycle),
        t + 1 + (if (get g.adj node).toList.isEmpty then 0 else 1)) := by
  rw [cp.ListGraph.find_cycle_dfs_rec]
  dsimp only
  rw [← Array.forIn_toList]
  have h := (show (size cycle : Int) ≠ 0 by simpa [size] using hc)
  generalize (get g.adj node).toList = row
  cases row with
  | nil => rfl
  | cons e rest =>
    rw [List.forIn_cons]
    dsimp only
    rw [ite_eq_left (decide_eq_true h)]
    rfl

end Proofs.Cpp.ListFindCycle

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.LowlinkMultigraph (offsets endpoints)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

omit [Inhabited E] in
theorem CycleWitness.positive {g : cp.ListGraph Cost E} {cycle : Array E}
    (w : CycleWitness g cycle.toList) : cycle.size ≠ 0 := by
  obtain ⟨start, path, froms, _, _, _⟩ := w
  have h := congrArg List.length froms
  simp at h
  omega

theorem gray_arc {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E}
    {st : FS} (valid : ValidGraph g)
    (inv : FInv g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) st)
    (v : Nat) (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (active : Active g visited parents st) (edge : E) (he : edge ∈ edgesAt g v)
    (hgray : get visited (Field.get (member := "to") edge) = 1)
    (hfuel : g.adj.size < fuel) (fuel' c : Nat) :
    ∃ (cycle : Array E) (t : Nat),
      (rowStep g fuel' (v : Int) edge (none, visited, parents, Array.empty)).run c =
        some (.done (some (visited, parents, cycle), visited, parents, cycle), t) ∧
      CycleWitness g cycle.toList ∧ t ≤ c + 4 + 3 * g.adj.size := by
  have hv := inv.c_lt v (by have := top_gray inv hsp htop; omega)
  obtain ⟨j, hj, hdest⟩ := active.gray_ancestor valid inv hv he hgray
  let depth := st.sp - 1 - j
  let spine := fun k => (st.Sk k : Int)
  have hidx : j + depth = st.sp - 1 := by omega
  have hv' : spine (j + depth) = (v : Int) := by simp only [spine, hidx, htop]
  have hf (k : Nat) (hk : k < depth) :
      Field.get (member := "from") (get parents (spine (j + (k + 1)))) = spine (j + k) := by
    have h := active.parent_endpoints valid inv (j := j + k) (by omega)
    simpa only [spine, Nat.add_assoc] using h.2.1
  have hne : ∀ k, 0 < k → k ≤ depth → spine (j + k) ≠ spine j := by
    intro k hpos hle heq
    have hs : st.Sk (j + k) = st.Sk j := by simpa [spine] using heq
    have := inv.sk_inj _ _ (by omega) hj hs
    omega
  have hbound := inv.sp_le
  have hdest' : Field.get (member := "to") edge = spine j := hdest.symm
  have hrun := rowStep_gray g fuel' edge none visited parents spine j depth c hdest'
    (by rwa [← hdest']) hne hf (by omega)
  rw [hv'] at hrun
  have hwitness := cycle_witness_of_active active valid inv j depth (by omega) edge
    (by rwa [hidx, htop]) hdest.symm
  exact ⟨_, _, hrun, by simpa using hwitness, by omega⟩

end Proofs.Cpp.ListFindCycle
