import Proofs.Cpp.FlowCostPathData

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

def bottleneckStep (adj : Array (Array E)) (source : Int) (parents indices : Array Int)
    (_ : Unit) (st : Int × Int) : M (ForInStep (Int × Int)) := do
  tick
  if !(decide (st.2 ≠ source)) then
    return .done st
  let u := get parents st.2
  let i := get indices st.2
  let c := Field.get (member := "cap") (Value := Int) (get (get adj u) i)
  return .yield (min st.1 c, u)

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

theorem bottleneck_loop (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (b : Pass Int) (s t : Nat)
    (path : List Arc) (route : Path n s t path) (lim : Nat) (enough : path.length < lim)
    (positive : ∀ a ∈ path, 0 < cap a) (parents : ∀ a ∈ path, n.head a ≠ s ∧
      get b.2.1 (n.head a : Int) = (n.tail a : Int) ∧ get b.2.2.1 (n.head a : Int) = (layout.position a : Int))
    (start : Int) (nonzero : 0 < start) (clock : Nat) :
    ∃ flow, (loopFuel lim (start, (t : Int)) (bottleneckStep g.adj (s : Int) b.2.1 b.2.2.1)).run clock =
      some ((flow, (s : Int)), clock + path.length + 1) ∧
      0 < flow ∧ flow ≤ start ∧ (∀ a ∈ path, flow ≤ cap a) ∧
      (∀ amount ≤ start, (∀ a ∈ path, amount ≤ cap a) → amount ≤ flow) := by
  induction lim generalizing start t path clock with
  | zero => omega
  | succ lim ih =>
    by_cases empty : path = []
    · have endAtRoot := route.eq_of_empty empty
      subst t
      refine ⟨start, ?_, nonzero, le_rfl, ?_, ?_⟩
      · rw [loopFuel]
        unfold bottleneckStep
        simp only [empty, List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false, decide_false, Bool.not_false, ite_true]
        rfl
      · simp [empty]
      · intro amount h _
        exact h
    · obtain ⟨front, last, pathEq, prefixRoute, dest⟩ := route.split_last empty
      have member : last ∈ path := by simp [pathEq]
      obtain ⟨notSource, row, idx⟩ := parents last member
      have castNe : (t : Int) ≠ (s : Int) := by omega
      have sm : front.length < lim := by simp [pathEq] at enough; omega
      have sub : front ⊆ path := by rw [pathEq]; exact List.subset_append_left _ _
      have pos := positive last member
      obtain ⟨flow, rest, flowPos, fromMin, each, maxFlow⟩ := ih (n.tail last) front prefixRoute sm
        (fun a ha => positive a (sub ha)) (fun a ha => parents a (sub ha)) (min start (cap last))
        (lt_min nonzero pos) (clock + 1)
      refine ⟨flow, ?_, flowPos, le_trans fromMin (min_le_left ..), ?_, ?_⟩
      · have step : (bottleneckStep g.adj (s : Int) b.2.1 b.2.2.1 () (start, (t : Int))).run clock =
            some (.yield (min start (cap last), (n.tail last : Int)), clock + 1) := by
          unfold bottleneckStep
          have hc : Field.get (member := "cap") (Value := Int)
              (get (get g.adj (get b.2.1 (t : Int))) (get b.2.2.1 (t : Int))) = cap last := by
            rw [dest] at row idx
            rw [row, idx]
            exact layout.cap last
          have skip : ¬ (!decide ((t : Int) ≠ (s : Int))) = true := by
            rw [decide_eq_true castNe]
            decide
          dsimp only
          rw [ite_eq_right skip, hc, show get b.2.1 (t : Int) = (n.tail last : Int) by simpa only [dest] using row]
          rfl
        rw [loopFuel, StateT.run_bind, step]
        change (loopFuel lim (min start (cap last), (n.tail last : Int))
          (bottleneckStep g.adj (s : Int) b.2.1 b.2.2.1)).run (clock + 1) = _
        rw [rest, pathEq, List.length_append]
        simp only [List.length_cons, List.length_nil]
        congr 2
        omega
      · intro a ha
        rw [pathEq, List.mem_append] at ha
        rcases ha with ha | ha
        · exact each a ha
        · obtain rfl : a = last := by simpa using ha
          exact le_trans fromMin (min_le_right ..)
      · intro amount minStart all
        exact maxFlow amount (le_min minStart (all last member)) (fun a ha => all a (sub ha))

end Proofs.Cpp.FlowCostSearch
