import Proofs.Cpp.FlowCostConvergence

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [DecidableEq Arc] [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

private def startLabels (len : Int) (s : Nat) (inf : Int) : Pass Int :=
  (set (replicate len inf) (s : Int) 0, set (replicate len (-1)) (s : Int) (s : Int), replicate len 0, false)

private theorem start_sizes (len : Int) (s : Nat) (inf : Int) : LabelSizes len.toNat (startLabels len s inf) := by
  constructor <;> simp [startLabels, replicate]

private theorem start_parentValue {len : Int} {s : Nat} (hs : s < len.toNat) (inf : Int) (v : Nat) (hv : v < len.toNat) :
    get (startLabels len s inf).2.1 (v : Int) = if v = s then (s : Int) else -1 := by
  change get (set (replicate len (-1)) (s : Int) (s : Int)) (v : Int) = _
  rw [get_natCast, getElemBang_set _ _ _ _ (by simpa [replicate] using hs), Int.toNat_natCast]
  simp [replicate, hv]

private theorem start_sound (n : Network Arc Nat) (cap : Capacity Arc) (atSlot : Int → Int → Option Arc)
    (len : Int) (s : Nat) (hs : s < len.toNat) (inf : Int) : SearchCert n cap s atSlot (startLabels len s inf) := by
  let b := startLabels len s inf
  have hsizes : LabelSizes len.toNat b := start_sizes len s inf
  have knownExactly (v : Nat) : known b v = true ↔ v = s := by
    rw [known_iff, hsizes.parent]
    by_cases hv : v < len.toNat
    · rw [start_parentValue hs inf v hv]
      by_cases h : v = s
      · have hzero : (s : Int) ≠ -1 := by omega
        simp [h, hzero]
        omega
      · simp [h]
    · have ne : v ≠ s := by omega
      simp [hv, ne]
  have rootzero : label b s = 0 := by
    change get (set (replicate len inf) (s : Int) 0) (s : Int) = _
    rw [get_natCast, getElemBang_set _ _ _ _ (by simpa [replicate] using hs), Int.toNat_natCast, ite_eq_left rfl]
  have noSaved (v : Nat) : savedParent atSlot s b v = none := by
    unfold savedParent
    by_cases hv : v < len.toNat
    · rw [start_parentValue hs inf v hv]
      by_cases he : v = s <;> simp [he]
    · rw [hsizes.parent]
      simp [hv]
  have root := (knownExactly s).mpr rfl
  refine ⟨⟨⟨root, rootzero⟩, ?_⟩, fun _ => 0, 1, ?_⟩
  · intro v hv
    obtain rfl : v = s := (knownExactly v).mp hv
    exact ⟨[], .nil _, by simp, rootzero.symm⟩
  · constructor
    · exact root
    · intro v hv _
      obtain rfl : v = s := (knownExactly v).mp hv
      exact ⟨rfl, rootzero⟩
    · intro v a h
      rw [noSaved] at h
      contradiction
    · intro v
      omega

private theorem mem_index (i bound : Nat) (h : i < bound) : (i : Int) ∈ range 0 (bound : Int) := by
  simp only [range, Int.sub_zero, Int.toNat_natCast, Int.zero_add]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

theorem stable_closed (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (b : Pass Int)
    (sizes : LabelSizes g.adj.size b) (stable : Stable g (labelPart b)) :
    ∀ a, 0 < cap a → known b (n.tail a) = true →
      HasLabel (known b) (label b) (n.head a) (label b (n.tail a) + n.cost a) := by
  intro a hp hk
  have v : (n.tail a : Int) ∈ range 0 g.n_ := by rw [layout.graph_size]; exact mem_index _ _ (layout.tailBound a)
  have i : (layout.position a : Int) ∈ range 0 (size (get g.adj (n.tail a : Int))) := mem_index _ _ (layout.positionBound a)
  have before : get (labelPart b).2.1 (n.tail a : Int) ≠ -1 := ((known_iff b _).mp hk).2
  have hf := stable (n.tail a : Int) v before (layout.position a : Int) i
  have bound : n.head a < (clearFlag b).2.1.size := by change n.head a < b.2.1.size; rw [sizes.parent]; exact layout.headBound a
  exact no_relax_projects n cap a (clearFlag b) (arcValue g (n.tail a) (layout.position a))
    (layout.dest a) (layout.cap a) (layout.cost a) bound hf hp

def arcCount (g : cp.FlowGraph Int E) : Nat := (g.adj.toList.map Array.size).sum

private theorem weight_rows (rows : List (Array E)) :
    (rows.map (fun row => 1 + row.size)).sum = rows.length + (rows.map Array.size).sum := by
  induction rows with
  | nil => rfl
  | cons a b ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

private theorem charge (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) : passCharge g = 1 + g.adj.size + arcCount g := by
  have columns := range_map_get g.adj
  unfold passCharge scanCharge arcCount
  rw [layout.graph_size, ← size]
  have hw := congrArg (fun rows : List (Array E) => (rows.map (fun r => 1 + r.size)).sum) columns
  rw [List.map_map, weight_rows, Array.length_toList] at hw
  simp only [Function.comp_def] at hw
  omega

variable [NumericTraits "Cost" Int] [ShiftInt Int]

private abbrev infinity : Int := ShiftInt.shr (NumericTraits.maximum (tag := "Cost") (α := Int)) 2
private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem tickN_run (k t : Nat) : (tickN k).run t = some ((), t + k) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl
private theorem inf_run (t : Nat) : (cp.FlowGraph.F_MAX (Cost := Int) (E := E)).run t = some (infinity, t + 1) := rfl

/-- The generated cost search terminates, computes shortest reachable labels and retains exact parent slots. -/
theorem bellman_ford_spec (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (p : Nat → Int)
    (feasible : FeasiblePotential n cap p) (s : Nat) (hs : s < g.adj.size) (fuelBound : g.adj.size ≤ fuel) (t : Nat) :
    ∃ (out : Pass Int) (finish : Nat),
      (cp.FlowGraph.bellman_ford g (s : Int)).run t = some ((labelPart out, g), finish) ∧
      LabelSizes g.adj.size out ∧
      SoundLabels n cap s (known out) (label out) ∧
      (∀ a, 0 < cap a → known out (n.tail a) = true →
        HasLabel (known out) (label out) (n.head a) (label out (n.tail a) + n.cost a)) ∧
      (∀ v, (known out v = true ↔ ∃ path, Path n s v path ∧ ∀ a ∈ path, 0 < cap a) ∧
        ∀ path, Path n s v path → (∀ a ∈ path, 0 < cap a) → label out v ≤ (path.map n.cost).sum) ∧
      (∃ last, ValidParents n cap s (fun v => if known out v then some (label out v) else none)
        (savedParent atSlot s out) last) ∧
      finish ≤ t + 2 + 6 * g.adj.size + g.adj.size * (1 + g.adj.size + arcCount g) := by
  let b := startLabels g.n_ s infinity
  let rewrap (c : Labels Int) : Pass Int := (c.1, c.2.1, c.2.2, false)
  have hn : g.n_.toNat = g.adj.size := by simp [layout.graph_size]
  have hsource : s < g.n_.toNat := by rwa [hn]
  have sizes : LabelSizes g.adj.size b := by rw [← hn]; exact start_sizes g.n_ s infinity
  have cert : SearchCert n cap s atSlot b := start_sound n cap atSlot g.n_ s hsource infinity
  have stops := stops_within_vertices layout p feasible s hs b sizes cert
  let invariant (c : Labels Int) : Prop := LabelSizes g.adj.size (rewrap c) ∧ SearchCert n cap s atSlot (rewrap c)
  have carries (c : Labels Int) (hc : invariant c) : invariant (labelPart (sweep g c)) := by
    obtain ⟨sz, ok, _, _⟩ := sweep_cert layout p feasible s (rewrap c) hc.1 hc.2
    exact ⟨⟨sz.distance, sz.parent, sz.edgeNumber⟩, ⟨ok.sound, ok.parents⟩⟩
  let tStart := t + 1 + 1 + g.n_.toNat + g.n_.toNat + g.n_.toNat
  obtain ⟨c, tickEnd, hlo, closed, ⟨os, certOut⟩, spent⟩ := pass_loop g fuel g.adj.size fuelBound (labelPart b) stops
    tStart invariant carries ⟨sizes, cert⟩
  let out := rewrap c
  have stableOf := stable_closed n g cap atSlot layout out os closed
  let total := tickEnd + c.1.size + c.2.1.size + c.2.2.size
  refine ⟨out, total, ?_, os, certOut.sound, stableOf,
    closed_shortest n cap s (known out) (label out) certOut.sound stableOf, ?_, ?_⟩
  · rw [search_program]
    unfold search
    simp only [StateT.run_bind, tick_run, tickN_run, inf_run, some_bind]
    change ((loopFuel fuel (labelPart b) (passStep g)).run tStart >>= _) = _
    rw [hlo]
    rfl
  · obtain ⟨last, now, ph⟩ := certOut.parents
    exact ⟨last, parent_state_complete n cap s (known out) (label out) (savedParent atSlot s out) last now
      ph certOut.sound.root.2 stableOf⟩
  · change tickEnd + out.1.size + out.2.1.size + out.2.2.1.size ≤ _
    rw [os.distance, os.parent, os.edgeNumber]
    rw [charge n g cap atSlot layout] at spent
    unfold tStart at spent
    rw [hn] at spent
    omega

end Proofs.Cpp.FlowCostSearch
