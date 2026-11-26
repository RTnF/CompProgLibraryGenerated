import Proofs.Cpp.FlowCostSearchPass
import Proofs.Math.FlowCostDistance

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

def known (b : Pass Int) (v : Nat) : Bool := decide (v < b.2.1.size) && decide (get b.2.1 (v : Int) ≠ -1)

theorem known_iff (b : Pass Int) (v : Nat) : known b v = true ↔
    v < b.2.1.size ∧ get b.2.1 (v : Int) ≠ -1 := by
  simp only [known, Bool.and_eq_true, decide_eq_true_eq]

def label (b : Pass Int) (v : Nat) : Int := get b.1 (v : Int)

/-- Resolve the saved row and position, leaving the initial source marker without a parent. -/
def savedParent (atSlot : Int → Int → Option Arc) (s : Nat) (b : Pass Int) (v : Nat) : Option Arc :=
  if v = s ∨ ¬ v < b.2.1.size ∨ get b.2.1 (v : Int) = -1 then none
  else atSlot (get b.2.1 (v : Int)) (get b.2.2.1 (v : Int))

private theorem get_after_set (xs : Array Int) (v : Nat) (value : Int) (h : v < xs.size) (u : Nat) :
    get (set xs (v : Int) value) (u : Int) = overwrite (fun (w : Nat) => get xs (w : Int)) v value u := by
  unfold overwrite
  simpa only [get_natCast, Int.toNat_natCast] using getElemBang_set xs (v : Int) value u (by simpa using h)

theorem relax_projects (atSlot : Int → Int → Option Arc) (source u w i : Nat) (row : Array E) (b : Pass Int)
    (a : Arc) (valid : atSlot (u : Int) (i : Int) = some a) (notSource : w ≠ source)
    (targets : target (get row (i : Int)) = (w : Int)) (dsize : w < b.1.size)
    (psize : w < b.2.1.size) (isize : w < b.2.2.1.size) :
    let e := get row (i : Int)
    let out := relaxEdge e (u : Int) (i : Int) b
    let distance := label b u + Field.get (member := "cost") (Value := Int) e
    label out = overwrite (label b) w distance ∧
    known out = overwrite (known b) w true ∧
    savedParent atSlot source out = overwrite (savedParent atSlot source b) w (some a) := by
  dsimp only [relaxEdge]
  rw [targets]
  refine ⟨?_, ?_, ?_⟩
  · funext v
    change get (set b.1 (w : Int) _) (v : Int) = overwrite (fun (u : Nat) => get b.1 (u : Int)) w _ v
    exact get_after_set b.1 w _ dsize v
  · funext v
    unfold known
    simp only [size_set]
    rw [get_after_set b.2.1 w _ psize]
    by_cases h : v = w
    · subst v
      have h0 : (u : Int) ≠ -1 := by omega
      simp [overwrite, h0, psize]
    · simp only [overwrite, h, ite_false]
  · funext v
    unfold savedParent
    simp only [size_set]
    rw [get_after_set b.2.1 w _ psize, get_after_set b.2.2.1 w _ isize]
    by_cases h : v = w
    · subst v
      have h0 : (u : Int) ≠ -1 := by omega
      simp [overwrite, h0, notSource, psize, valid]
    · simp only [overwrite, h, ite_false]

/-- The relaxation condition is the mathematical positive-capacity and strict-improvement test. -/
theorem relaxes_projects (n : Network Arc Nat) (capacity : Capacity Arc) (a : Arc) (b : Pass Int)
    (e : E) (target_eq : target e = (n.head a : Int))
    (cap_eq : Field.get (member := "cap") (Value := Int) e = capacity a)
    (cost_eq : Field.get (member := "cost") (Value := Int) e = n.cost a) (bound : n.head a < b.2.1.size) :
    relaxes e (n.tail a : Int) b = true ↔ 0 < capacity a ∧
      (known b (n.head a) = true → label b (n.tail a) + n.cost a < label b (n.head a)) := by
  unfold relaxes label
  rw [target_eq, cap_eq, cost_eq]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, known_iff, bound, true_and]
  by_cases h : get b.2.1 (n.head a : Int) = -1
  · exact ⟨fun p => ⟨p.1, fun hn => False.elim (hn h)⟩, fun p => ⟨p.1, Or.inl h⟩⟩
  · exact ⟨fun p => ⟨p.1, fun _ => p.2.resolve_left h⟩, fun p => ⟨p.1, Or.inr (p.2 h)⟩⟩

/-- Feasible reduced costs ensure the source is never overwritten despite the shared parent marker. -/
theorem relaxes_target_ne_source [DecidableEq Arc] (n : Network Arc Nat) (capacity : Capacity Arc)
    (p : Nat → Int) (feasible : FeasiblePotential n capacity p) (source : Nat) (a : Arc) (b : Pass Int)
    (sound : SoundLabels n capacity source (known b) (label b)) (openRow : known b (n.tail a) = true)
    (positive : 0 < capacity a)
    (better : known b (n.head a) = true → label b (n.tail a) + n.cost a < label b (n.head a)) :
    n.head a ≠ source := by
  intro eq
  have edge_cost := feasible a positive
  have lower := sound.lower feasible (n.tail a) openRow
  have strict := better (eq.symm ▸ sound.root.1)
  rw [eq] at strict edge_cost
  have root := sound.root.2
  omega

structure SearchCert (n : Network Arc Nat) (capacity : Capacity Arc) (source : Nat)
    (atSlot : Int → Int → Option Arc) (b : Pass Int) : Prop where
  sound : SoundLabels n capacity source (known b) (label b)
  parents : ∃ (last : Nat → Nat) (now : Nat),
    ParentState n capacity source (known b) (label b) (savedParent atSlot source b) last now

theorem fold_preserves_cert [DecidableEq Arc] (n : Network Arc Nat) (capacity : Capacity Arc)
    (p : Nat → Int) (feasible : FeasiblePotential n capacity p) (source : Nat) (a : Arc)
    (atSlot : Int → Int → Option Arc) (row : Array E) (i : Nat) (b : Pass Int)
    (valid : atSlot (n.tail a : Int) (i : Int) = some a) (openRow : known b (n.tail a) = true)
    (dsize : n.head a < b.1.size) (psize : n.head a < b.2.1.size) (isize : n.head a < b.2.2.1.size)
    (target_eq : target (get row (i : Int)) = (n.head a : Int))
    (cap_eq : Field.get (member := "cap") (Value := Int) (get row (i : Int)) = capacity a)
    (cost_eq : Field.get (member := "cost") (Value := Int) (get row (i : Int)) = n.cost a)
    (before : SearchCert n capacity source atSlot b) :
    SearchCert n capacity source atSlot (edgeFold row (n.tail a : Int) b (i : Int)) := by
  unfold edgeFold
  split
  next h =>
    have ⟨pos, better⟩ := (relaxes_projects n capacity a b _ target_eq cap_eq cost_eq psize).mp h
    have notSource := relaxes_target_ne_source n capacity p feasible source a b before.sound openRow pos better
    obtain ⟨labels, seen, pred⟩ := relax_projects atSlot source (n.tail a) (n.head a) i row b a valid notSource
      target_eq dsize psize isize
    rw [cost_eq] at labels
    constructor
    · rw [seen, labels]
      exact relax_sound n capacity source a (known b) (label b) p before.sound feasible pos openRow better
    · obtain ⟨last, now, old⟩ := before.parents
      rw [seen, labels, pred]
      exact ⟨_, _, parent_state_relax n capacity source (known b) (label b)
        (savedParent atSlot source b) last now old a pos openRow better⟩
  next => exact before

theorem no_relax_projects (n : Network Arc Nat) (capacity : Capacity Arc) (a : Arc) (b : Pass Int)
    (e : E) (target_eq : target e = (n.head a : Int))
    (cap_eq : Field.get (member := "cap") (Value := Int) e = capacity a)
    (cost_eq : Field.get (member := "cost") (Value := Int) e = n.cost a) (bound : n.head a < b.2.1.size)
    (hfalse : relaxes e (n.tail a : Int) b = false) (pos : 0 < capacity a) :
    HasLabel (known b) (label b) (n.head a) (label b (n.tail a) + n.cost a) := by
  have noBetter : ¬ (known b (n.head a) = true → label b (n.tail a) + n.cost a < label b (n.head a)) := by
    intro h
    have hx := (relaxes_projects n capacity a b e target_eq cap_eq cost_eq bound).mpr ⟨pos, h⟩
    rw [hfalse] at hx
    contradiction
  have seen : known b (n.head a) = true := by
    by_contra h
    exact noBetter fun h' => False.elim (h h')
  refine ⟨seen, ?_⟩
  by_contra h
  exact noBetter fun _ => by omega

structure LabelSizes (n : Nat) (b : Pass Int) : Prop where
  distance : b.1.size = n
  parent : b.2.1.size = n
  edgeNumber : b.2.2.1.size = n

theorem edgeFold_sizes (row : Array E) (v i : Int) (b : Pass Int) {n : Nat} (sizes : LabelSizes n b) :
    LabelSizes n (edgeFold row v b i) := by
  unfold edgeFold
  split
  · exact ⟨by simp [relaxEdge, sizes.distance], by simp [relaxEdge, sizes.parent], by simp [relaxEdge, sizes.edgeNumber]⟩
  · exact sizes

def Improves (start finish : Pass Int) : Prop :=
  ∀ v cost, HasLabel (known start) (label start) v cost → HasLabel (known finish) (label finish) v cost

theorem Improves.refl (b : Pass Int) : Improves b b := fun _ _ h => h

theorem Improves.trans {a b c : Pass Int} (ab : Improves a b) (bc : Improves b c) : Improves a c :=
  fun v cost h => bc v cost (ab v cost h)

theorem edgeFold_label_bounds [DecidableEq Arc] (n : Network Arc Nat) (capacity : Capacity Arc)
    (p : Nat → Int) (feasible : FeasiblePotential n capacity p) (source : Nat) (a : Arc)
    (atSlot : Int → Int → Option Arc) (row : Array E) (i : Nat) (b : Pass Int)
    (valid : atSlot (n.tail a : Int) (i : Int) = some a) (openRow : known b (n.tail a) = true)
    {size : Nat} (sizes : LabelSizes size b) (headBound : n.head a < size)
    (target_eq : target (get row (i : Int)) = (n.head a : Int))
    (cap_eq : Field.get (member := "cap") (Value := Int) (get row (i : Int)) = capacity a)
    (cost_eq : Field.get (member := "cost") (Value := Int) (get row (i : Int)) = n.cost a)
    (sound : SoundLabels n capacity source (known b) (label b)) :
    let out := edgeFold row (n.tail a : Int) b (i : Int)
    Improves b out ∧
      (0 < capacity a → HasLabel (known out) (label out) (n.head a) (label b (n.tail a) + n.cost a)) := by
  have bound : n.head a < b.2.1.size := by rwa [sizes.parent]
  unfold edgeFold
  split
  next fire =>
    have ⟨hp, lower⟩ := (relaxes_projects n capacity a b _ target_eq cap_eq cost_eq bound).mp fire
    have notSource := relaxes_target_ne_source n capacity p feasible source a b sound openRow hp lower
    obtain ⟨labels, seen, _⟩ := relax_projects atSlot source (n.tail a) (n.head a) i row b a valid notSource
      target_eq (by rwa [sizes.distance]) (by rwa [sizes.parent]) (by rwa [sizes.edgeNumber])
    rw [cost_eq] at labels
    refine ⟨?_, ?_⟩
    · intro v cost prev
      rw [seen, labels]
      exact relax_keeps_lower n a (known b) (label b) lower v cost prev
    · intro _
      rw [seen, labels]
      simp [HasLabel, overwrite]
  next h =>
    have closed : relaxes (get row (i : Int)) (n.tail a : Int) b = false := by
      cases casesFlag : relaxes (get row (i : Int)) (n.tail a : Int) b <;> simp_all
    exact ⟨Improves.refl b, no_relax_projects n capacity a b _ target_eq cap_eq cost_eq bound closed⟩

end Proofs.Cpp.FlowCostSearch
