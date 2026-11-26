import Proofs.Cpp.FlowCostBottleneck
import Proofs.Cpp.FlowDinicProgram
import Proofs.Cpp.FlowResidualView

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowDinic

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [DecidableEq Arc]

/-- The two writes in the generated slope loop. The reverse row is the current destination. -/
def pushPairTo (adj : Array (Array E)) (v i w d : Int) : Array (Array E) :=
  let e := atEdge adj v i
  let updated := set adj v (set (get adj v) i (withCap e (cap e - d)))
  let k := revIdx (atEdge updated v i)
  let r := atEdge updated w k
  set updated w (set (get updated w) k (withCap r (cap r + d)))

private theorem pushPairTo_adjust (n : Network Arc Nat) (adj : Array (Array E)) (slot : Arc → Slot)
    (rep : Represents n adj slot) (laws : CapLaws (E := E)) (a : Arc) (d : Int)
    (validRev : 0 ≤ revIdx (readSlot adj (slot a))) :
    pushPairTo adj ((slot a).1 : Int) ((slot a).2 : Int) (n.head a : Int) d = adjust adj (slot a) d := by
  let s := slot a
  let e := readSlot adj s
  let updated := writeSlot adj s (withCap e (cap e - d))
  have hread : readSlot updated s = withCap e (cap e - d) := by
    simp [updated, read_writeSlot adj s s _ (rep.bounded a)]
  have hv : dest (readSlot updated s) = (n.head a : Int) := by
    rw [hread, laws.to_same]
    exact rep.head_eq a
  have hbound : 0 ≤ dest (readSlot adj s) := by
    change 0 ≤ dest (readSlot adj (slot a))
    rw [rep.head_eq]
    exact Int.natCast_nonneg _
  rw [← pushPair_adjust laws adj s.1 s.2 d (rep.bounded a) hbound validRev]
  let k := revIdx (readSlot updated s)
  let amend (w : Int) :=
    let r := atEdge updated w k
    set updated w (set (get updated w) k (withCap r (cap r + d)))
  change amend (n.head a : Int) = amend (dest (readSlot updated s))
  rw [hv]

def pushParentStep (s : Int) (parents indices : Array Int) (amount : Int) (_ : Unit)
    (st : Array (Array E) × Int) : M (ForInStep (Array (Array E) × Int)) := do
  tick
  if !(decide (st.2 ≠ s)) then
    return .done st
  let sourceRow := get parents st.2
  let i := get indices st.2
  return .yield (pushPairTo st.1 sourceRow i st.2 amount, sourceRow)

/-- The generated updates follow the predecessor chain and realize the reversed path augmentation. -/
theorem push_parent_loop (n : Network Arc Nat) (slot : Arc → Slot) (laws : CapLaws (E := E))
    (b : Pass Int) (s t : Nat) (path : List Arc) (route : Path n s t path) (lim : Nat) (enough : path.length < lim)
    (parents : ∀ a ∈ path, n.head a ≠ s ∧ get b.2.1 (n.head a : Int) = ((slot a).1 : Int) ∧
      get b.2.2.1 (n.head a : Int) = ((slot a).2 : Int))
    (adj : Array (Array E)) (rep : Represents n adj slot)
    (indicesValid : ∀ a, 0 ≤ revIdx (readSlot adj (slot a))) (d : Int) (clock : Nat) :
    ∃ out, (loopFuel lim (adj, (t : Int)) (pushParentStep (s : Int) b.2.1 b.2.2.1 d)).run clock =
      some ((out, (s : Int)), clock + path.length + 1) ∧ Represents n out slot ∧
      (out.size = adj.size ∧ ∀ v : Nat, out[v]!.size = adj[v]!.size) ∧
      (∀ a, 0 ≤ revIdx (readSlot out (slot a))) ∧
      capacity out slot = augment n d (capacity adj slot) path.reverse := by
  induction lim generalizing t path adj clock with
  | zero => omega
  | succ lim ih =>
    by_cases empty : path = []
    · have root := route.eq_of_empty empty
      subst t path
      refine ⟨adj, ?_, rep, ⟨rfl, fun _ => rfl⟩, indicesValid, rfl⟩
      rw [loopFuel]
      unfold pushParentStep
      simp only [List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false, decide_false, Bool.not_false, ite_true]
      rfl
    · obtain ⟨front, last, eq, suffix, dest⟩ := route.split_last empty
      have hlast : last ∈ path := by simp [eq]
      obtain ⟨notSource, sourceRow, idx⟩ := parents last hlast
      have castNe : (t : Int) ≠ (s : Int) := by omega
      have enough' : front.length < lim := by simp [eq] at enough; omega
      let mid := adjust adj (slot last) d
      have repMid : Represents n mid slot := rep.adjust laws last d
      have hr : InBounds adj (reverseSlot adj (slot last)) := by rw [rep.reverse_eq]; exact rep.bounded _
      have distinct : reverseSlot adj (slot last) ≠ slot last := by
        rw [rep.reverse_eq]
        exact fun h => n.reverse_ne last (rep.injective h)
      have midDims := adjust_shape laws adj (slot last) d (rep.bounded last) hr
      have indicesMid (a : Arc) : 0 ≤ revIdx (readSlot mid (slot a)) := by
        have fields := adjust_metadata laws adj (slot last) d (rep.bounded last) hr distinct (slot a)
        rw [fields.2.1]
        exact indicesValid a
      obtain ⟨out, tailRun, repOut, outDims, outIndices, charges⟩ := ih (n.tail last) front suffix enough'
        (fun a ha => parents a (by rw [eq]; exact List.mem_append.mpr (Or.inl ha))) mid repMid indicesMid (clock + 1)
      refine ⟨out, ?_, repOut, ⟨outDims.1.trans midDims.1, fun v => (outDims.2 v).trans (midDims.2 v)⟩, outIndices, ?_⟩
      · have one : (pushParentStep (s : Int) b.2.1 b.2.2.1 d () (adj, (t : Int))).run clock =
            some (.yield (mid, (n.tail last : Int)), clock + 1) := by
          unfold pushParentStep
          have skip : ¬ (!decide ((t : Int) ≠ (s : Int))) = true := by
            rw [decide_eq_true castNe]
            decide
          dsimp only
          rw [ite_eq_right skip, ← dest, sourceRow, idx, pushPairTo_adjust n adj slot rep laws last d (indicesValid last)]
          rw [rep.tail_eq]
          rfl
        rw [loopFuel, StateT.run_bind, one]
        change (loopFuel lim (mid, (n.tail last : Int)) (pushParentStep (s : Int) b.2.1 b.2.2.1 d)).run (clock + 1) = _
        rw [tailRun, eq, List.length_append]
        simp only [List.length_cons, List.length_nil]
        congr 2
        omega
      · rw [charges, eq, List.reverse_append]
        rw [rep.adjust_capacity laws last d]
        rfl

end Proofs.Cpp.FlowCostSearch
