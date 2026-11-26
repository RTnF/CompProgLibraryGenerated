import Proofs.Cpp.FlowResidualSlots

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.FlowResidualSlots

namespace Proofs.Cpp.FlowDinic

variable {Cost E : Type} [Inhabited E] [Zero Cost] [Add Cost] [Sub Cost] [DecidableEq Cost] [Min Cost]
  [Field "cap" E Cost] [Field "to" E Int] [Field "rev" E Int] [WriteField "cap" E Cost]

abbrev Frame (Cost E : Type) := Option (Cost × cp.FlowGraph Cost E) × Int × Int × Array (Array E) × Array Int × Array Int

def pack (result : Option (Cost × cp.FlowGraph Cost E)) (g : cp.FlowGraph Cost E) : Frame Cost E :=
  (result, g.n_, g.m_, g.adj, g.level, g.iter)

def frameGraph (st : Frame Cost E) : cp.FlowGraph Cost E :=
  ⟨st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2⟩

def atEdge (adj : Array (Array E)) (v i : Int) : E := get (get adj v) i
abbrev capOf (e : E) : Cost := Field.get (member := "cap") e
abbrev destOf (e : E) : Int := Field.get (member := "to") e
abbrev revOf (e : E) : Int := Field.get (member := "rev") e

def pushPair (adj : Array (Array E)) (v i : Int) (d : Cost) : Array (Array E) :=
  let e := atEdge adj v i
  let updated := set adj v (set (get adj v) i (WriteField.set (member := "cap") e (capOf e - d)))
  let e' := atEdge updated v i
  let w := destOf e'
  let k := revOf e'
  let r := atEdge updated w k
  set updated w (set (get updated w) k (WriteField.set (member := "cap") r (capOf r + d)))

def eligible (g : cp.FlowGraph Cost E) (v i : Int) : Bool :=
  let e := atEdge g.adj v i
  !(decide (capOf e = (0 : Cost)) || decide (get g.level v ≥ get g.level (destOf e)))

def advanceCursor (g : cp.FlowGraph Cost E) (v i : Int) : cp.FlowGraph Cost E :=
  { g with iter := set g.iter v (i + 1) }

def tryEdge (lim : Nat) (v t : Int) (limit : Cost) (i : Int) (st : Frame Cost E) : M (ForInStep (Frame Cost E)) := do
  tick
  let mut g := frameGraph st
  let e := atEdge g.adj v i
  if eligible g v i then
    let result ← cp.FlowGraph.dfs_rec lim g (destOf e) t (min limit (capOf e))
    let d := result.1
    g := result.2
    if !(decide (d = (0 : Cost))) then
      let augmented := { g with adj := pushPair g.adj v i d }
      return .done (pack (some (d, augmented)) augmented)
  return .yield (pack none (advanceCursor g v i))

def frame (lim : Nat) (g : cp.FlowGraph Cost E) (v t : Int) (limit : Cost) : M (Cost × cp.FlowGraph Cost E) := do
  tick
  if decide (v = t) then
    return (limit, g)
  else
    let st ← forIn (range (get g.iter v) (size (get g.adj v))) (pack none g) (tryEdge lim v t limit)
    match st.1 with
    | some r => return r
    | none => return (0, frameGraph st)

theorem dfs_frame (lim : Nat) (g : cp.FlowGraph Cost E) (v t : Int) (limit : Cost) :
    cp.FlowGraph.dfs_rec (lim + 1) g v t limit = frame lim g v t limit := by
  rw [cp.FlowGraph.dfs_rec.eq_2]
  unfold frame tryEdge pack frameGraph pushPair eligible advanceCursor atEdge capOf destOf revOf
  dsimp only
  apply congrArg (fun body : Unit → M (Cost × cp.FlowGraph Cost E) => tick >>= body)
  funext _
  by_cases ht : v = t
  · simp only [ht, decide_true, ite_true]
  · simp only [ht, decide_false, Bool.false_eq_true, ite_false]
    congr 1
    funext st
    cases st.1 <;> rfl

theorem tryEdge_ineligible (lim : Nat) (g : cp.FlowGraph Cost E) (v t i : Int) (limit : Cost) (clock : Nat)
    (skip : eligible g v i = false) :
    (tryEdge lim v t limit i (pack none g)).run clock = some (.yield (pack none (advanceCursor g v i)), clock + 1) := by
  unfold tryEdge
  simp only [pack, frameGraph, skip, Bool.false_eq_true, ite_false]
  rfl

theorem tryEdge_recursive (lim : Nat) (g child : cp.FlowGraph Cost E) (v t i : Int) (limit d : Cost)
    (clock finish : Nat) (use : eligible g v i = true)
    (recRun : (cp.FlowGraph.dfs_rec lim g (destOf (atEdge g.adj v i)) t (min limit (capOf (atEdge g.adj v i)))).run
      (clock + 1) = some ((d, child), finish)) :
    let augmented := {child with adj := pushPair child.adj v i d}
    (tryEdge lim v t limit i (pack none g)).run clock =
      some ((if d = 0 then .yield (pack none (advanceCursor child v i)) else
        .done (pack (some (d, augmented)) augmented)), finish) := by
  unfold tryEdge
  simp only [pack, frameGraph, use, ite_true, StateT.run_bind]
  have ht : tick.run clock = some ((), clock + 1) := rfl
  rw [ht]
  change ((cp.FlowGraph.dfs_rec lim g (destOf (atEdge g.adj v i)) t (min limit (capOf (atEdge g.adj v i)))).run
    (clock + 1) >>= _) = _
  rw [recRun]
  have h (fn : (Cost × cp.FlowGraph Cost E) × Nat → Option (ForInStep (Frame Cost E) × Nat)) :=
    show (some ((d, child), finish) >>= fn) = fn ((d, child), finish) from rfl
  rw [h]
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd]

section Pair

variable {E : Type} [Inhabited E] [Field "cap" E Int] [Field "to" E Int] [Field "rev" E Int]
  [Field "cost" E Int] [WriteField "cap" E Int]

/-- When the stored reverse indices are nonnegative, generated writes are the pure paired update. -/
theorem pushPair_adjust (laws : CapLaws (E := E)) (adj : Array (Array E)) (v i : Nat) (d : Int)
    (bound : InBounds adj (v, i)) (targetNonnegative : 0 ≤ dest (readSlot adj (v, i)))
    (reverseNonnegative : 0 ≤ revIdx (readSlot adj (v, i))) :
    pushPair adj (v : Int) (i : Int) d = adjust adj (v, i) d := by
  let a : Slot := (v, i)
  let e := readSlot adj a
  let updated := writeSlot adj a (withCap e (cap e - d))
  have ha : InBounds adj a := bound
  have hread : readSlot updated a = withCap e (cap e - d) := by
    simp [updated, read_writeSlot adj a a _ ha]
  have ht : ((dest (readSlot updated a)).toNat : Int) = dest (readSlot updated a) := by
    rw [hread, laws.to_same]
    exact Int.toNat_of_nonneg targetNonnegative
  have hr : ((revIdx (readSlot updated a)).toNat : Int) = revIdx (readSlot updated a) := by
    rw [hread, laws.rev_same]
    exact Int.toNat_of_nonneg reverseNonnegative
  let w := dest (readSlot updated a)
  let k := revIdx (readSlot updated a)
  let amend (x y : Int) :=
    let r := atEdge updated x y
    set updated x (set (get updated x) y (withCap r (cap r + d)))
  change amend w k = amend (w.toNat : Int) (k.toNat : Int)
  have hw : (w.toNat : Int) = w := ht
  have hk : (k.toNat : Int) = k := hr
  rw [hw, hk]

end Pair
end Proofs.Cpp.FlowDinic
