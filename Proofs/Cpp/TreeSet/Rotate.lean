import Proofs.Cpp.TreeSet.Refresh

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def leftPivot {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) : UInt64 :=
  (cell arena.slots i).right

def rightPivot {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) : UInt64 :=
  (cell arena.slots i).left

def linkLeft {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i child : UInt64) : cp.TreeSet K :=
  putCell arena i { cell arena.slots i with left := child }

def linkRight {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i child : UInt64) : cp.TreeSet K :=
  putCell arena i { cell arena.slots i with right := child }

def linkRotateLeft {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) : cp.TreeSet K :=
  let pivot := leftPivot arena i
  let moved := linkRight arena i (cell arena.slots pivot).left
  linkLeft moved pivot i

def linkRotateRight {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) : cp.TreeSet K :=
  let pivot := rightPivot arena i
  let moved := linkLeft arena i (cell arena.slots pivot).right
  linkRight moved pivot i

theorem generated_rotate_left_program {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    cp.TreeSet.rotate_left arena i = (do
      Cpp.tick
      let next ← cp.TreeSet.refresh (linkRotateLeft arena i) i
      let out ← cp.TreeSet.refresh next (leftPivot arena i)
      return (leftPivot arena i, out)) := by
  rcases arena with ⟨_, _, _⟩
  unfold cp.TreeSet.rotate_left linkRotateLeft linkLeft linkRight leftPivot putCell cell slotOffset
  rfl

theorem generated_rotate_right_program {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    cp.TreeSet.rotate_right arena i = (do
      Cpp.tick
      let next ← cp.TreeSet.refresh (linkRotateRight arena i) i
      let out ← cp.TreeSet.refresh next (rightPivot arena i)
      return (rightPivot arena i, out)) := by
  rcases arena with ⟨_, _, _⟩
  unfold cp.TreeSet.rotate_right linkRotateRight linkLeft linkRight rightPivot putCell cell slotOffset
  rfl

theorem linkLeft_preserves {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i next : UInt64) (inside : i.toNat < arena.slots.size) (fits : arena.slots.size ≤ 2 ^ 63) :
    cell (linkLeft arena i next).slots i = { cell arena.slots i with left := next } :=
  cell_written _ _ _ (by rwa [slotOffset_nat i (by omega)])

theorem linkRight_preserves {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i next : UInt64) (inside : i.toNat < arena.slots.size) (fits : arena.slots.size ≤ 2 ^ 63) :
    cell (linkRight arena i next).slots i = { cell arena.slots i with right := next } :=
  cell_written _ _ _ (by rwa [slotOffset_nat i (by omega)])

theorem cell_put_away {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i j : UInt64) (row : cp.TreeSet_Slot K) (inside : i.toNat < arena.slots.size)
    (inRange : j.toNat < arena.slots.size) (fits : arena.slots.size ≤ 2 ^ 63) (apart : j ≠ i) :
    cell (putCell arena i row).slots j = cell arena.slots j := by
  apply cell_other
  · rwa [slotOffset_nat i (by omega)]
  · rw [slotOffset_nat i (by omega), slotOffset_nat j (by omega)]
    exact fun same => apart (UInt64.toNat_inj.mp same)

@[simp] theorem linkLeft_size {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i next : UInt64) :
    (linkLeft arena i next).slots.size = arena.slots.size := by simp [linkLeft]

@[simp] theorem linkRight_size {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i next : UInt64) :
    (linkRight arena i next).slots.size = arena.slots.size := by simp [linkRight]


structure TwoCells {K : Type} [Inhabited K] (before after : cp.TreeSet K) (i j : UInt64) : Prop where
  root : after.root = before.root
  free : after.free_head = before.free_head
  size : after.slots.size = before.slots.size
  outside : ∀ k, k.toNat < before.slots.size → k.toNat ≠ i.toNat → k.toNat ≠ j.toNat →
    cell after.slots k = cell before.slots k

theorem TwoCells.trans {K : Type} [Inhabited K] {a b c : cp.TreeSet K} {i j : UInt64}
    (ab : TwoCells a b i j) (bc : TwoCells b c i j) : TwoCells a c i j :=
  ⟨bc.root.trans ab.root, bc.free.trans ab.free, bc.size.trans ab.size,
    fun k allocated hi hj => (bc.outside k (by rwa [ab.size]) hi hj).trans (ab.outside k allocated hi hj)⟩

theorem TwoCells.layout {K : Type} [Inhabited K] {a b : cp.TreeSet K} {i j index : UInt64}
    {tree : Tree K} {used : List Nat} (frame : TwoCells a b i j)
    (layout : Layout a.slots index tree used) (xi : i.toNat ∉ used) (xj : j.toNat ∉ used) :
    Layout b.slots index tree used := by
  apply layout.frame
  · simpa [frame.size] using layout.in_range
  · intro k member
    exact (frame.outside k (layout.in_range _ member)
      (fun same => xi (same ▸ member)) (fun same => xj (same ▸ member))).symm

theorem TwoCells.putFirst {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i j : UInt64)
    (row : cp.TreeSet_Slot K) (inside : i.toNat < arena.slots.size)
    (fits : arena.slots.size ≤ 2 ^ 63) : TwoCells arena (putCell arena i row) i j := by
  refine ⟨rfl, rfl, putCell_size .., ?_⟩
  intro k allocated hi _
  exact cell_put_away arena i k row inside allocated fits (fun same => hi (congrArg UInt64.toNat same))

theorem TwoCells.putSecond {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i j : UInt64)
    (row : cp.TreeSet_Slot K) (inside : j.toNat < arena.slots.size)
    (fits : arena.slots.size ≤ 2 ^ 63) : TwoCells arena (putCell arena j row) i j := by
  refine ⟨rfl, rfl, putCell_size .., ?_⟩
  intro k allocated _ hj
  exact cell_put_away arena j k row inside allocated fits (fun same => hj (congrArg UInt64.toNat same))

private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl

theorem generated_rotate_left_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i : UInt64) (a b c : Tree K) (x y : K) (knownLeft knownRight : List Nat)
    (old : Pending arena i a x (.node b y c) knownLeft knownRight)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    let j := leftPivot arena i
    ∃ after occupied, (cp.TreeSet.rotate_left arena i).run start = some ((j, after), start + 23) ∧
      Layout after.slots j (.node (.node a x b) y c) occupied ∧ TwoCells arena after i j ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (knownLeft ++ knownRight)) := by
  let j := leftPivot arena i
  obtain ⟨bs, cs, rightUsed, pivot⟩ := layout_pending old.rightLayout
  change Pending arena j b y c bs cs at pivot
  change knownRight = j.toNat :: (bs ++ cs) at rightUsed
  have allocatedI := old.allocated
  have allocatedJ := pivot.allocated
  let oldPivot := cell arena.slots j
  let one := linkRight arena i oldPivot.left
  let two := linkLeft one j i
  let three := putCell two i (refreshRow two i)
  let four := putCell three j (refreshRow three j)
  have different : i.toNat ≠ j.toNat := fun same => old.rightApart (by rw [rightUsed, same]; simp)
  have diff : i ≠ j := fun eq => different (congrArg UInt64.toNat eq)
  have leftJ : j.toNat ∉ knownLeft := fun mem => old.disjoint mem (by rw [rightUsed]; simp)
  have iB : i.toNat ∉ bs := fun mem => old.rightApart (by rw [rightUsed]; simp [mem])
  have iC : i.toNat ∉ cs := fun mem => old.rightApart (by rw [rightUsed]; simp [mem])
  have splitB : List.Disjoint knownLeft bs :=
    fun _ ha hb => old.disjoint ha (by rw [rightUsed]; simp [hb])
  have splitC : List.Disjoint knownLeft cs :=
    fun _ ha hc => old.disjoint ha (by rw [rightUsed]; simp [hc])
  have sizeOne : one.slots.size = arena.slots.size := linkRight_size ..
  have sizeTwo : two.slots.size = arena.slots.size := (linkLeft_size ..).trans sizeOne
  have sizeThree : three.slots.size = arena.slots.size := (putCell_size ..).trans sizeTwo
  have frame1 : TwoCells arena one i j := .putFirst _ _ _ _ old.allocated fits
  have frame2 : TwoCells one two i j := .putSecond _ _ _ _ (by rwa [sizeOne]) (by rwa [sizeOne])
  have linked := frame1.trans frame2
  have oneI : cell one.slots i = { cell arena.slots i with right := oldPivot.left } :=
    linkRight_preserves _ _ _ old.allocated fits
  have oneJ : cell one.slots j = oldPivot :=
    cell_put_away arena i j _ allocatedI allocatedJ fits (Ne.symm diff)
  have twoI : cell two.slots i = cell one.slots i :=
    cell_put_away one j i _ (by rwa [sizeOne] : j.toNat < one.slots.size)
      (by rwa [sizeOne] : i.toNat < one.slots.size) (by rwa [sizeOne]) diff
  have twoJ : cell two.slots j = { oldPivot with left := i } := by
    change cell (linkLeft one j i).slots j = _
    rw [linkLeft_preserves _ _ _ (by rwa [sizeOne]) (by rwa [sizeOne]), oneJ]
  have inner : Pending two i a x b knownLeft bs := by
    refine ⟨by rwa [sizeTwo], old.nonnull, ?_, ?_, ?_, old.leftApart, iB, splitB⟩
    · rw [twoI, oneI]
      exact old.value
    · rw [twoI, oneI]
      exact linked.layout old.leftLayout old.leftApart leftJ
    · rw [twoI, oneI]
      exact linked.layout pivot.leftLayout iB pivot.leftApart
  have first := generated_refresh_layout two i a x b knownLeft bs inner (by rwa [sizeTwo]) (start + 1)
  have frame3 : TwoCells two three i j := .putFirst _ _ _ _ (by rwa [sizeTwo]) (by rwa [sizeTwo])
  have threeJ : cell three.slots j = cell two.slots j :=
    cell_put_away two i j _ (by rwa [sizeTwo] : i.toNat < two.slots.size)
      (by rwa [sizeTwo] : j.toNat < two.slots.size) (by rwa [sizeTwo]) (Ne.symm diff)
  have outer : Pending three j (.node a x b) y c (i.toNat :: (knownLeft ++ bs)) cs := by
    refine ⟨by rwa [sizeThree], pivot.nonnull, ?_, ?_, ?_, ?_, pivot.rightApart, ?_⟩
    · rw [threeJ, twoJ]
      exact pivot.value
    · rw [threeJ, twoJ]
      exact first.2
    · rw [threeJ, twoJ]
      exact (linked.trans frame3).layout pivot.rightLayout iC pivot.rightApart
    · simp [Ne.symm different, leftJ, pivot.leftApart]
    · intro k inLeft inRight
      rcases List.mem_cons.mp inLeft with rfl | under
      · exact iC inRight
      · exact (List.mem_append.mp under).elim (fun mem => splitC mem inRight)
          (fun mem => pivot.disjoint mem inRight)
  have second := generated_refresh_layout three j (.node a x b) y c _ cs outer
    (by rwa [sizeThree]) (start + 12)
  refine ⟨four, _, ?_, second.2, (linked.trans frame3).trans (.putSecond _ _ _ _
    (by rwa [sizeThree]) (by rwa [sizeThree])), ?_⟩
  · have run1 : (cp.TreeSet.refresh two i).run (start + 1) = some (three, start + 12) := first.1
    have run2 : (cp.TreeSet.refresh three j).run (start + 12) = some (four, start + 23) := second.1
    rw [generated_rotate_left_program]
    simp only [StateT.run_bind, tick_run, some_bind, pure_run]
    change (do
      let p ← (cp.TreeSet.refresh two i).run (start + 1)
      let q ← (cp.TreeSet.refresh p.1 j).run p.2
      pure ((j, q.1), q.2)) = some ((j, four), start + 23)
    simp only [run1, some_bind, run2]
    rfl
  · intro k
    simp only [rightUsed, List.mem_cons, List.mem_append]
    simp only [or_assoc, or_left_comm, or_comm]

theorem generated_rotate_right_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i : UInt64) (a b c : Tree K) (x y : K) (knownLeft knownRight : List Nat)
    (old : Pending arena i (.node c y b) x a knownLeft knownRight)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    let j := rightPivot arena i
    ∃ after occupied, (cp.TreeSet.rotate_right arena i).run start = some ((j, after), start + 23) ∧
      Layout after.slots j (.node c y (.node b x a)) occupied ∧ TwoCells arena after i j ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (knownLeft ++ knownRight)) := by
  let j := rightPivot arena i
  obtain ⟨cs, bs, leftUsed, pivot⟩ := layout_pending old.leftLayout
  change Pending arena j c y b cs bs at pivot
  change knownLeft = j.toNat :: (cs ++ bs) at leftUsed
  have allocatedI := old.allocated
  have allocatedJ := pivot.allocated
  let oldPivot := cell arena.slots j
  let one := linkLeft arena i oldPivot.right
  let two := linkRight one j i
  let three := putCell two i (refreshRow two i)
  let four := putCell three j (refreshRow three j)
  have different : i.toNat ≠ j.toNat := fun same => old.leftApart (by rw [leftUsed, same]; simp)
  have diff : i ≠ j := fun eq => different (congrArg UInt64.toNat eq)
  have rightJ : j.toNat ∉ knownRight := fun mem => old.disjoint (by rw [leftUsed]; simp) mem
  have iB : i.toNat ∉ bs := fun mem => old.leftApart (by rw [leftUsed]; simp [mem])
  have iC : i.toNat ∉ cs := fun mem => old.leftApart (by rw [leftUsed]; simp [mem])
  have splitB : List.Disjoint knownRight bs :=
    fun _ ha hb => old.disjoint (by rw [leftUsed]; simp [hb]) ha
  have splitC : List.Disjoint knownRight cs :=
    fun _ ha hc => old.disjoint (by rw [leftUsed]; simp [hc]) ha
  have sizeOne : one.slots.size = arena.slots.size := linkLeft_size ..
  have sizeTwo : two.slots.size = arena.slots.size := (linkRight_size ..).trans sizeOne
  have sizeThree : three.slots.size = arena.slots.size := (putCell_size ..).trans sizeTwo
  have frame1 : TwoCells arena one i j := .putFirst _ _ _ _ old.allocated fits
  have frame2 : TwoCells one two i j := .putSecond _ _ _ _ (by rwa [sizeOne]) (by rwa [sizeOne])
  have linked := frame1.trans frame2
  have oneI : cell one.slots i = { cell arena.slots i with left := oldPivot.right } :=
    linkLeft_preserves _ _ _ old.allocated fits
  have oneJ : cell one.slots j = oldPivot :=
    cell_put_away arena i j _ allocatedI allocatedJ fits (Ne.symm diff)
  have twoI : cell two.slots i = cell one.slots i :=
    cell_put_away one j i _ (by rwa [sizeOne] : j.toNat < one.slots.size)
      (by rwa [sizeOne] : i.toNat < one.slots.size) (by rwa [sizeOne]) diff
  have twoJ : cell two.slots j = { oldPivot with right := i } := by
    change cell (linkRight one j i).slots j = _
    rw [linkRight_preserves _ _ _ (by rwa [sizeOne]) (by rwa [sizeOne]), oneJ]
  have inner : Pending two i b x a bs knownRight := by
    refine ⟨by rwa [sizeTwo], old.nonnull, ?_, ?_, ?_, iB, old.rightApart, fun {_} hb ha => splitB ha hb⟩
    · rw [twoI, oneI]
      exact old.value
    · rw [twoI, oneI]
      exact linked.layout pivot.rightLayout iB pivot.rightApart
    · rw [twoI, oneI]
      exact linked.layout old.rightLayout old.rightApart rightJ
  have first := generated_refresh_layout two i b x a bs knownRight inner (by rwa [sizeTwo]) (start + 1)
  have frame3 : TwoCells two three i j := .putFirst _ _ _ _ (by rwa [sizeTwo]) (by rwa [sizeTwo])
  have threeJ : cell three.slots j = cell two.slots j :=
    cell_put_away two i j _ (by rwa [sizeTwo] : i.toNat < two.slots.size)
      (by rwa [sizeTwo] : j.toNat < two.slots.size) (by rwa [sizeTwo]) (Ne.symm diff)
  have outer : Pending three j c y (.node b x a) cs (i.toNat :: (bs ++ knownRight)) := by
    refine ⟨by rwa [sizeThree], pivot.nonnull, ?_, ?_, ?_, pivot.leftApart, ?_, ?_⟩
    · rw [threeJ, twoJ]
      exact pivot.value
    · rw [threeJ, twoJ]
      exact (linked.trans frame3).layout pivot.leftLayout iC pivot.leftApart
    · rw [threeJ, twoJ]
      exact first.2
    · simp [Ne.symm different, rightJ, pivot.rightApart]
    · intro k inLeft inRight
      rcases List.mem_cons.mp inRight with rfl | under
      · exact iC inLeft
      · exact (List.mem_append.mp under).elim (fun mem => pivot.disjoint inLeft mem)
          (fun mem => splitC mem inLeft)
  have second := generated_refresh_layout three j c y (.node b x a) cs _ outer
    (by rwa [sizeThree]) (start + 12)
  refine ⟨four, _, ?_, second.2, (linked.trans frame3).trans (.putSecond _ _ _ _
    (by rwa [sizeThree]) (by rwa [sizeThree])), ?_⟩
  · have run1 : (cp.TreeSet.refresh two i).run (start + 1) = some (three, start + 12) := first.1
    have run2 : (cp.TreeSet.refresh three j).run (start + 12) = some (four, start + 23) := second.1
    rw [generated_rotate_right_program]
    simp only [StateT.run_bind, tick_run, some_bind, pure_run]
    change (do
      let p ← (cp.TreeSet.refresh two i).run (start + 1)
      let q ← (cp.TreeSet.refresh p.1 j).run p.2
      pure ((j, q.1), q.2)) = some ((j, four), start + 23)
    simp only [run1, some_bind, run2]
    rfl
  · intro k
    simp only [leftUsed, List.mem_cons, List.mem_append]
    simp only [or_assoc, or_left_comm, or_comm]

end Proofs.Cpp.TreeSet
