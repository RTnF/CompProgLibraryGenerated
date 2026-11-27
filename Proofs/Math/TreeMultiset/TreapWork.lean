import Proofs.Math.TreeMultiset.Treap

namespace Proofs.Cpp.TreeMultiset.Tree

def height : Tree K → Nat
  | .empty => 0
  | .node _ _ _ left right => 1 + max left.height right.height

theorem height_le_slots (tree : Tree K) : tree.height ≤ tree.slots := by
  induction tree with
  | empty => exact Nat.le_refl _
  | node key p c left right ihLeft ihRight =>
    simp only [height, slots]
    have : max left.height right.height ≤ left.slots + right.slots :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

def splitSteps [LT K] [DecidableLT K] (pivot : K) : Tree K → Nat
  | .empty => 1
  | .node key _ _ left right =>
    1 + if pivot < key then splitSteps pivot left else splitSteps pivot right

theorem split_steps_le [LT K] [DecidableLT K] (pivot : K) (tree : Tree K) :
    splitSteps pivot tree ≤ tree.height + 1 := by
  induction tree with
  | empty => exact Nat.le_refl _
  | node key p c left right ihLeft ihRight =>
    simp only [splitSteps, height]
    split
    · have h := Nat.le_max_left left.height right.height
      omega
    · have h := Nat.le_max_right left.height right.height
      omega

def mergeSteps (left right : Tree K) : Nat :=
  match left, right with
  | .empty, _ => 1
  | _, .empty => 1
  | .node kl pl cl ll lr, .node kr pr cr rl rr =>
    1 + if pr < pl then mergeSteps lr (.node kr pr cr rl rr)
                    else mergeSteps (.node kl pl cl ll lr) rl
termination_by left.slots + right.slots
decreasing_by all_goals simp [slots]; omega

theorem merge_steps_le (left right : Tree K) :
    mergeSteps left right ≤ left.height + right.height + 1 := by
  induction left, right using mergeSteps.induct with
  | case1 right => rw [mergeSteps]; simp [height]
  | case2 left nonempty => cases left <;> simp [mergeSteps, height]
  | case3 kl pl cl ll lr kr pr cr rl rr ihLeft ihRight =>
    rw [mergeSteps]
    split
    · have h := Nat.le_max_right ll.height lr.height
      simp only [height] at ihLeft ⊢
      omega
    · have h := Nat.le_max_left rl.height rr.height
      simp only [height] at ihRight ⊢
      omega

def insertSteps [LT K] [DecidableLT K] (key : K) (priority : UInt64) : Tree K → Nat
  | .empty => 1
  | .node old p c left right =>
    1 + if p < priority then splitSteps key (.node old p c left right)
        else if key < old then insertSteps key priority left else insertSteps key priority right

theorem insert_steps_le [LT K] [DecidableLT K] (key : K) (priority : UInt64) (tree : Tree K) :
    insertSteps key priority tree ≤ tree.height + 2 := by
  induction tree with
  | empty => simp [insertSteps, height]
  | node old p c left right ihLeft ihRight =>
    simp only [insertSteps]
    split
    · have h := split_steps_le key (Tree.node old p c left right)
      omega
    · simp only [height]
      split
      · have h := Nat.le_max_left left.height right.height
        omega
      · have h := Nat.le_max_right left.height right.height
        omega

def eraseSteps [LT K] [DecidableLT K] [DecidableEq K] (key : K) : Tree K → Nat
  | .empty => 1
  | .node old _ _ left right =>
    1 + if key = old then mergeSteps left right
        else if key < old then eraseSteps key left else eraseSteps key right

theorem erase_steps_le [LT K] [DecidableLT K] [DecidableEq K] (key : K) (tree : Tree K) :
    eraseSteps key tree ≤ 2 * tree.height + 1 := by
  induction tree with
  | empty => simp [eraseSteps, height]
  | node old p c left right ihLeft ihRight =>
    simp only [eraseSteps, height]
    have leftMax := Nat.le_max_left left.height right.height
    have rightMax := Nat.le_max_right left.height right.height
    split
    · have h := merge_steps_le left right
      omega
    · split <;> omega

end Proofs.Cpp.TreeMultiset.Tree
