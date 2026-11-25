import Proofs.Cpp.Prelude

/-! # `std::priority_queue` and `std::stack` (docs/translation.md)

A priority queue is the list of its elements (the multiset; the order of the list is not observable). With the
comparison `comp` of the queue (`std::less`: `a < b`; `std::greater`: `b < a`), `top` is the first element `x` of
the list such that no later better element replaces it (`pqBest`): for a strict total order whose equivalent
elements are equal (integers, pairs of integers) it is the unique maximum under `comp`, which is the element that
the C++ queue returns. `push` and `pop` cost `log2 size + 1` steps, `top`/`empty`/`size` one step (the documented
complexities). A stack is the list with its top first; each operation costs one step. -/

namespace Proofs.Cpp

abbrev PQ (α : Type) := List α
abbrev Stack (α : Type) := List α

/-- `std::pair`'s `operator<` from the `<` of the components: `a.1 < b.1 || (!(b.1 < a.1) && a.2 < b.2)`. -/
def pairLt {α β : Type} (lt₁ : α → α → Bool) (lt₂ : β → β → Bool) (a b : α × β) : Bool :=
  lt₁ a.1 b.1 || (!lt₁ b.1 a.1 && lt₂ a.2 b.2)

/-- The position of the best element under `comp`: a later element replaces the current one when
`comp current later`. -/
def pqBestIdx {α : Type} (comp : α → α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => ((xs.zipIdx 1).foldl (fun (b : α × Nat) y => if comp b.1 y.1 then y else b) (x, 0)).2

def pqBest {α : Type} (comp : α → α → Bool) (q : List α) : Option α := q[pqBestIdx comp q]?

def pqPush {α : Type} (q : PQ α) (x : α) : M (PQ α) := do
  tickN (Nat.log2 (q.length + 1) + 1)
  return q ++ [x]

/-- `top()` of a nonempty queue (the empty queue is a precondition violation: failure). -/
def pqTop {α : Type} (comp : α → α → Bool) (q : PQ α) : M α := do
  tick
  match pqBest comp q with
  | some x => return x
  | none => failure

/-- `pop()`: removes one copy of the top. -/
def pqPop {α : Type} (comp : α → α → Bool) (q : PQ α) : M (PQ α) := do
  tickN (Nat.log2 q.length + 1)
  if q.isEmpty then failure else return q.eraseIdx (pqBestIdx comp q)

def stackPush {α : Type} (s : Stack α) (x : α) : M (Stack α) := do
  tick
  return x :: s

def stackTop {α : Type} (s : Stack α) : M α := do
  tick
  match s with
  | x :: _ => return x
  | [] => failure

def stackPop {α : Type} (s : Stack α) : M (Stack α) := do
  tick
  match s with
  | _ :: rest => return rest
  | [] => failure

end Proofs.Cpp

namespace Proofs.Cpp

theorem bestFold_inv {α : Type} (comp : α → α → Bool) (hirr : ∀ a, comp a a = false)
    (htrans : ∀ a b c, comp a b = true → comp b c = true → comp a c = true)
    (q : List α) (xs : List (α × Nat)) (b : α × Nat) (seen : List α)
    (hxs : ∀ y ∈ xs, q[y.2]? = some y.1) (hb : q[b.2]? = some b.1) (hseen : ∀ z ∈ seen, comp b.1 z = false) :
    let r := xs.foldl (fun (b : α × Nat) y => if comp b.1 y.1 then y else b) b
    q[r.2]? = some r.1 ∧ (∀ z ∈ seen, comp r.1 z = false) ∧ ∀ y ∈ xs, comp r.1 y.1 = false := by
  induction xs generalizing b seen with
  | nil => exact ⟨hb, hseen, by simp⟩
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have hy := hxs y (by simp)
    have hys : ∀ z ∈ ys, q[z.2]? = some z.1 := fun z hz => hxs z (by simp [hz])
    by_cases hc : comp b.1 y.1 = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih y (y.1 :: seen) hys hy (by
        intro z hz
        simp at hz
        rcases hz with rfl | hz
        · exact hirr _
        · cases h : comp y.1 z
          · rfl
          · have := htrans _ _ _ hc h; rw [hseen z hz] at this; cases this)
      refine ⟨h1, fun z hz => h2 z (by simp [hz]), ?_⟩
      intro w hw; simp at hw
      rcases hw with rfl | hw
      · exact h2 _ (by simp)
      · exact h3 _ hw
    · have hc' : comp b.1 y.1 = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih b (y.1 :: seen) hys hb (by
        intro z hz; simp at hz; rcases hz with rfl | hz
        · exact hc'
        · exact hseen z hz)
      refine ⟨h1, fun z hz => h2 z (by simp [hz]), ?_⟩
      intro w hw; simp at hw
      rcases hw with rfl | hw
      · exact h2 _ (by simp)
      · exact h3 _ hw

/-- The top of a nonempty queue is an element at the position `pqBestIdx` that no element beats. -/
theorem pqBest_spec {α : Type} (comp : α → α → Bool) (hirr : ∀ a, comp a a = false)
    (htrans : ∀ a b c, comp a b = true → comp b c = true → comp a c = true) (q : List α) (hq : q ≠ []) :
    ∃ x, q[pqBestIdx comp q]? = some x ∧ pqBest comp q = some x ∧ ∀ y ∈ q, comp x y = false := by
  cases q with
  | nil => exact absurd rfl hq
  | cons x xs =>
    have hxs : ∀ y ∈ xs.zipIdx 1, (x :: xs)[y.2]? = some y.1 := by
      intro y hy
      obtain ⟨a, i⟩ := y
      obtain ⟨h1, h2, h3⟩ := List.mem_zipIdx hy
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp at h2 h3 ⊢
      rw [List.getElem?_eq_getElem (by omega), h3]
    obtain ⟨h1, h2, h3⟩ := bestFold_inv comp hirr htrans (x :: xs) (xs.zipIdx 1) (x, 0) [x] hxs (by simp)
      (by simp [hirr])
    refine ⟨_, h1, ?_, ?_⟩
    · simp only [pqBest, pqBestIdx]; exact h1
    · intro y hy
      simp at hy
      rcases hy with rfl | hy
      · exact h2 _ (by simp)
      · obtain ⟨i, hi⟩ := List.getElem_of_mem hy
        have := h3 (y, i + 1) (by
          rw [List.mem_iff_getElem?]
          obtain ⟨hlt, hget⟩ := hi
          refine ⟨i, ?_⟩
          rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hlt, hget]
          rw [Option.map_some, Nat.add_comm])
        exact this

end Proofs.Cpp
