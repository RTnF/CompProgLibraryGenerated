import Proofs.Cpp.Gen.GraphList

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListFindCycle

variable {E : Type} [Inhabited E] [Field "from" E Int]

/-- The parent edges, read from the current stack level back to the ancestor. -/
def parentsBack (parents : Array E) (spine : Nat → Int) (first : Nat) : Nat → List E
  | 0 => []
  | d + 1 => get parents (spine (first + (d + 1))) :: parentsBack parents spine first d

/-- This is the body of the generated loop that follows parent edges. -/
def collectStep (parents : Array E) (target : Int) (_ : Unit) (s : Array E × Int) :
    M (ForInStep (Array E × Int)) := do
  tick
  if !(decide (s.2 ≠ target)) then
    return .done (s.1, s.2)
  tick
  return .yield (s.1.push (get parents s.2), Field.get (member := "from") (get parents s.2))

/-- Along the active path, the reconstruction loop pushes each exact parent edge once and stops at
its ancestor. The last tick belongs to the iteration that reaches the ancestor. -/
theorem collect_parents (parents : Array E) (spine : Nat → Int) (first depth : Nat)
    (distinct : ∀ d, 0 < d → d ≤ depth → spine (first + d) ≠ spine first)
    (parent_from : ∀ d, d < depth →
      Field.get (member := "from") (get parents (spine (first + (d + 1)))) = spine (first + d))
    (available : Nat) (enough : depth < available) (edges : Array E) (c : Nat) :
    (loopFuel available (edges, spine (first + depth)) (collectStep parents (spine first))).run c =
      some ((edges ++ (parentsBack parents spine first depth).toArray, spine first), c + 2 * depth + 1) := by
  induction depth generalizing available edges c with
  | zero =>
    cases available with
    | zero => omega
    | succ n =>
      simp only [Nat.add_zero, parentsBack, Nat.mul_zero]
      rw [loopFuel]
      have hstep : collectStep parents (spine first) () (edges, spine first) = (do
          tick
          pure (.done (edges, spine first))) := by
        simp [collectStep]
      rw [hstep]
      rfl
  | succ d ih =>
    cases available with
    | zero => omega
    | succ n =>
      have hne := distinct (d + 1) (by omega) (by omega)
      have hprev := parent_from d (by omega)
      have hclock : c + 1 + 1 + 2 * d + 1 = c + 2 * (d + 1) + 1 := by omega
      rw [loopFuel]
      have hstep : collectStep parents (spine first) () (edges, spine (first + (d + 1))) = (do
          tick
          tick
          pure (.yield
            (edges.push (get parents (spine (first + (d + 1)))),
              Field.get (member := "from") (get parents (spine (first + (d + 1))))))) := by
        simp [collectStep, hne]
      rw [hstep]
      change (loopFuel n
        (edges.push (get parents (spine (first + (d + 1)))),
          Field.get (member := "from") (get parents (spine (first + (d + 1))))) _).run (c + 1 + 1) = _
      rw [hprev, ih (fun k hp hk => distinct k hp (by omega)) (fun k hk => parent_from k (by omega))
        n (by omega), hclock]
      simp [parentsBack]

omit [Field "from" E Int] in
@[simp] theorem parentsBack_length (parents : Array E) (spine : Nat → Int) (first depth : Nat) :
    (parentsBack parents spine first depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ d ih => simp [parentsBack, ih]

omit [Field "from" E Int] in
theorem parentsBack_mem (parents : Array E) (spine : Nat → Int) (first depth : Nat) (e : E) :
    e ∈ parentsBack parents spine first depth ↔
      ∃ d, d < depth ∧ e = get parents (spine (first + (d + 1))) := by
  induction depth with
  | zero => simp [parentsBack]
  | succ d ih =>
    simp only [parentsBack, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨d, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      by_cases hl : k < d
      · exact .inr ⟨k, hl, h⟩
      · have : k = d := by omega
        subst k
        exact .inl h

/-- The first `len` vertices of a stack slice, from ancestor to descendant. -/
def stackSlice (spine : Nat → Int) (first : Nat) : Nat → List Int
  | 0 => []
  | len + 1 => stackSlice spine first len ++ [spine (first + len)]

theorem stackSlice_head (spine : Nat → Int) (first len : Nat) :
    stackSlice spine first (len + 1) = spine first :: stackSlice spine (first + 1) len := by
  induction len with
  | zero => simp [stackSlice]
  | succ d ih =>
    rw [stackSlice, ih, stackSlice]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem mem_stackSlice (spine : Nat → Int) (first len : Nat) (v : Int) :
    v ∈ stackSlice spine first len ↔ ∃ i, i < len ∧ spine (first + i) = v := by
  induction len with
  | zero => simp [stackSlice]
  | succ d ih =>
    rw [stackSlice, List.mem_append, ih, List.mem_singleton]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨d, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases hi' : i < d
      · exact .inl ⟨i, hi', rfl⟩
      · have : i = d := by omega
        subst i
        exact .inr rfl

theorem stackSlice_nodup (spine : Nat → Int) (first len : Nat)
    (hinj : ∀ i j, i < len → j < len → spine (first + i) = spine (first + j) → i = j) :
    (stackSlice spine first len).Nodup := by
  induction len with
  | zero => simp [stackSlice]
  | succ d ih =>
    rw [stackSlice, List.nodup_append]
    refine ⟨ih (fun i j hi hj => hinj i j (by omega) (by omega)), by simp, ?_⟩
    intro v hv w hw heq
    have hvd := heq.trans (List.mem_singleton.mp hw)
    obtain ⟨i, hi, hvi⟩ := (mem_stackSlice spine first d v).mp hv
    have := hinj i d (by omega) (by omega) (hvi.trans hvd)
    omega

/-- Reversing the recorded edges gives the original stack slice in order, closed by the back edge. -/
theorem reconstruction_endpoints [Field "to" E Int] (parents : Array E) (spine : Nat → Int)
    (first depth : Nat) (back : E)
    (hfrom : Field.get (member := "from") back = spine (first + depth))
    (hto : Field.get (member := "to") back = spine first)
    (parent_ends : ∀ d, d < depth →
      Field.get (member := "from") (get parents (spine (first + (d + 1)))) = spine (first + d) ∧
      Field.get (member := "to") (get parents (spine (first + (d + 1)))) = spine (first + (d + 1))) :
    let es := (back :: parentsBack parents spine first depth).reverse
    es.map (Field.get (member := "from")) = stackSlice spine first (depth + 1) ∧
    es.map (Field.get (member := "to")) = stackSlice spine (first + 1) depth ++ [spine first] := by
  have hp : ∀ k, k ≤ depth →
      (parentsBack parents spine first k).reverse.map (Field.get (member := "from")) = stackSlice spine first k ∧
      (parentsBack parents spine first k).reverse.map (Field.get (member := "to")) = stackSlice spine (first + 1) k := by
    intro k hk
    induction k with
    | zero => simp [parentsBack, stackSlice]
    | succ d ih =>
      obtain ⟨hf, ht⟩ := ih (by omega)
      obtain ⟨hpf, hpt⟩ := parent_ends d (by omega)
      simp [parentsBack, List.reverse_cons, hf, ht, hpf, hpt, stackSlice, Nat.add_comm, Nat.add_left_comm]
  obtain ⟨hf, ht⟩ := hp depth (Nat.le_refl _)
  simp [List.reverse_cons, hf, ht, hfrom, hto, stackSlice]

end Proofs.Cpp.ListFindCycle
