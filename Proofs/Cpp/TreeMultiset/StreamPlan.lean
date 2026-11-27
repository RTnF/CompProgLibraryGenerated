import Proofs.Cpp.TreeMultiset.StreamRepeat

open Proofs Proofs.Cpp

namespace Proofs.Cpp.TreeMultiset

def printBatch (key : K) (count : Nat) : List (Option K) :=
  List.replicate count (some key) ++ [none]

def printPlan {K : Type} [LinearOrder K] (lo hi : K) : Tree K → List (Option K)
  | .empty => [none, none]
  | .node key _ count left right =>
    [none, none] ++ (if lo < key then printPlan lo hi left else []) ++
      (if lo ≤ key ∧ key ≤ hi then printBatch key count else []) ++
      (if key < hi then printPlan lo hi right else [])

theorem printPlan_keys {K : Type} [LinearOrder K] (lo hi : K) (tree : Tree K) :
    (printPlan lo hi tree).filterMap id = tree.closedKeys lo hi := by
  have copy (key : K) (count : Nat) :
      (List.replicate count (some key)).filterMap id = List.replicate count key := by
    induction count with
    | zero => rfl
    | succ count ih => simp [List.replicate_succ, ih]
  induction tree with
  | empty => rfl
  | node key p count left right ihLeft ihRight =>
    by_cases l : lo < key <;> by_cases r : key < hi <;> by_cases selected : lo ≤ key ∧ key ≤ hi <;>
      simp [printPlan, printBatch, Tree.closedKeys, l, r, selected, copy, ihLeft, ihRight, List.append_assoc]

theorem printPlan_length {K : Type} [LinearOrder K] (lo hi : K) (tree : Tree K) :
    (printPlan lo hi tree).length ≤ 2 + 5 * tree.slots + (tree.closedKeys lo hi).length := by
  induction tree with
  | empty => simp [printPlan, Tree.slots, Tree.closedKeys]
  | node key p count left right ihLeft ihRight =>
    by_cases l : lo < key <;> by_cases r : key < hi <;> by_cases selected : lo ≤ key ∧ key ≤ hi <;>
      simp [printPlan, printBatch, Tree.slots, Tree.closedKeys, l, r, selected] <;> omega

section Output

variable {K : Type} [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar]

def runPrintPlan (events : List (Option K)) (stream : Cpp.OStream) : Cpp.M Cpp.OStream :=
  events.foldlM (fun output event => do
    tick
    match event with
    | none => pure output
    | some key => printLine output key) stream

@[simp] theorem run_plan_empty (stream : Cpp.OStream) :
    runPrintPlan ([] : List (Option K)) stream = pure stream := rfl

theorem run_plan_advance (events : List (Option K)) (stream : Cpp.OStream) :
    runPrintPlan (none :: events) stream = (do
      tick
      runPrintPlan events stream) := by
  simp [runPrintPlan]

theorem run_plan_append (first second : List (Option K)) (stream : Cpp.OStream) :
    runPrintPlan (first ++ second) stream = (do
      let out ← runPrintPlan first stream
      runPrintPlan second out) := by
  simp [runPrintPlan, List.foldlM_append]

theorem run_plan_repeat (key : K) (count : Nat) (stream : Cpp.OStream) :
    runPrintPlan (printBatch key count) stream = repeatPrint key count stream := by
  unfold printBatch
  induction count generalizing stream with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, repeatPrint]
    unfold runPrintPlan
    rw [List.foldlM_cons]
    simp only [bind_assoc]
    congr 1
    funext tickResult
    congr 1
    funext output
    exact ih output

theorem run_plan_work (events : List (Option K)) (lineCost : Nat)
    (bounded : ∀ stream (key : K) start, ∃ out stop, (printLine stream key).run start = some (out, stop) ∧
      stop ≤ start + lineCost) (stream : Cpp.OStream) (start : Nat) :
    ∃ out stop, (runPrintPlan events stream).run start = some (out, stop) ∧
      stop ≤ start + events.length + lineCost * (events.filterMap id).length := by
  induction events generalizing stream start with
  | nil => exact ⟨stream, start, rfl, by simp⟩
  | cons item tail ih =>
    have first : Cpp.tick.run start = some ((), start + 1) := rfl
    cases item with
    | none =>
      obtain ⟨out, stop, run, bound⟩ := ih stream (start + 1)
      refine ⟨out, stop, ?_, ?_⟩
      · simpa [runPrintPlan, List.foldlM_cons, StateT.run_bind, first] using run
      · simp; omega
    | some key =>
      obtain ⟨middle, afterLine, written, budget⟩ := bounded stream key (start + 1)
      obtain ⟨out, stop, run, bound⟩ := ih middle afterLine
      refine ⟨out, stop, ?_, ?_⟩
      · simpa [runPrintPlan, List.foldlM_cons, StateT.run_bind, first, written] using run
      · simp [Nat.mul_add]; omega

end Output
end Proofs.Cpp.TreeMultiset
