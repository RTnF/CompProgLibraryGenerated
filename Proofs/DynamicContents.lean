import Proofs.MultiVecDynamic

namespace Proofs.DynamicContents
open Proofs.CppScalar Proofs.CppRootModel

-- Contents omit allocation IDs, epochs, capacities and resource counters.
inductive Contents where
  | flat (ty : Ty) (scope : Nat) (values : List Int)
  | rows (ty : Ty) (scope : Nat) (values : List (List Int))
  deriving DecidableEq, Repr

def erase : View → Contents
  | .flat ty sc vs => .flat ty sc vs
  | .rows ty sc _ _ vs => .rows ty sc vs

abbrev ContentsHeap := Nat → Option Contents

def eraseHeap (h : Heap) : ContentsHeap := fun root => (h root).map erase

def putContents (h : ContentsHeap) (root : Nat) (v : Contents) : ContentsHeap :=
  fun owner => if owner = root then some v else h owner

theorem erase_put (h : Heap) (root : Nat) (v : View) :
    eraseHeap (put h root v) = putContents (eraseHeap h) root (erase v) := by
  funext owner
  by_cases same : owner = root <;> simp [eraseHeap,put,putContents,same]

def appendRoot (h : ContentsHeap) (root : Nat) (ty : Ty) : Option ContentsHeap := do
  let .rows t sc vs ← h root | none
  if t = ty then some (putContents h root (.rows t sc (vs ++ [[]]))) else none

def appendChild (h : ContentsHeap) (root : Nat) (ty : Ty) (k : Nat) (x : Int) : Option ContentsHeap := do
  let .rows t sc vs ← h root | none
  let old ← vs[k]?
  if t = ty ∧ ty.valid x = true then
    some (putContents h root (.rows t sc (vs.set k (old ++ [x]))))
  else none

theorem appendRoot_erased (h : Heap) (root : Nat) (ty : Ty) (sc : Nat)
    (ids ids' : List Nat) (epoch epoch' : Nat) (vs : List (List Int))
    (lookup : h root = some (.rows ty sc ids epoch vs)) :
    appendRoot (eraseHeap h) root ty =
      some (eraseHeap (put h root (.rows ty sc ids' epoch' (vs ++ [[]])))) := by
  simp [appendRoot,eraseHeap,lookup,erase,erase_put]

theorem appendChild_erased (h : Heap) (root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch k : Nat) (vs : List (List Int)) (old : List Int) (x : Int)
    (lookup : h root = some (.rows ty sc ids epoch vs)) (found : vs[k]? = some old)
    (valid : ty.valid x = true) :
    appendChild (eraseHeap h) root ty k x =
      some (eraseHeap (put h root (.rows ty sc ids epoch (vs.set k (old ++ [x]))))) := by
  simp [appendChild,eraseHeap,lookup,erase,found,valid,erase_put]

end Proofs.DynamicContents
