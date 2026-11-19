import Proofs.Cpp.Gen.SegmentTree
import Proofs.Cpp.Gen.Monoid

/-! The searches of the generated SegmentTree model with MonoidMax (tests/test_segment_tree_search.py); the same
cases as tests/imports/segment_tree_search.cpp. -/

open Proofs.Cpp Proofs.Cpp.Gen

instance : NumericTraits "T" Int := intNumericTraits "T" 64 true
instance : StaticCall "e" (cp.MonoidMax Int) (cp.MonoidMax Int) := ⟨cp.MonoidMax.e⟩
instance : AdlCall2 "op" (cp.MonoidMax Int) (cp.MonoidMax Int) (cp.MonoidMax Int) :=
  ⟨cp.op_MonoidMax_MonoidMax_hidden⟩

structure Pred where
  k : Int
  mono : Bool

def emin : Int := -9223372036854775808

instance : Invoke1 Pred (cp.MonoidMax Int) Bool :=
  ⟨fun f x => pure (if x.x == emin then true else
    if f.mono then decide (x.x ≤ f.k) else ((x.x.tmod 3 + 3).tmod 3 != (f.k + 3).tmod 3))⟩

def step (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def main : IO Unit := do
  let mut s := 1
  for _ in [0:200] do
    s := step s
    let n := s % 30
    let mut v : Array (cp.MonoidMax Int) := #[]
    for _ in [0:n] do
      s := step s
      v := v.push ⟨((s % 21 : Nat) : Int) - 10⟩
    let some (st, _) := (cp.SegmentTree.init_vec v).run 0 | throw (IO.userError "init failed")
    for _ in [0:20] do
      s := step s
      let k : Int := ((s % 7 : Nat) : Int) - 3
      s := step s
      let mono := s % 2 == 1
      s := step s
      let a : Int := (s % (n + 1) : Nat)
      let f : Pred := ⟨k, mono⟩
      let some ((r, _), _) := (cp.SegmentTree.search_prod_right st a f).run 0 | throw (IO.userError "right failed")
      let some ((l, _), _) := (cp.SegmentTree.search_prod_left st a f).run 0 | throw (IO.userError "left failed")
      IO.println s!"{r} {l}"
