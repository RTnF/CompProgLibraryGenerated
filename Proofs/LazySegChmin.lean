import Proofs.SegmentTreeExec
import Proofs.LazySegMath
import Proofs.Generated.LazySegmentTree

namespace Proofs.LazySegChmin
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.SegTreeMath Proofs.LazySegMath
open Proofs.SegmentTreeExec (mx maxMon s64_bounds)

/-- `min(f, x)` written as the C++ does: `r = x; if (f < x) r = f;`. -/
def mi (f x : Int) : Int := if f < x then f else x

/-- The action "chmin" over the maximum monoid of `long long`. -/
def chminMon : LMon where
  toMon := maxMon
  Fv := fun x => s64.valid x = true
  fid := 9223372036854775807
  comp := mi
  mp := mi
  fid_v := by decide
  comp_v := by
    intro f g hf hg
    unfold mi
    split <;> assumption
  mp_v := by
    intro f x hf hx
    unfold mi
    split <;> assumption
  mp_op := by
    intro f a b hf ha hb
    show mi f (mx a b) = mx (mi f a) (mi f b)
    unfold mi mx
    split_ifs <;> omega
  mp_comp := by
    intro f g x hf hg hx
    unfold mi
    split_ifs <;> omega
  mp_id := by
    intro x hx
    have := s64_bounds x hx
    unfold mi
    split_ifs <;> omega
  comp_assoc := by
    intro f g h hf hg hh
    unfold mi
    split_ifs <;> omega
  comp_idl := by
    intro g hg
    have := s64_bounds g hg
    unfold mi
    split_ifs <;> omega
  comp_idr := by
    intro f hf
    have := s64_bounds f hf
    unfold mi
    split_ifs <;> omega

end Proofs.LazySegChmin
