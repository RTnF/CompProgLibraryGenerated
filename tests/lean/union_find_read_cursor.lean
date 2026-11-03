
namespace UnionFindNormalModelChecks
example : UnionFindPublicCompat.Methods.UnionFind_unite = Proofs.UnionFindCandidateInstance.UnionFind_unite := rfl
example : UnionFindPublicCompat.Methods.UnionFind_same_2 = Proofs.UnionFindCandidateInstance.UnionFind_same := rfl
example : UnionFindPublicCompat.Methods.UnionFind_root = Proofs.UnionFindCandidateInstance.UnionFind_root := rfl
example : UnionFindPublicCompat.Methods.UnionFind_size_1 = Proofs.UnionFindCandidateInstance.UnionFind_size := rfl
example : UnionFindPublicCompat.Methods.UnionFind_num_groups_0 = Proofs.UnionFindCandidateInstance.UnionFind_num_groups := rfl
example : UnionFindPublicCompat.Methods.UnionFind_find_root.parameters =
  [.vector ⟨32,true,false⟩ false,.scalar ⟨32,true,false⟩ true false,
    .scalar ⟨32,true,false⟩ false true,.scalar ⟨32,true,false⟩ false true] := rfl
example : Proofs.UnionFindInstance.UnionFind_find_root.body = Proofs.UfReadCursor.body [] := rfl
end UnionFindNormalModelChecks

namespace UnionFindReadonlyModelChecks
open Proofs.UfReadCursor Proofs.UfRootCall Proofs.CppScalar Proofs.VecKitW Proofs.VecWrite
open Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr
open Proofs.CppState (Cell Binding)
open Proofs.DoublingNested

def commandAt : Nat → Command → Command
  | 0, .sequence first _ => first
  | n+1, .sequence _ rest => commandAt n rest
  | _, other => other

example (b0 b1 : Binding) : UnionFindPublicCompat.Methods.UnionFind_find_root.body = body [b0,b1] := rfl
example (bindings : List Binding) (length : bindings.length = 5) :
    commandAt 6 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body = loop bindings := by
  simp only [loop,condition,readCursor,iteration,assignCursor,length]
  rfl
example (bindings : List Binding) (length : bindings.length = 9) :
    commandAt 11 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body = loop bindings := by
  simp only [loop,condition,readCursor,iteration,assignCursor,length]
  rfl
example (bindings : List Binding) (length : bindings.length = 4) :
    commandAt 4 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body = loop bindings := by
  simp only [loop,condition,readCursor,iteration,assignCursor,length]
  rfl

example (P : List Cell) (b0 b1 : Binding) (ps : List Int) (rank : Nat → Nat)
    (forest : Forest ps rank) (length : ps.length < 2147483648) (a : Nat) (inside : a < ps.length)
    (fuel : Nat) (enough : rank a + 2 ≤ fuel) :
    ∃ (res : PRW) (r : Nat),
      pexecW i32 fuel UnionFindPublicCompat.Methods.UnionFind_find_root.body (cursor P [b0,b1] a) ps = some res ∧
      res.ret = some (r : Int) ∧ res.ps = cursor P [b0,b1] r ∧ res.vec = ps ∧
      Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
      res.cost ≤ 16 * rank a + 18 ∧ res.need ≤ P.length + [b0,b1].length + 20 ∧ res.wk = 0 :=
  body_run P [b0,b1] ps rank forest length a inside fuel enough

#guard (match pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_find_root.body
    (cursor [⟨i32,4⟩,⟨i32,4⟩] [⟨0,false⟩,⟨1,false⟩] 3) [-4,0,1,2] with
  | some r => r.ret == some 0 && r.vec == [-4,0,1,2] &&
      r.ps.mem.map (·.value) == [4,4,0] && r.ps.bs.map (·.writable) == [false,false,true]
  | none => false)
#guard (pexecW i32 1 UnionFindPublicCompat.Methods.UnionFind_find_root.body
    (cursor [] [⟨0,false⟩,⟨0,false⟩] 3) [-4,0,1,2]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_find_root.body
    (cursor [] [⟨0,false⟩,⟨0,false⟩] 4) [-4,0,1,2]).isNone
end UnionFindReadonlyModelChecks
