namespace UnionFindReadQueryChecks
open Proofs.UfReadQueries Proofs.UfReadInline Proofs.UfRootCall
open Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite Proofs.VecKitW
open Proofs.DoublingNested Proofs.CppState

theorem size_body_eq : UnionFindPublicCompat.Methods.UnionFind_size_1_2.body = sizeBody := rfl
theorem same_body_eq : UnionFindPublicCompat.Methods.UnionFind_same_2_2.body = sameBody := rfl
theorem counter_body_eq : UnionFindPublicCompat.Methods.UnionFind_num_groups_0_2.body = counterBody := rfl

example (state : PS) (slots : state.bs.length = 3) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights vec) (n : Int) (nvalid : i32.valid n = true)
    (a : Nat) (inside : a < vec.length) (nv : penv1 state 2 i32 = some n)
    (av : penv1 state 3 i32 = some (a : Int)) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat) (w : Int), pexecW i32 fuel UnionFindPublicCompat.Methods.UnionFind_size_1_2.body state vec = some out ∧
      out.ret = some (-w) ∧ Reach vec a r ∧ r < vec.length ∧ vec[r]? = some w ∧ w < 0 ∧
      i32.valid (-w) = true ∧ out.vec = vec ∧ out.ps = inlineState state n r ∧
      out.cost ≤ 16 * rank a+40 ∧ out.need ≤ state.mem.length+state.bs.length+30 ∧ out.wk = 0 := by
  rw [size_body_eq]
  exact size_correct state slots vec rank forest length weights n nvalid a inside nv av fuel enough

example (state : PS) (slots : state.bs.length = 4) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (n : Int) (nvalid : i32.valid n = true) (a b : Nat) (ha : a < vec.length) (hb : b < vec.length)
    (nv : penv1 state 2 i32 = some n) (av : penv1 state 3 i32 = some (a : Int))
    (bv : penv1 state 4 i32 = some (b : Int)) (fuel : Nat) (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat), pexecW i32 fuel UnionFindPublicCompat.Methods.UnionFind_same_2_2.body state vec = some out ∧
      out.ret = some (if r1=r2 then 1 else 0) ∧ Reach vec a r1 ∧ Reach vec b r2 ∧
      r1 < vec.length ∧ r2 < vec.length ∧ (∃ w, vec[r1]? = some w ∧ w < 0) ∧
      (∃ w, vec[r2]? = some w ∧ w < 0) ∧ out.vec = vec ∧ out.ps = sameState state n r1 r2 ∧
      out.cost ≤ 16 * rank a+16 * rank b+74 ∧ out.need ≤ state.mem.length+state.bs.length+40 ∧ out.wk = 0 := by
  rw [same_body_eq]
  exact same_correct state slots vec rank forest length n nvalid a b ha hb nv av bv fuel fa fb

example (state : PS) (vec : List Int) (count : Int)
    (value : penv1 state 1 i32 = some count) (fuel : Nat) :
    pexecW i32 fuel UnionFindPublicCompat.Methods.UnionFind_num_groups_0_2.body state vec =
      some ⟨state,vec,some count,2,state.mem.length+state.bs.length+3,0⟩ := by
  rw [counter_body_eq]
  exact counter_correct state vec count value fuel


def sizeInput (n a : Int) : Proofs.StraightLine.PS :=
  ⟨[⟨i32,2⟩,⟨i32,n⟩,⟨i32,a⟩],[⟨0,false⟩,⟨1,true⟩,⟨2,true⟩]⟩
def sameInput (n a b : Int) : Proofs.StraightLine.PS :=
  ⟨[⟨i32,2⟩,⟨i32,n⟩,⟨i32,a⟩,⟨i32,b⟩],[⟨0,false⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩
#guard (match pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body
    (sizeInput 99 3) [-4,0,1,2] with
  | some out => out.ret == some 4 && out.vec == [-4,0,1,2] &&
      out.ps.mem.map (·.value) == [2,99,3,99,0,0] &&
      out.ps.bs.map (·.writable) == [false,true,true,true,true,true] && out.wk == 0
  | none => false)
#guard (match pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body
    (sameInput 99 1 3) [-2,0,-2,2] with
  | some out => out.ret == some 0 && out.vec == [-2,0,-2,2] &&
      out.ps.mem.take 4 == (sameInput 99 1 3).mem &&
      out.ps.bs.take 4 == (sameInput 99 1 3).bs && out.wk == 0
  | none => false)
#guard (match pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body
    (sameInput 99 1 0) [-2,0,-2,2] with
  | some out => out.ret == some 1 && out.vec == [-2,0,-2,2]
  | none => false)
#guard (pexecW i32 1 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body
  (sizeInput 99 3) [-4,0,1,2]).isNone
#guard (pexecW i32 1 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body
  (sameInput 99 3 0) [-4,0,1,2]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body (sizeInput 99 4) [-4,0,1,2]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body (sizeInput 99 (-1)) [-4,0,1,2]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body (sizeInput 0 0) []).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_size_1_2.body
  (sizeInput 1 0) [-2147483648]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body (sameInput 99 0 4) [-4,0,1,2]).isNone
#guard (pexecW i32 5 UnionFindPublicCompat.Methods.UnionFind_same_2_2.body (sameInput 0 0 0) []).isNone
#guard (match pexecW i32 0 UnionFindPublicCompat.Methods.UnionFind_num_groups_0_2.body
  (sizeInput 99 3) [] with
  | some out => out.ret == some 2 && out.ps.mem == (sizeInput 99 3).mem && out.vec == []
  | none => false)
end UnionFindReadQueryChecks
