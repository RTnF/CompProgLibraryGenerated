import Proofs.UfFieldsSize

namespace Proofs.UfClassInvariant
open Proofs.DoublingNested Proofs.CppScalar Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfFieldsSize

noncomputable def roots (ps : List Int) : List Nat := by
  classical
  exact (List.range ps.length).filter fun r => decide (∃ w, ps[r]? = some w ∧ w < 0)

noncomputable def members (ps : List Int) (r : Nat) : List Nat := by
  classical
  exact (List.range ps.length).filter fun i => decide (Reach ps i r)

-- These lists enumerate each in-range index once, so length is cardinality.
noncomputable def component (ps : List Int) (a : Nat) : List Nat := by
  classical
  exact (List.range ps.length).filter fun i => decide (Proofs.UfFieldsSame.Connected ps i a)

theorem component_eq_members (ps : List Int) (a r : Nat) (reach : Reach ps a r)
    (root : ∃ w, ps[r]? = some w ∧ w < 0) : component ps a = members ps r := by
  classical
  unfold component members
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨z,iz,az,negative⟩
    have same : z=r := root_unique az reach negative root
    simpa [same] using iz
  · intro ir
    exact ⟨r,ir,reach,root⟩

theorem component_nodup (ps : List Int) (a : Nat) : (component ps a).Nodup := by
  classical
  exact List.Pairwise.filter _ List.nodup_range

structure Valid (ps : List Int) (groups : Int) (rank : Nat → Nat) : Prop where
  forest : Forest ps rank
  length : ps.length < 2147483648
  sizes : ∀ r w, ps[r]? = some w → w < 0 → w = -((members ps r).length : Int)
  count : groups = ((roots ps).length : Int)

theorem members_nodup (ps : List Int) (r : Nat) : (members ps r).Nodup := by
  classical
  exact List.Pairwise.filter _ List.nodup_range

theorem roots_nodup (ps : List Int) : (roots ps).Nodup := by
  classical
  exact List.Pairwise.filter _ List.nodup_range

theorem members_card_le (ps : List Int) (r : Nat) : (members ps r).length ≤ ps.length := by
  classical
  simpa [members] using List.length_filter_le (fun i => decide (Reach ps i r)) (List.range ps.length)

theorem roots_card_le (ps : List Int) : (roots ps).length ≤ ps.length := by
  classical
  simpa [roots] using List.length_filter_le (fun r => decide (∃ w, ps[r]? = some w ∧ w < 0)) (List.range ps.length)

theorem Valid.weights {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) : Weights ps := by
  intro r w found negative
  have size := valid.sizes r w found negative
  have bound := members_card_le ps r
  omega

theorem Valid.count_range {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) : 0 ≤ groups ∧ groups ≤ ps.length ∧ i32.valid groups = true := by
  have bound := roots_card_le ps
  have length := valid.length
  have count := valid.count
  refine ⟨by omega,by omega,?_⟩
  exact Proofs.VectorSumCall.i32_valid groups (by omega) (by omega)

theorem roots_compressed {ps vec : List Int} {a r : Nat} (compressed : Compressed ps vec a r) :
    roots vec = roots ps := by
  classical
  simp only [roots,compressed.length]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨w,found,negative⟩
    exact ⟨w,(negative_entry compressed w negative).mp found,negative⟩
  · rintro ⟨w,found,negative⟩
    exact ⟨w,(negative_entry compressed w negative).mpr found,negative⟩

theorem members_compressed {ps vec : List Int} {a r z : Nat} (compressed : Compressed ps vec a r)
    (root : ∃ w, ps[z]? = some w ∧ w < 0) : members vec z = members ps z := by
  classical
  simp only [members,compressed.length]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨reach_backward compressed,fun reach => root_forward compressed reach root⟩

theorem Valid.compressed {ps vec : List Int} {groups : Int} {rank : Nat → Nat} {a r : Nat}
    (valid : Valid ps groups rank) (compressed : Compressed ps vec a r) : Valid vec groups rank := by
  obtain ⟨w,found,negative⟩ := compressed.root
  have inside : r < ps.length := (List.getElem?_eq_some_iff.mp found).1
  have rootValid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by have := valid.length; omega)
  refine ⟨find_forest ps vec rank valid.forest a r compressed.reach inside compressed.root
    compressed.length compressed.entries rootValid,by rw [compressed.length]; exact valid.length,?_,?_⟩
  · intro z x found negative
    have old := (negative_entry compressed x negative).mp found
    rw [members_compressed compressed ⟨x,old,negative⟩]
    exact valid.sizes z x old negative
  · rw [roots_compressed compressed]
    exact valid.count

theorem Valid.size_value {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) {r : Nat} {w : Int} (found : ps[r]? = some w) (negative : w < 0) :
    -w = ((members ps r).length : Int) := by
  rw [valid.sizes r w found negative,neg_neg]

-- Mathematical representation initialized by the original constructor.
-- The C++ constructor execution still needs its separate generated-call proof.
def initial (n : Nat) : List Int := List.replicate n (-1)

theorem initial_reach (n i r : Nat) (inside : i < n) : Reach (initial n) i r ↔ r = i := by
  constructor
  · intro reach
    exact root_reach (initial n) i ⟨-1,by simp [initial,inside],by decide⟩ r reach
  · intro same
    subst r
    exact Reach.refl i

theorem initial_roots (n : Nat) : roots (initial n) = List.range n := by
  classical
  unfold roots
  rw [show (initial n).length = n from List.length_replicate]
  apply List.filter_eq_self.mpr
  intro i member
  have inside := List.mem_range.mp member
  simp only [decide_eq_true_eq]
  exact ⟨-1,by simp [initial,inside],by decide⟩

theorem initial_members (n r : Nat) (inside : r < n) : members (initial n) r = [r] := by
  classical
  unfold members
  rw [show (initial n).length = n from List.length_replicate]
  have sameFilter : (List.range n).filter (fun i => decide (Reach (initial n) i r)) =
      (List.range n).filter (· == r) := by
    apply List.filter_congr
    intro i member
    have bound := List.mem_range.mp member
    by_cases same : i=r
    · subst i
      simp [Reach.refl]
    · have notReach : ¬ Reach (initial n) i r := fun reach => same ((initial_reach n i r bound).mp reach).symm
      simp [notReach,same]
  rw [sameFilter,List.filter_beq,(List.nodup_range : (List.range n).Nodup).count_of_mem (List.mem_range.mpr inside)]
  rfl

theorem initial_valid (n : Nat) (length : n < 2147483648) : Valid (initial n) n (fun _ => 0) := by
  refine ⟨⟨?_,?_,?_⟩,by simpa [initial] using length,?_,?_⟩
  · intro x member
    have same : x = -1 := List.eq_of_mem_replicate member
    subst x
    decide
  · intro i p found nonneg
    have same : p = -1 := List.eq_of_mem_replicate (List.mem_of_getElem? found)
    omega
  · intro i p found nonneg
    have same : p = -1 := List.eq_of_mem_replicate (List.mem_of_getElem? found)
    omega
  · intro r w found negative
    have bound : r < n := by simpa [initial] using (List.getElem?_eq_some_iff.mp found).1
    have same : w = -1 := List.eq_of_mem_replicate (List.mem_of_getElem? found)
    rw [same,initial_members n r bound]
    simp
  · rw [initial_roots]
    simp

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.UfRootCall Proofs.UfFindCall
open Proofs.UfCompression Proofs.VectorFillCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall

open Proofs.VecKitW Proofs.PowModStep
open Proofs.UfInlineRoot Proofs.VecCapture Proofs.UfFieldsRoot


theorem size_card_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (valid : Valid ps count rank)
    (items : vbuf.items = ps.map Value.integer)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea : NExpr) (a : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some (ps.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (inside : a < ps.length) :
    ∃ Sinit fuel out, ∃ (r : Nat) (vec : List Int),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_size.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out,.scalar ((component ps a).length : Int)) ∧
      Compressed ps vec a r ∧ Valid vec count rank ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes) (90 * rank a+160) caller.scalars.memory (rank a) V vec := by
  obtain ⟨Sinit,fuel,out,r,w,vec,prep,call,found,negative,compressed,_,_,post⟩ :=
    Proofs.UfFieldsSize.size_call caller ok countBinding count cell writable ps rank valid.forest valid.weights
      items valid.length bvalid limit owner en ea a ns as_ nt at_ nv av inside
  have result := valid.size_value found negative
  rw [← component_eq_members ps a r compressed.reach ⟨w,found,negative⟩] at result
  rw [result] at call
  exact ⟨Sinit,fuel,out,r,vec,prep,call,compressed,valid.compressed compressed,post⟩

end Proofs.UfClassInvariant
