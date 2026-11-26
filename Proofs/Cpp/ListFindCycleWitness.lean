import Proofs.Cpp.ListFindCycleProjection
import Proofs.Cpp.ListFindCycleReconstruct

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv
open Proofs.LowlinkMultigraph (offsets endpoints)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

/-- The returned edge list has its original edge values and follows a nonempty simple directed cycle. -/
def CycleWitness (g : cp.ListGraph Cost E) (es : List E) : Prop :=
  ∃ (first : Int) (rest : List Int),
    es.map (Field.get (member := "from")) = first :: rest ∧
    es.map (Field.get (member := "to")) = rest ++ [first] ∧ (first :: rest).Nodup ∧
    ∀ e ∈ es, ∃ v, v < g.adj.size ∧ e ∈ edgesAt g v

theorem cycle_witness_of_active {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E}
    {st : FS} (active : Active g visited parents st) (valid : ValidGraph g)
    (inv : FInv g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) st)
    (j depth : Nat) (hstack : j + depth < st.sp) (back : E)
    (hback : back ∈ edgesAt g (st.Sk (j + depth)))
    (hto : Field.get (member := "to") back = (st.Sk j : Int)) :
    let spine := fun k => (st.Sk k : Int)
    CycleWitness g (back :: parentsBack parents spine j depth).reverse := by
  let spine := fun k => (st.Sk k : Int)
  have hin (k : Nat) (hk : k < st.sp) : st.Sk k < g.adj.size :=
    inv.c_lt _ (by have := inv.sk_gray k hk; omega)
  have hinj : ∀ x y, x < depth + 1 → y < depth + 1 →
      spine (j + x) = spine (j + y) → x = y := by
    intro x y hx hy he
    have hsk : st.Sk (j + x) = st.Sk (j + y) := by simp [spine] at he; exact he
    have := inv.sk_inj _ _ (by omega) (by omega) hsk
    omega
  have hparent (k : Nat) (hk : k < depth) := active.parent_endpoints valid inv
    (j := j + k) (by omega)
  have hend (k : Nat) (hk : k < depth) :
      let e := get parents (spine (j + (k + 1)))
      Field.get (member := "from") e = spine (j + k) ∧ Field.get (member := "to") e = spine (j + (k + 1)) := by
    simpa only [spine, Nat.add_assoc] using (hparent k hk).2
  have hfrom := (valid.row _ (hin _ hstack) back hback).1
  obtain ⟨hs, hd⟩ := reconstruction_endpoints parents spine j depth back hfrom hto hend
  rw [stackSlice_head] at hs
  have hnd := stackSlice_nodup spine j (depth + 1) hinj
  rw [stackSlice_head] at hnd
  refine ⟨spine j, stackSlice spine (j + 1) depth, hs, hd, hnd, ?_⟩
  intro edge he
  rw [List.mem_reverse, List.mem_cons] at he
  rcases he with rfl | he
  · exact ⟨_, hin _ hstack, hback⟩
  · obtain ⟨k, hk, rfl⟩ := (parentsBack_mem parents spine j depth edge).mp he
    exact ⟨st.Sk (j + k), hin _ (by omega), by
      simpa only [spine, Nat.add_assoc] using (hparent k hk).1⟩

end Proofs.Cpp.ListFindCycle
