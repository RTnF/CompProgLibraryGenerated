import Proofs.UfReceiverTrace
import Proofs.CppCallUnique

namespace Proofs.UfScalarOther
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfFindCall
open Proofs.CppState (Cell Binding)
open Proofs.DoublingNested (i32)

theorem state_unique (s expected out : NState) (layout : Layout) (op : Operation)
    (first second : Nat) (known ret : Ret)
    (one : call first s layout op = .finished (expected,known))
    (two : call second s layout op = .finished (out,ret)) : expected = out := by
  exact congrArg Prod.fst (Proofs.CppCallUnique.call_unique op.program first second s
    (arguments layout++op.extra) (expected,known) (out,ret) one two)

theorem scalar_other (s out : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (cb nb : Binding)
    (inv : Inv s layout ps count rank buf cb nb) (op : Operation) (allowed : op.allowed ps.length)
    (fuel : Nat) (ret : Ret) (actual : call fuel s layout op = .finished (out,ret)) :
    ∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) →
      binding.address ≠ cb.address → out.scalarCell slot ty = some (binding,cell) := by
  cases op with
  | root a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,f,expected,r,vec,prep,ran,compressed,forest,recursive,post,ready,cells⟩ :=
      Proofs.UfRootReady.root_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
        inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
        rfl rfl rfl rfl inv.n_value (literal_value a av s) allowed
    have same := state_unique s expected out layout (.root a) f fuel _ ret ran actual
    intro slot ty binding cell found _
    rw [←same,cells]
    exact found
  | size a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,f,expected,r,w,vec,prep,ran,found,negative,compressed,forest,weights,post,ready,cells⟩ :=
      Proofs.UfSizeReady.size_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
        inv.math.weights inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
        rfl rfl rfl rfl inv.n_value (literal_value a av s) allowed
    have same := state_unique s expected out layout (.size a) f fuel _ ret ran actual
    intro slot ty binding cell found _
    rw [←same,cells]
    exact found
  | same a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,f,expected,r1,r2,middle,vec,prep,ran,c1,c2,forest,connected,post,ready,cells⟩ :=
      Proofs.UfSameReady.same_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
        inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
        a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
    have same := state_unique s expected out layout (.same a b) f fuel _ ret ran actual
    intro slot ty binding cell found _
    rw [←same,cells]
    exact found
  | unite a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,f,expected,r1,r2,middle,two,vec,prep,ran,c1,c2,finalEq,newValid,connected,
      bindings,base,post,ready,counter,other,aliases⟩ :=
      Proofs.UfUniteReady.unite_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
        inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
        a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
    have same := state_unique s expected out layout (.unite a b) f fuel _ ret ran actual
    rw [←same]
    exact other
  | numGroups =>
    obtain ⟨init,f,expected,prep,ran,bindings,base,post,ready,cells⟩ :=
      Proofs.UfCounterReady.num_groups_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
        inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) rfl rfl inv.n_value
    have same := state_unique s expected out layout .numGroups f fuel _ ret ran actual
    intro slot ty binding cell found _
    rw [←same,cells]
    exact found

end Proofs.UfScalarOther
