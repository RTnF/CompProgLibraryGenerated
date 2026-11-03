import Proofs.UfRootScalarPeak
import Proofs.UfSameScalarPeak
import Proofs.UfSizeScalarPeak
import Proofs.UfUniteScalarPeak
import Proofs.UfCounterScalarPeak
import Proofs.UfReceiverValues

namespace Proofs.UfReceiverScalarPeak
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver
open Proofs.DoublingNested (i32)

theorem call_peak (fuel : Nat) (s out : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) (result : Ret)
    (actual : call fuel s layout op = .finished (out,result)) :
    ∃ init, prepare s op.program.parameters (arguments layout++op.extra) = some init ∧
      out.scalars.peak ≤ max init.scalars.peak
        ((Proofs.DoublingCall.callerP s).length+12-s.scalars.baseMemory+100) := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  cases op with
  | root a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    exact Proofs.UfRootScalarPeak.root_scalar_peak_actual s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) allowed fuel out result actual
  | same a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    exact Proofs.UfSameScalarPeak.same_scalar_peak_actual s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
      a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
      fuel out result actual
  | size a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    exact Proofs.UfSizeScalarPeak.size_scalar_peak_actual s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.math.weights inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) allowed fuel out result actual
  | unite a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    exact Proofs.UfUniteScalarPeak.unite_scalar_peak_actual s inv.ok cb count inv.countCell inv.writable ps rank inv.math
      inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
      a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
      fuel out result actual
  | numGroups =>
    have small := inv.math.length
    have nvalid := Proofs.VectorSumCall.i32_valid (ps.length : Int) (by omega) (by omega)
    exact Proofs.UfCounterScalarPeak.counter_scalar_peak_actual s inv.ok cb count inv.countCell inv.writable ps inv.items
      (by omega) inv.bufferValid inv.limit inv.owner (nExpr layout) ps.length rfl rfl inv.n_value nvalid fuel out result actual

theorem step_peak (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ init fuel out vec nextCount nextRank answer,
      prepare s op.program.parameters (arguments layout++op.extra) = some init ∧
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      out.work ≤ s.work+Proofs.UfTraceWork.budget ps.length ∧
      out.scalars.peak ≤ max init.scalars.peak
        ((Proofs.DoublingCall.callerP s).length+12-s.scalars.baseMemory+100) := by
  obtain ⟨fuel,out,vec,nextCount,nextRank,answer,ran,strong,length,work⟩ :=
    Proofs.UfTraceWork.step_work s layout ps count rank represented op allowed
  obtain ⟨init,prep,peak⟩ := call_peak fuel s out layout ps count rank represented.1 op allowed (.scalar answer) ran
  exact ⟨init,fuel,out,vec,nextCount,nextRank,answer,prep,ran,strong,length,work,peak⟩

end Proofs.UfReceiverScalarPeak
