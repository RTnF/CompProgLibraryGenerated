import Proofs.UfConstructorSpace
import Proofs.UfUniformPeak

namespace Proofs.UfConstructedPeak
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop Proofs.CppNestedEval
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame
open Proofs.DoublingNested (i32)

def scalarEnvelope (s : NState) (nodes : Nat) : Nat :=
  max s.scalars.peak (liveS s+s.frame.bindings.length+nodes+117)

def storageEnvelope (s : NState) (n : Nat) : Nat :=
  max s.frame.state.storage.peak (s.frame.state.liveSpace+n+2-s.frame.state.storage.baseSpace)

def envelope (s : NState) (n nodes : Nat) : Nat := max s.peak (scalarEnvelope s nodes+storageEnvelope s n)

theorem scalar_resident (s out : NState) (nodes : Nat) (live : liveS out = liveS s+4)
    (peak : out.scalars.peak ≤ scalarEnvelope s nodes) :
    out.scalars.peak ≤ max s.scalars.peak (liveS out+s.frame.bindings.length+nodes+113) := by
  have budgetEq : liveS out+s.frame.bindings.length+nodes+113 = liveS s+s.frame.bindings.length+nodes+117 := by
    rw [live]
    omega
  rw [budgetEq]
  exact peak

theorem storage_resident (s out : NState) (n : Nat) (live : out.frame.state.liveSpace = s.frame.state.liveSpace+n+1)
    (peak : out.frame.state.storage.peak ≤ storageEnvelope s n) :
    out.frame.state.storage.peak ≤ max s.frame.state.storage.peak (out.frame.state.liveSpace+1-s.frame.state.storage.baseSpace) := by
  rw [live]
  simpa only [storageEnvelope,Nat.add_assoc] using peak

theorem receiver_envelopes (s r : NState) (n nodes : Nat)
    (scalar : r.scalars.peak ≤ max s.scalars.peak (liveS s+s.frame.bindings.length+nodes+12))
    (storage : r.frame.state.storage.peak ≤ storageEnvelope s n)
    (scalarLive : liveS r = liveS s+4) (vectorLive : r.frame.state.liveSpace = s.frame.state.liveSpace+n+1)
    (base : r.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace)
    (bindings : r.frame.bindings.length = s.frame.bindings.length+1) :
    max r.scalars.peak (Proofs.UfUniformScalarPeak.budget r) ≤ scalarEnvelope s nodes ∧
      Proofs.CppStoragePeak.bound r ≤ storageEnvelope s n := by
  constructor
  · unfold Proofs.UfUniformScalarPeak.budget scalarEnvelope
    rw [scalarLive,bindings]
    apply max_le
    · exact scalar.trans (max_le_max (Nat.le_refl _) (by omega))
    · apply le_trans ?_ (Nat.le_max_right _ _)
      omega
  · unfold Proofs.CppStoragePeak.bound
    rw [vectorLive,base]
    apply max_le storage
    unfold storageEnvelope
    simpa only [Nat.add_assoc] using Nat.le_max_right s.frame.state.storage.peak
      (s.frame.state.liveSpace+n+2-s.frame.state.storage.baseSpace)

theorem sized (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int))
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Strong out (layoutOf caller) vec count rank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+en.nodes+n+30+ops.length*Proofs.UfTraceWork.budget n ∧
      liveS out = liveS caller+4 ∧ out.frame.state.liveSpace = caller.frame.state.liveSpace+n+1 ∧
      CallEffects receiver out ∧ out.scalars.peak ≤ scalarEnvelope caller en.nodes ∧
      out.frame.state.storage.peak ≤ storageEnvelope caller n ∧ out.peak ≤ envelope caller n en.nodes := by
  obtain ⟨receiver,constructed,strong,ctorWork,scalarLive,vectorLive,ctorPeak,ctorScalar,ctorStorage,ctorBase,ctorBindings⟩ :=
    Proofs.UfConstructorSpace.construct_sized_components caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalStrong,length,fuelsLength,answersLength,work,effects,scalarPeak,storagePeak,outerPeak⟩ :=
    Proofs.UfUniformPeak.calls_peak ops receiver (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) strong (by simpa using allowed)
  simp only [List.length_replicate] at length work
  have envelopes := receiver_envelopes caller receiver n en.nodes ctorScalar ctorStorage scalarLive vectorLive ctorBase ctorBindings
  have ctorEnvelope : receiver.peak ≤ envelope caller n en.nodes := by
    apply ctorPeak.trans
    apply max_le_max (Nat.le_refl _)
    apply Nat.add_le_add
    · unfold scalarEnvelope
      exact max_le_max (Nat.le_refl _) (by omega)
    · exact Nat.le_refl _
  have components : Proofs.UfUniformPeak.components receiver ≤ scalarEnvelope caller en.nodes+storageEnvelope caller n :=
    Nat.add_le_add envelopes.1 envelopes.2
  have finalPeak : out.peak ≤ envelope caller n en.nodes := outerPeak.trans
    (max_le ctorEnvelope (components.trans (Nat.le_max_right _ _)))
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalStrong,length,fuelsLength,answersLength,
    Nat.le_trans work (Nat.add_le_add_right ctorWork _),effects.scalarLive.trans scalarLive,effects.headers.live.trans vectorLive,
    effects,scalarPeak.trans envelopes.1,storagePeak.trans envelopes.2,finalPeak⟩

theorem default (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed 0) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Strong out (layoutOf caller) vec count rank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+12+ops.length*Proofs.UfTraceWork.budget 0 ∧
      liveS out = liveS caller+4 ∧ out.frame.state.liveSpace = caller.frame.state.liveSpace+1 ∧
      CallEffects receiver out ∧ out.scalars.peak ≤ scalarEnvelope caller 0 ∧
      out.frame.state.storage.peak ≤ storageEnvelope caller 0 ∧ out.peak ≤ envelope caller 0 0 := by
  obtain ⟨receiver,constructed,strong,ctorWork,scalarLive,vectorLive,ctorPeak,ctorScalar,ctorStorage,ctorBase,ctorBindings⟩ :=
    Proofs.UfConstructorSpace.construct_default_components caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalStrong,length,fuelsLength,answersLength,work,effects,scalarPeak,storagePeak,outerPeak⟩ :=
    Proofs.UfUniformPeak.calls_peak ops receiver (layoutOf caller) [] 0 (fun _ => 0) strong allowed
  have storage : receiver.frame.state.storage.peak ≤ storageEnvelope caller 0 := by
    apply ctorStorage.trans
    apply max_le_max (Nat.le_refl _)
    apply Nat.sub_le_sub_right
    omega
  have scalar : receiver.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+0+12) :=
    ctorScalar.trans (max_le_max (Nat.le_refl _) (by omega))
  have envelopes := receiver_envelopes caller receiver 0 0 scalar storage scalarLive (by simpa using vectorLive) ctorBase ctorBindings
  have ctorEnvelope : receiver.peak ≤ envelope caller 0 0 := by
    apply ctorPeak.trans
    apply max_le_max (Nat.le_refl _)
    apply Nat.add_le_add
    · unfold scalarEnvelope
      exact max_le_max (Nat.le_refl _) (by omega)
    · unfold storageEnvelope
      apply max_le_max (Nat.le_refl _)
      apply Nat.sub_le_sub_right
      omega
  have components : Proofs.UfUniformPeak.components receiver ≤ scalarEnvelope caller 0+storageEnvelope caller 0 :=
    Nat.add_le_add envelopes.1 envelopes.2
  have finalPeak : out.peak ≤ envelope caller 0 0 := outerPeak.trans
    (max_le ctorEnvelope (components.trans (Nat.le_max_right _ _)))
  have workFinal : out.work ≤ caller.work+12+ops.length*Proofs.UfTraceWork.budget 0 := by
    simpa only [List.length_nil] using Nat.le_trans work (Nat.add_le_add_right ctorWork _)
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalStrong,length,fuelsLength,answersLength,
    workFinal,effects.scalarLive.trans scalarLive,effects.headers.live.trans vectorLive,
    effects,scalarPeak.trans envelopes.1,storagePeak.trans envelopes.2,finalPeak⟩

end Proofs.UfConstructedPeak
