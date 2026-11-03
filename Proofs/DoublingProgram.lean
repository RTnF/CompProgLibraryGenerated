import Proofs.DoublingConstruct

namespace Proofs.DoublingPrologue
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested
open Proofs.CppState (Cell)

abbrev declNStmt : NStmt := .declare i32 false eN

abbrev bodyCmd : Command :=
  .sequence (.primitive (.check ePos)) (.sequence (.primitive (.check eMax))
    (.sequence (.primitive declNStmt) (.sequence assertScope (.sequence bitWidthCall
      (.sequence (.primitive declW) (.sequence (.primitive consStmt) (.sequence (.primitive assignStmt)
        (.sequence loopsPhase (.sequence (.primitive (.retVector 5)) (.primitive .skip))))))))))

theorem body_eq : DoublingNestedInstance.doubling.body = bodyCmd := rfl

theorem capOf (F : Fixed) (ok : FixedOK F) {sc : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PS F sc rw0 S cells binds slots) (hc : cells.length ≤ 5) (hb : binds.length ≤ 5) :
    liveS S+40 ≤ F.SPB := by
  have := ps.live_eq
  have hB := ok.base
  have spb := ok.spb
  omega

theorem _root_.Proofs.DoublingNested.Done.mono_work {F : Fixed} {sc L0 Wd Wd' Td : Nat} {S : NState} (d : Done F sc L0 Wd Td S) (le : Wd ≤ Wd') :
    Done F sc L0 Wd' Td S := { d with scalarWork := Nat.le_trans d.scalarWork le }

abbrev retStmt : NStmt := .retVector 5

-- The whole body of `doubling`: from the entry state to the returned table.
theorem body_run (F : Fixed) (ok : FixedOK F) (hv : F.vbuf.items = F.items.map Value.integer)
    {rw0 : List Bool} {L0 W T0 : Nat} (S : NState)
    (hrw : F.rw = rw0 ++ [true] ++ List.replicate F.w false) (hw1 : 1 ≤ F.w)
    (hw : F.w = Proofs.BitWidthU64.width F.K.toNat) (hK0 : 0 < F.K) (hK : F.K < 2^64)
    (hvn : F.vbuf.items.length = F.n) (space : L0+F.w+F.n*F.w+3 ≤ F.TPB)
    (ps : PS F F.sc rw0 S [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots) (vf : VF F L0 T0 S.frame)
    (cb : Cb F W S) :
    RunsTo bodyCmd S fun step => step.returned = some (.vector F.R (.vector atom)) ∧ step.breaking = false ∧
      ∃ D, step.state = D.charge 1 0 ∧
        Done F F.sc L0 (W+F.n*100+990+2+(F.w-1)*(60*F.n+200)+5) (T0+F.w+1+F.n+1+(F.w-1)*(2*F.n+1)) D := by
  have nS := ok.nSmall
  have hL : L0 ≤ F.TPB := by omega
  have cap0 := capOf F ok ps (by simp) (by simp)
  -- E1
  obtain ⟨S1,run1,ps1,fr1,cb1⟩ := e1_step F S hK0 hK ps cb (by omega)
  have vf1 : VF F L0 T0 S1.frame := vf.of_eq fr1
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  -- E2
  obtain ⟨S2,run2,ps2,fr2,cb2⟩ := e2_step F S1 (by omega) ps1 vf1 cb1 (by have := capOf F ok ps1 (by simp) (by simp); omega)
  have vf2 : VF F L0 T0 S2.frame := vf1.of_eq fr2
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  -- E3
  obtain ⟨S3,run3,ps3,fr3,cb3⟩ := e3_step F S2 hvn nS ps2 vf2 cb2 (by have := capOf F ok ps2 (by simp) (by simp); omega)
  have vf3 : VF F L0 T0 S3.frame := vf2.of_eq fr3
  apply RunsTo.seq
  apply RunsTo.primitive run3
  refine ⟨rfl,rfl,?_⟩
  -- the assertion scope
  have hsc3 : S3.scope = F.sc := ps3.scope
  have asserts := assert_scope F ok hv S3 hL hsc3 ps3 vf3 cb3
    (by have := capOf F ok ps3 (by simp) (by simp); omega)
  apply RunsTo.seq
  refine asserts.mono ?_
  intro st4 ⟨nr,nb,ps4,vf4,cb4⟩
  refine ⟨nr,nb,?_⟩
  generalize st4.state = S4 at ps4 vf4 cb4 ⊢
  -- the scalar call
  obtain ⟨S5,run5,ps5,fr5,cb5⟩ := invoke_step F ok S4 (Int.le_of_lt hK0) hK hw ps4 cb4
    (by have := capOf F ok ps4 (by simp [cells2]) (by simp [binds2]); omega)
  have vf5 : VF F L0 T0 S5.frame := vf4.of_eq fr5
  apply RunsTo.seq
  refine ⟨81,⟨S5,none,false⟩,run5,rfl,rfl,?_⟩
  -- E6
  obtain ⟨S6,run6,ps6,fr6,cb6⟩ := declW_step F ok S5 ps5 cb5
    (by have := capOf F ok ps5 (by simp [cells3w,cells2]) (by simp [binds3w,binds2]); omega)
  have vf6 : VF F L0 T0 S6.frame := vf5.of_eq fr6
  apply RunsTo.seq
  apply RunsTo.primitive run6
  refine ⟨rfl,rfl,?_⟩
  -- E7
  obtain ⟨S7,run7,inv7⟩ := construct_step F ok S6 hrw hw1 hv space ps6 vf6 cb6 vf6.work
    (by have := capOf F ok ps6 (by simp [cells4,cells3w,cells2]) (by simp [binds4,binds3w,binds2]); omega)
  apply RunsTo.seq
  apply RunsTo.primitive run7
  refine ⟨rfl,rfl,?_⟩
  -- E8
  obtain ⟨S8,run8,inv8⟩ := assign_row0 F ok S7 hv hw1 space inv7
    (by have := liveS_shRet inv7.shape; have hB := ok.base; have spb := ok.spb; omega)
  apply RunsTo.seq
  apply RunsTo.primitive run8
  refine ⟨rfl,rfl,?_⟩
  -- the loops and the return
  apply RunsTo.seq
  refine (loops_phase F ok (Nat.le_refl _) hw1 inv8).mono ?_
  intro st ⟨nr,nb,done⟩
  refine ⟨nr,nb,?_⟩
  have run : retStmt.run st.state = some ⟨st.state.charge 1 0,some (.vector F.R (.vector atom)),false⟩ := by
    simp [NStmt.run,done.ctx.slot,done.ctx.binding]
  apply RunsTo.sequence
  apply RunsTo.primitive run
  exact Or.inl ⟨Or.inl rfl,rfl,rfl,st.state,rfl,done.mono_work (by omega)⟩

end Proofs.DoublingPrologue
