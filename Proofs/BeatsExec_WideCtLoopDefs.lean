import Proofs.BeatsExecL1
import Proofs.BeatsCtorBase
import Proofs.BeatsWideExec
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec

abbrev WideCtLoopc0_4 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc0_3 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable i32 (_o + 4)) (.variable i32 (_o + 5))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 6) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc0_4 _o REST)
abbrev WideCtLoopc0_2 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (WideCtLoopc0_3 _o REST)
abbrev WideCtLoopc0_1 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc0_2 _o REST)
abbrev WideCtLoopc0_0 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc0_1 _o REST)
abbrev WideCtLoopc0 (_o : Nat) (REST : Command) : Command := WideCtLoopc0_0 _o REST
abbrev WideCtLoopc1_8 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc1_7 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (WideCtLoopc1_8 _o REST)
abbrev WideCtLoopc1_6 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (_o + 6)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (_o + 7)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 8) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc1_7 _o REST)
abbrev WideCtLoopc1_5 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (WideCtLoopc1_6 _o REST)
abbrev WideCtLoopc1_4 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.cast s64 (.binary i32 .sub (.variable i32 (_o + 5)) (.variable i32 (_o + 4)))))) (WideCtLoopc1_5 _o REST)
abbrev WideCtLoopc1 (_o : Nat) (REST : Command) : Command := WideCtLoopc1_4 _o REST
abbrev WideCtLoopc2_12 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc2_11 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 6) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 10)))) (WideCtLoopc2_12 _o REST)
abbrev WideCtLoopc2_10 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 6)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 10) s64 (.variable s64 (_o + 7)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc2_11 _o REST)
abbrev WideCtLoopc2_9 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 6) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc2_10 _o REST)
abbrev WideCtLoopc2_8 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (_o + 6)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (_o + 7)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 9) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc2_9 _o REST)
abbrev WideCtLoopc2 (_o : Nat) (REST : Command) : Command := WideCtLoopc2_8 _o REST
abbrev WideCtLoopc3_16 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc3_15 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc3_16 _o REST)
abbrev WideCtLoopc3_14 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc3_15 _o REST)
abbrev WideCtLoopc3_13 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc3_14 _o REST)
abbrev WideCtLoopc3_12 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 15) (.cast u64 (.variable i32 (_o + 4)))))) (WideCtLoopc3_13 _o REST)
abbrev WideCtLoopc3 (_o : Nat) (REST : Command) : Command := WideCtLoopc3_12 _o REST
abbrev WideCtLoopc4_20 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc4_19 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 12) s64 (.variable s64 (_o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc4_20 _o REST)
abbrev WideCtLoopc4_18 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc4_19 _o REST)
abbrev WideCtLoopc4_17 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc4_18 _o REST)
abbrev WideCtLoopc4_16 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (_o + 3)))))) (WideCtLoopc4_17 _o REST)
abbrev WideCtLoopc4 (_o : Nat) (REST : Command) : Command := WideCtLoopc4_16 _o REST
abbrev WideCtLoopc5_24 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc5_23 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 16) s64 (.cast s64 (.literal i32 (1))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc5_24 _o REST)
abbrev WideCtLoopc5_22 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 15) s64 (.variable s64 (_o + 0)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc5_23 _o REST)
abbrev WideCtLoopc5_21 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 14) s64 (.unary s64 .neg (.variable s64 (_o + 0))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc5_22 _o REST)
abbrev WideCtLoopc5_20 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 13) s64 (.variable s64 (_o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc5_21 _o REST)
abbrev WideCtLoopc5 (_o : Nat) (REST : Command) : Command := WideCtLoopc5_20 _o REST
abbrev WideCtLoopc6_28 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc6_27 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 14)))) (WideCtLoopc6_28 _o REST)
abbrev WideCtLoopc6_26 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 13)))) (WideCtLoopc6_27 _o REST)
abbrev WideCtLoopc6_25 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 12)))) (WideCtLoopc6_26 _o REST)
abbrev WideCtLoopc6_24 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 17) s64 (.cast s64 (.literal i32 (1))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc6_25 _o REST)
abbrev WideCtLoopc6 (_o : Nat) (REST : Command) : Command := WideCtLoopc6_24 _o REST
abbrev WideCtLoopc7_32 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc7_31 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.divrem i32 false (.binary i32 .add (.variable i32 (_o + 4)) (.variable i32 (_o + 5))) (.literal i32 (2))))) (WideCtLoopc7_32 _o REST)
abbrev WideCtLoopc7_30 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 17)))) (WideCtLoopc7_31 _o REST)
abbrev WideCtLoopc7_29 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 16)))) (WideCtLoopc7_30 _o REST)
abbrev WideCtLoopc7_28 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (_o + 3))) (.variable s64 (_o + 15)))) (WideCtLoopc7_29 _o REST)
abbrev WideCtLoopc7 (_o : Nat) (REST : Command) : Command := WideCtLoopc7_28 _o REST
abbrev WideCtLoopc8_36 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc8_35 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable u64 (_o + 19)))))) (WideCtLoopc8_36 _o REST)
abbrev WideCtLoopc8_34 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable u64 (_o + 19)))))) (WideCtLoopc8_35 _o REST)
abbrev WideCtLoopc8_33 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare u64 true (.binary u64 .add (.binary u64 .mul (.literal u64 (2)) (.cast u64 (.variable i32 (_o + 3)))) (.literal u64 (2))))) (WideCtLoopc8_34 _o REST)
abbrev WideCtLoopc8_32 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare u64 true (.binary u64 .add (.binary u64 .mul (.literal u64 (2)) (.cast u64 (.variable i32 (_o + 3)))) (.literal u64 (1))))) (WideCtLoopc8_33 _o REST)
abbrev WideCtLoopc8 (_o : Nat) (REST : Command) : Command := WideCtLoopc8_32 _o REST
abbrev WideCtLoopc9_40 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc9_39 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 22) i32 (.variable i32 (_o + 18)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc9_40 _o REST)
abbrev WideCtLoopc9_38 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 21) i32 (.variable i32 (_o + 4)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc9_39 _o REST)
abbrev WideCtLoopc9_37 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable u64 (_o + 20)))))) (WideCtLoopc9_38 _o REST)
abbrev WideCtLoopc9_36 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable u64 (_o + 20)))))) (WideCtLoopc9_37 _o REST)
abbrev WideCtLoopc9 (_o : Nat) (REST : Command) : Command := WideCtLoopc9_36 _o REST
abbrev WideCtLoopc10_44 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc10_43 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 10) i32 (.cast u64 (.variable u64 (_o + 19))) (.variable i32 (_o + 22)))) (WideCtLoopc10_44 _o REST)
abbrev WideCtLoopc10_42 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 9) i32 (.cast u64 (.variable u64 (_o + 19))) (.variable i32 (_o + 21)))) (WideCtLoopc10_43 _o REST)
abbrev WideCtLoopc10_41 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 24) i32 (.variable i32 (_o + 5)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc10_42 _o REST)
abbrev WideCtLoopc10_40 (_o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (_o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (_o + 23) i32 (.variable i32 (_o + 18)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (WideCtLoopc10_41 _o REST)
abbrev WideCtLoopc10 (_o : Nat) (REST : Command) : Command := WideCtLoopc10_40 _o REST
abbrev WideCtLoopc11_48 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc11_47 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (_o + 2) i32 (.binary i32 .add (.variable i32 (_o + 2)) (.variable i32 (_o + 9))))) (WideCtLoopc11_48 _o REST)
abbrev WideCtLoopc11_46 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 14) i32 (.cast u64 (.variable i32 (_o + 2))) (.variable i32 (_o + 3)))) (WideCtLoopc11_47 _o REST)
abbrev WideCtLoopc11_45 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 10) i32 (.cast u64 (.variable u64 (_o + 20))) (.variable i32 (_o + 24)))) (WideCtLoopc11_46 _o REST)
abbrev WideCtLoopc11_44 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 9) i32 (.cast u64 (.variable u64 (_o + 20))) (.variable i32 (_o + 23)))) (WideCtLoopc11_45 _o REST)
abbrev WideCtLoopc11 (_o : Nat) (REST : Command) : Command := WideCtLoopc11_44 _o REST
abbrev WideCtLoopc12_49 (_o : Nat) (REST : Command) : Command := REST
abbrev WideCtLoopc12_48 (_o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (_o + 3) i32 (.binary i32 .add (.variable i32 (_o + 3)) (.literal i32 (1))))) (WideCtLoopc12_49 _o REST)
abbrev WideCtLoopc12 (_o : Nat) (REST : Command) : Command := WideCtLoopc12_48 _o REST
abbrev WideCtLoopBody (_o : Nat) : Command := WideCtLoopc0 _o (WideCtLoopc1 _o (WideCtLoopc2 _o (WideCtLoopc3 _o (WideCtLoopc4 _o (WideCtLoopc5 _o (WideCtLoopc6 _o (WideCtLoopc7 _o (WideCtLoopc8 _o (WideCtLoopc9 _o (WideCtLoopc10 _o (WideCtLoopc11 _o (WideCtLoopc12 _o (Sk)))))))))))))

def uw1 (s : BS) (idx : Nat) (a : Int) : BS := { s with len := s.len.set idx a }
def uw2 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def uw3 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def uw4 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def uw5 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }
def uw6 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def uw7 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def uw8 (s : BS) (idx : Nat) (a : Int) : BS := { s with lo := s.lo.set idx a }
def uw9 (s : BS) (idx : Nat) (a : Int) : BS := { s with hi := s.hi.set idx a }
def uw10 (s : BS) (idx : Nat) (a : Int) : BS := { s with lo := s.lo.set idx a }
def uw11 (s : BS) (idx : Nat) (a : Int) : BS := { s with hi := s.hi.set idx a }
def uw12 (s : BS) (idx : Nat) (a : Int) : BS := { s with ent := s.ent.set idx a }


end Proofs.BeatsExec
