import Proofs.BeatsCtorBase
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
set_option maxRecDepth 100000

abbrev CtUpdc0_20 (o : Nat) (REST : Command) : Command := REST
abbrev CtUpdc0_19 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 10)))) (CtUpdc0_20 o REST)
abbrev CtUpdc0_18 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable s64 (o + 10)) (.variable s64 (o + 11))) (.sequence (.scope (.sequence (.primitive (.assign (o + 18) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc0_19 o REST)
abbrev CtUpdc0_17 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .gt (.variable s64 (o + 10)) (.variable s64 (o + 11))) (.sequence (.scope (.sequence (.primitive (.assign (o + 17) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc0_18 o REST)
abbrev CtUpdc0_16 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 10)) (.variable s64 (o + 11))) (.sequence (.scope (.sequence (.primitive (.assign (o + 16) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc0_17 o REST)
abbrev CtUpdc0_15 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc0_16 o REST)
abbrev CtUpdc0_14 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc0_15 o REST)
abbrev CtUpdc0_13 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc0_14 o REST)
abbrev CtUpdc0_12 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc0_13 o REST)
abbrev CtUpdc0_11 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc0_12 o REST)
abbrev CtUpdc0_10 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc0_11 o REST)
abbrev CtUpdc0_9 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc0_10 o REST)
abbrev CtUpdc0_8 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc0_9 o REST)
abbrev CtUpdc0_7 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc0_8 o REST)
abbrev CtUpdc0_6 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 7))) (.literal i32 (2))))) (CtUpdc0_7 o REST)
abbrev CtUpdc0_5 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 7))) (.literal i32 (1))))) (CtUpdc0_6 o REST)
abbrev CtUpdc0_4 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 4)))) (CtUpdc0_5 o REST)
abbrev CtUpdc0_3 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 1)))) (CtUpdc0_4 o REST)
abbrev CtUpdc0_2 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 0)))) (CtUpdc0_3 o REST)
abbrev CtUpdc0_1 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 14) (.cast u64 (.variable i32 (o + 2)))))) (CtUpdc0_2 o REST)
abbrev CtUpdc0_0 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 2) i32 (.binary i32 .sub (.variable i32 (o + 2)) (.literal i32 (1))))) (CtUpdc0_1 o REST)
abbrev CtUpdc0 (o : Nat) (REST : Command) : Command := CtUpdc0_0 o REST
abbrev CtUpdc1_40 (o : Nat) (REST : Command) : Command := REST
abbrev CtUpdc1_39 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc1_40 o REST)
abbrev CtUpdc1_38 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc1_39 o REST)
abbrev CtUpdc1_37 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc1_38 o REST)
abbrev CtUpdc1_36 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc1_37 o REST)
abbrev CtUpdc1_35 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc1_36 o REST)
abbrev CtUpdc1_34 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 9)))))) (CtUpdc1_35 o REST)
abbrev CtUpdc1_33 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 8)))))) (CtUpdc1_34 o REST)
abbrev CtUpdc1_32 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 21)))) (CtUpdc1_33 o REST)
abbrev CtUpdc1_31 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 20)))) (CtUpdc1_32 o REST)
abbrev CtUpdc1_30 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 19)))) (CtUpdc1_31 o REST)
abbrev CtUpdc1_29 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 21)) (.variable s64 (o + 22))) (.sequence (.scope (.sequence (.primitive (.assign (o + 21) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_30 o REST)
abbrev CtUpdc1_28 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 17)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 22) s64 (.variable s64 (o + 12)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_29 o REST)
abbrev CtUpdc1_27 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 13)))) (CtUpdc1_28 o REST)
abbrev CtUpdc1_26 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 17)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 21) s64 (.variable s64 (o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_27 o REST)
abbrev CtUpdc1_25 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 16)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 21) s64 (.variable s64 (o + 10)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_26 o REST)
abbrev CtUpdc1_24 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 12)))) (CtUpdc1_25 o REST)
abbrev CtUpdc1_23 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 18)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 20) s64 (.binary s64 .add (.variable s64 (o + 14)) (.variable s64 (o + 15))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_24 o REST)
abbrev CtUpdc1_22 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 16)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 20) s64 (.variable s64 (o + 15)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_23 o REST)
abbrev CtUpdc1_21 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 14)))) (CtUpdc1_22 o REST)
abbrev CtUpdc1_20 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 16)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 19) s64 (.variable s64 (o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc1_21 o REST)
abbrev CtUpdc1 (o : Nat) (REST : Command) : Command := CtUpdc1_20 o REST
abbrev CtUpdc2_59 (o : Nat) (REST : Command) : Command := REST
abbrev CtUpdc2_58 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 34)))) (CtUpdc2_59 o REST)
abbrev CtUpdc2_57 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 33)))) (CtUpdc2_58 o REST)
abbrev CtUpdc2_56 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (o + 7))) (.variable s64 (o + 32)))) (CtUpdc2_57 o REST)
abbrev CtUpdc2_55 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 35)) (.variable s64 (o + 34))) (.sequence (.scope (.sequence (.primitive (.assign (o + 34) s64 (.variable s64 (o + 35)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_56 o REST)
abbrev CtUpdc2_54 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 29)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 35) s64 (.variable s64 (o + 25)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_55 o REST)
abbrev CtUpdc2_53 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 26)))) (CtUpdc2_54 o REST)
abbrev CtUpdc2_52 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 30)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 34) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_53 o REST)
abbrev CtUpdc2_51 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 29)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 34) s64 (.variable s64 (o + 24)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_52 o REST)
abbrev CtUpdc2_50 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 25)))) (CtUpdc2_51 o REST)
abbrev CtUpdc2_49 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 31)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 33) s64 (.binary s64 .add (.variable s64 (o + 27)) (.variable s64 (o + 28))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_50 o REST)
abbrev CtUpdc2_48 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 30)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 33) s64 (.variable s64 (o + 28)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_49 o REST)
abbrev CtUpdc2_47 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 27)))) (CtUpdc2_48 o REST)
abbrev CtUpdc2_46 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 30)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 32) s64 (.variable s64 (o + 24)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_47 o REST)
abbrev CtUpdc2_45 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 23)))) (CtUpdc2_46 o REST)
abbrev CtUpdc2_44 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable s64 (o + 23)) (.variable s64 (o + 24))) (.sequence (.scope (.sequence (.primitive (.assign (o + 31) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_45 o REST)
abbrev CtUpdc2_43 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .gt (.variable s64 (o + 23)) (.variable s64 (o + 24))) (.sequence (.scope (.sequence (.primitive (.assign (o + 30) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_44 o REST)
abbrev CtUpdc2_42 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 23)) (.variable s64 (o + 24))) (.sequence (.scope (.sequence (.primitive (.assign (o + 29) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtUpdc2_43 o REST)
abbrev CtUpdc2_41 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc2_42 o REST)
abbrev CtUpdc2_40 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtUpdc2_41 o REST)
abbrev CtUpdc2 (o : Nat) (REST : Command) : Command := CtUpdc2_40 o REST
abbrev CtUpdBody (o : Nat) : Command := CtUpdc0 o (CtUpdc1 o (CtUpdc2 o (Sk)))

def ul1 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def ul2 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def ul3 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def ul4 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def ul5 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def ul6 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }


end Proofs.BeatsExec
