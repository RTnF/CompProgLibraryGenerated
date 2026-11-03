import Proofs.BeatsExecL0
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

abbrev UpdLoopc0_20 (o : Nat) (REST : Command) : Command := REST
abbrev UpdLoopc0_19 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 14)))) (UpdLoopc0_20 o REST)
abbrev UpdLoopc0_18 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable s64 (o + 14)) (.variable s64 (o + 15))) (.sequence (.scope (.sequence (.primitive (.assign (o + 22) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc0_19 o REST)
abbrev UpdLoopc0_17 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .gt (.variable s64 (o + 14)) (.variable s64 (o + 15))) (.sequence (.scope (.sequence (.primitive (.assign (o + 21) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc0_18 o REST)
abbrev UpdLoopc0_16 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 14)) (.variable s64 (o + 15))) (.sequence (.scope (.sequence (.primitive (.assign (o + 20) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc0_17 o REST)
abbrev UpdLoopc0_15 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc0_16 o REST)
abbrev UpdLoopc0_14 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc0_15 o REST)
abbrev UpdLoopc0_13 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc0_14 o REST)
abbrev UpdLoopc0_12 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc0_13 o REST)
abbrev UpdLoopc0_11 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc0_12 o REST)
abbrev UpdLoopc0_10 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc0_11 o REST)
abbrev UpdLoopc0_9 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc0_10 o REST)
abbrev UpdLoopc0_8 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc0_9 o REST)
abbrev UpdLoopc0_7 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc0_8 o REST)
abbrev UpdLoopc0_6 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 11))) (.literal i32 (2))))) (UpdLoopc0_7 o REST)
abbrev UpdLoopc0_5 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 11))) (.literal i32 (1))))) (UpdLoopc0_6 o REST)
abbrev UpdLoopc0_4 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 8)))) (UpdLoopc0_5 o REST)
abbrev UpdLoopc0_3 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 1)))) (UpdLoopc0_4 o REST)
abbrev UpdLoopc0_2 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 0)))) (UpdLoopc0_3 o REST)
abbrev UpdLoopc0_1 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 14) (.cast u64 (.variable i32 (o + 7)))))) (UpdLoopc0_2 o REST)
abbrev UpdLoopc0_0 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 7) i32 (.binary i32 .sub (.variable i32 (o + 7)) (.literal i32 (1))))) (UpdLoopc0_1 o REST)
abbrev UpdLoopc0 (o : Nat) (REST : Command) : Command := UpdLoopc0_0 o REST
abbrev UpdLoopc1_40 (o : Nat) (REST : Command) : Command := REST
abbrev UpdLoopc1_39 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc1_40 o REST)
abbrev UpdLoopc1_38 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc1_39 o REST)
abbrev UpdLoopc1_37 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc1_38 o REST)
abbrev UpdLoopc1_36 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc1_37 o REST)
abbrev UpdLoopc1_35 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc1_36 o REST)
abbrev UpdLoopc1_34 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 13)))))) (UpdLoopc1_35 o REST)
abbrev UpdLoopc1_33 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 12)))))) (UpdLoopc1_34 o REST)
abbrev UpdLoopc1_32 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 25)))) (UpdLoopc1_33 o REST)
abbrev UpdLoopc1_31 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 24)))) (UpdLoopc1_32 o REST)
abbrev UpdLoopc1_30 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 23)))) (UpdLoopc1_31 o REST)
abbrev UpdLoopc1_29 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 25)) (.variable s64 (o + 26))) (.sequence (.scope (.sequence (.primitive (.assign (o + 25) s64 (.variable s64 (o + 26)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_30 o REST)
abbrev UpdLoopc1_28 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 21)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 26) s64 (.variable s64 (o + 16)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_29 o REST)
abbrev UpdLoopc1_27 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 17)))) (UpdLoopc1_28 o REST)
abbrev UpdLoopc1_26 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 21)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 25) s64 (.variable s64 (o + 15)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_27 o REST)
abbrev UpdLoopc1_25 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 20)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 25) s64 (.variable s64 (o + 14)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_26 o REST)
abbrev UpdLoopc1_24 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 16)))) (UpdLoopc1_25 o REST)
abbrev UpdLoopc1_23 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 22)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 24) s64 (.binary s64 .add (.variable s64 (o + 18)) (.variable s64 (o + 19))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_24 o REST)
abbrev UpdLoopc1_22 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 20)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 24) s64 (.variable s64 (o + 19)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_23 o REST)
abbrev UpdLoopc1_21 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 18)))) (UpdLoopc1_22 o REST)
abbrev UpdLoopc1_20 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 20)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 23) s64 (.variable s64 (o + 15)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc1_21 o REST)
abbrev UpdLoopc1 (o : Nat) (REST : Command) : Command := UpdLoopc1_20 o REST
abbrev UpdLoopc2_59 (o : Nat) (REST : Command) : Command := REST
abbrev UpdLoopc2_58 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 38)))) (UpdLoopc2_59 o REST)
abbrev UpdLoopc2_57 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 37)))) (UpdLoopc2_58 o REST)
abbrev UpdLoopc2_56 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (o + 11))) (.variable s64 (o + 36)))) (UpdLoopc2_57 o REST)
abbrev UpdLoopc2_55 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 39)) (.variable s64 (o + 38))) (.sequence (.scope (.sequence (.primitive (.assign (o + 38) s64 (.variable s64 (o + 39)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_56 o REST)
abbrev UpdLoopc2_54 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 33)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 39) s64 (.variable s64 (o + 29)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_55 o REST)
abbrev UpdLoopc2_53 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 30)))) (UpdLoopc2_54 o REST)
abbrev UpdLoopc2_52 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 34)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 38) s64 (.variable s64 (o + 27)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_53 o REST)
abbrev UpdLoopc2_51 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 33)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 38) s64 (.variable s64 (o + 28)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_52 o REST)
abbrev UpdLoopc2_50 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 29)))) (UpdLoopc2_51 o REST)
abbrev UpdLoopc2_49 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 35)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 37) s64 (.binary s64 .add (.variable s64 (o + 31)) (.variable s64 (o + 32))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_50 o REST)
abbrev UpdLoopc2_48 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 34)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 37) s64 (.variable s64 (o + 32)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_49 o REST)
abbrev UpdLoopc2_47 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 31)))) (UpdLoopc2_48 o REST)
abbrev UpdLoopc2_46 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 34)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 36) s64 (.variable s64 (o + 28)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_47 o REST)
abbrev UpdLoopc2_45 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 27)))) (UpdLoopc2_46 o REST)
abbrev UpdLoopc2_44 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable s64 (o + 27)) (.variable s64 (o + 28))) (.sequence (.scope (.sequence (.primitive (.assign (o + 35) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_45 o REST)
abbrev UpdLoopc2_43 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .gt (.variable s64 (o + 27)) (.variable s64 (o + 28))) (.sequence (.scope (.sequence (.primitive (.assign (o + 34) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_44 o REST)
abbrev UpdLoopc2_42 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable s64 (o + 27)) (.variable s64 (o + 28))) (.sequence (.scope (.sequence (.primitive (.assign (o + 33) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (UpdLoopc2_43 o REST)
abbrev UpdLoopc2_41 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc2_42 o REST)
abbrev UpdLoopc2_40 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (UpdLoopc2_41 o REST)
abbrev UpdLoopc2 (o : Nat) (REST : Command) : Command := UpdLoopc2_40 o REST
abbrev UpdLoopBody (o : Nat) : Command := UpdLoopc0 o (UpdLoopc1 o (UpdLoopc2 o (Sk)))

def uu1 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def uu2 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def uu3 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def uu4 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def uu5 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def uu6 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }


end Proofs.BeatsExec
