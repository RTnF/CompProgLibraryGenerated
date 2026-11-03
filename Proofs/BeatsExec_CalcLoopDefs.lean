import Proofs.BeatsExecL1
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

abbrev CalcLoopc0_20 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc0_19 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 15)))) (CalcLoopc0_20 o REST)
abbrev CalcLoopc0_18 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 7)))) (CalcLoopc0_19 o REST)
abbrev CalcLoopc0_17 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.variable i32 (o + 1)))) (CalcLoopc0_18 o REST)
abbrev CalcLoopc0_16 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 0)))) (CalcLoopc0_17 o REST)
abbrev CalcLoopc0_15 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 14)) (.literal i32 (1))) (.binary bT .eq (.variable i32 (o + 2)) (.literal i32 (1)))) (.binary bT .lt (.variable s64 (o + 11)) (.variable s64 (o + 5)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 5) s64 (.variable s64 (o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_16 o REST)
abbrev CalcLoopc0_14 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 14)) (.literal i32 (1))) (.binary bT .eq (.variable i32 (o + 2)) (.literal i32 (0)))) (.binary bT .lt (.variable s64 (o + 5)) (.variable s64 (o + 10)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 5) s64 (.variable s64 (o + 10)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_15 o REST)
abbrev CalcLoopc0_13 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 12)) (.literal i32 (0))) (.binary bT .eq (.variable i32 (o + 14)) (.literal i32 (0)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 15) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_14 o REST)
abbrev CalcLoopc0_12 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc0_13 o REST)
abbrev CalcLoopc0_11 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 12)) (.literal i32 (0))) (.binary bT .eq (.variable i32 (o + 13)) (.literal i32 (1)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 14) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_12 o REST)
abbrev CalcLoopc0_10 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc0_11 o REST)
abbrev CalcLoopc0_9 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .le (.variable i32 (o + 3)) (.variable i32 (o + 8))) (.binary bT .le (.variable i32 (o + 9)) (.variable i32 (o + 4)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 13) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_10 o REST)
abbrev CalcLoopc0_8 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc0_9 o REST)
abbrev CalcLoopc0_7 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical false (.binary bT .le (.variable i32 (o + 4)) (.variable i32 (o + 8))) (.binary bT .le (.variable i32 (o + 9)) (.variable i32 (o + 3)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 12) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc0_8 o REST)
abbrev CalcLoopc0_6 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc0_7 o REST)
abbrev CalcLoopc0_5 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 7)))))) (CalcLoopc0_6 o REST)
abbrev CalcLoopc0_4 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 7)))))) (CalcLoopc0_5 o REST)
abbrev CalcLoopc0_3 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 13) (.cast u64 (.variable i32 (o + 6)))))) (CalcLoopc0_4 o REST)
abbrev CalcLoopc0_2 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 12) (.cast u64 (.variable i32 (o + 6)))))) (CalcLoopc0_3 o REST)
abbrev CalcLoopc0_1 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 11) (.cast u64 (.variable i32 (o + 6)))))) (CalcLoopc0_2 o REST)
abbrev CalcLoopc0_0 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 6) i32 (.binary i32 .sub (.variable i32 (o + 6)) (.literal i32 (1))))) (CalcLoopc0_1 o REST)
abbrev CalcLoopc0 (o : Nat) (REST : Command) : Command := CalcLoopc0_0 o REST
abbrev CalcLoopc1_40 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc1_39 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 8) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_40 o REST)
abbrev CalcLoopc1_38 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 7) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_39 o REST)
abbrev CalcLoopc1_37 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_38 o REST)
abbrev CalcLoopc1_36 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_37 o REST)
abbrev CalcLoopc1_35 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_36 o REST)
abbrev CalcLoopc1_34 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_35 o REST)
abbrev CalcLoopc1_33 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_34 o REST)
abbrev CalcLoopc1_32 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc1_33 o REST)
abbrev CalcLoopc1_31 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 18))) (.literal i32 (2))))) (CalcLoopc1_32 o REST)
abbrev CalcLoopc1_30 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 18))) (.literal i32 (1))))) (CalcLoopc1_31 o REST)
abbrev CalcLoopc1_29 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 19)) (.literal i32 (1))) (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (0)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 26) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc1_30 o REST)
abbrev CalcLoopc1_28 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc1_29 o REST)
abbrev CalcLoopc1_27 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 19)) (.literal i32 (1))) (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (0)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 25) s64 (.variable s64 (o + 21)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc1_28 o REST)
abbrev CalcLoopc1_26 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 (0))))) (CalcLoopc1_27 o REST)
abbrev CalcLoopc1_25 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 19)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 20)) (.variable s64 (o + 16)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 24) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc1_26 o REST)
abbrev CalcLoopc1_24 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc1_25 o REST)
abbrev CalcLoopc1_23 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 18)))))) (CalcLoopc1_24 o REST)
abbrev CalcLoopc1_22 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 18)))))) (CalcLoopc1_23 o REST)
abbrev CalcLoopc1_21 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 7) (.cast u64 (.variable i32 (o + 18)))))) (CalcLoopc1_22 o REST)
abbrev CalcLoopc1_20 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 8) (.cast u64 (.variable i32 (o + 18)))))) (CalcLoopc1_21 o REST)
abbrev CalcLoopc1 (o : Nat) (REST : Command) : Command := CalcLoopc1_20 o REST
abbrev CalcLoopc2_60 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc2_59 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 51) s64 (.variable s64 (o + 16)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc2_60 o REST)
abbrev CalcLoopc2_58 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 33)))) (CalcLoopc2_59 o REST)
abbrev CalcLoopc2_57 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 50) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc2_58 o REST)
abbrev CalcLoopc2_56 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 32)))) (CalcLoopc2_57 o REST)
abbrev CalcLoopc2_55 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 49) s64 (.variable s64 (o + 37)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc2_56 o REST)
abbrev CalcLoopc2_54 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 31)))) (CalcLoopc2_55 o REST)
abbrev CalcLoopc2_53 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 48) s64 (.unary s64 .neg (.variable s64 (o + 16))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc2_54 o REST)
abbrev CalcLoopc2_52 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 30)))) (CalcLoopc2_53 o REST)
abbrev CalcLoopc2_51 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 47) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc2_52 o REST)
abbrev CalcLoopc2_50 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 29)))) (CalcLoopc2_51 o REST)
abbrev CalcLoopc2_49 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 6) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_50 o REST)
abbrev CalcLoopc2_48 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 8) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_49 o REST)
abbrev CalcLoopc2_47 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 7) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_48 o REST)
abbrev CalcLoopc2_46 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_47 o REST)
abbrev CalcLoopc2_45 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_46 o REST)
abbrev CalcLoopc2_44 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_45 o REST)
abbrev CalcLoopc2_43 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_44 o REST)
abbrev CalcLoopc2_42 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_43 o REST)
abbrev CalcLoopc2_41 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 28)))))) (CalcLoopc2_42 o REST)
abbrev CalcLoopc2_40 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 6) (.cast u64 (.variable i32 (o + 27)))))) (CalcLoopc2_41 o REST)
abbrev CalcLoopc2 (o : Nat) (REST : Command) : Command := CalcLoopc2_40 o REST
abbrev CalcLoopc3_80 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc3_79 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 61)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 62) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_80 o REST)
abbrev CalcLoopc3_78 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 55)))) (CalcLoopc3_79 o REST)
abbrev CalcLoopc3_77 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 26)) (.literal i32 (1))) (.binary bT .lt (.variable s64 (o + 22)) (.variable s64 (o + 55)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 61) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_78 o REST)
abbrev CalcLoopc3_76 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc3_77 o REST)
abbrev CalcLoopc3_75 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 54)) (.variable s64 (o + 16))) (.sequence (.scope (.sequence (.primitive (.assign (o + 60) s64 (.binary s64 .add (.variable s64 (o + 54)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_76 o REST)
abbrev CalcLoopc3_74 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 54)))) (CalcLoopc3_75 o REST)
abbrev CalcLoopc3_73 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable s64 (o + 54)) (.variable s64 (o + 16))) (.binary bT .ne (.variable s64 (o + 37)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 59) s64 (.binary s64 .add (.variable s64 (o + 53)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_74 o REST)
abbrev CalcLoopc3_72 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 53)))) (CalcLoopc3_73 o REST)
abbrev CalcLoopc3_71 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 51)) (.variable s64 (o + 16))) (.sequence (.scope (.sequence (.primitive (.assign (o + 58) s64 (.binary s64 .add (.variable s64 (o + 51)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_72 o REST)
abbrev CalcLoopc3_70 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 51)))) (CalcLoopc3_71 o REST)
abbrev CalcLoopc3_69 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.binary s64 .add (.variable s64 (o + 50)) (.variable s64 (o + 25))))) (CalcLoopc3_70 o REST)
abbrev CalcLoopc3_68 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 48)) (.unary s64 .neg (.variable s64 (o + 16)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 56) s64 (.binary s64 .add (.variable s64 (o + 48)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_69 o REST)
abbrev CalcLoopc3_67 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 48)))) (CalcLoopc3_68 o REST)
abbrev CalcLoopc3_66 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.binary s64 .add (.variable s64 (o + 47)) (.variable s64 (o + 25))))) (CalcLoopc3_67 o REST)
abbrev CalcLoopc3_65 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 37)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 54) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_66 o REST)
abbrev CalcLoopc3_64 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 36)))) (CalcLoopc3_65 o REST)
abbrev CalcLoopc3_63 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 53) s64 (.cast s64 (.literal i32 (0))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_64 o REST)
abbrev CalcLoopc3_62 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 35)))) (CalcLoopc3_63 o REST)
abbrev CalcLoopc3_61 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 52) s64 (.variable s64 (o + 37)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc3_62 o REST)
abbrev CalcLoopc3_60 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 34)))) (CalcLoopc3_61 o REST)
abbrev CalcLoopc3 (o : Nat) (REST : Command) : Command := CalcLoopc3_60 o REST
abbrev CalcLoopc4_100 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc4_99 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 72) s64 (.unary s64 .neg (.variable s64 (o + 16))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_100 o REST)
abbrev CalcLoopc4_98 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 39)))) (CalcLoopc4_99 o REST)
abbrev CalcLoopc4_97 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 71) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_98 o REST)
abbrev CalcLoopc4_96 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 38)))) (CalcLoopc4_97 o REST)
abbrev CalcLoopc4_95 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 66)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 65)) (.variable s64 (o + 16)))) (.binary bT .lt (.variable s64 (o + 65)) (.variable s64 (o + 23)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 70) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_96 o REST)
abbrev CalcLoopc4_94 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 65)))) (CalcLoopc4_95 o REST)
abbrev CalcLoopc4_93 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 66)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 62)) (.variable s64 (o + 63)))) (.binary bT .eq (.variable s64 (o + 56)) (.variable s64 (o + 63)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 69) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_94 o REST)
abbrev CalcLoopc4_92 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 56)))) (CalcLoopc4_93 o REST)
abbrev CalcLoopc4_91 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 66)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (o + 62)) (.variable s64 (o + 63)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 68) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_92 o REST)
abbrev CalcLoopc4_90 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 62)))) (CalcLoopc4_91 o REST)
abbrev CalcLoopc4_89 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 66)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 67) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_90 o REST)
abbrev CalcLoopc4_88 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 63)))) (CalcLoopc4_89 o REST)
abbrev CalcLoopc4_87 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 26)) (.literal i32 (1))) (.binary bT .lt (.variable s64 (o + 63)) (.variable s64 (o + 23)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 66) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_88 o REST)
abbrev CalcLoopc4_86 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc4_87 o REST)
abbrev CalcLoopc4_85 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 61)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 60)) (.variable s64 (o + 16)))) (.binary bT .lt (.variable s64 (o + 22)) (.variable s64 (o + 60)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 65) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_86 o REST)
abbrev CalcLoopc4_84 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 60)))) (CalcLoopc4_85 o REST)
abbrev CalcLoopc4_83 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 61)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 55)) (.variable s64 (o + 57)))) (.binary bT .eq (.variable s64 (o + 55)) (.variable s64 (o + 58)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 64) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_84 o REST)
abbrev CalcLoopc4_82 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 58)))) (CalcLoopc4_83 o REST)
abbrev CalcLoopc4_81 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 61)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (o + 55)) (.variable s64 (o + 57)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 63) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc4_82 o REST)
abbrev CalcLoopc4_80 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 57)))) (CalcLoopc4_81 o REST)
abbrev CalcLoopc4 (o : Nat) (REST : Command) : Command := CalcLoopc4_80 o REST
abbrev CalcLoopc5_120 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc5_119 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable s64 (o + 78)) (.variable s64 (o + 16))) (.binary bT .ne (.variable s64 (o + 46)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 83) s64 (.binary s64 .add (.variable s64 (o + 77)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_120 o REST)
abbrev CalcLoopc5_118 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 77)))) (CalcLoopc5_119 o REST)
abbrev CalcLoopc5_117 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 75)) (.variable s64 (o + 16))) (.sequence (.scope (.sequence (.primitive (.assign (o + 82) s64 (.binary s64 .add (.variable s64 (o + 75)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_118 o REST)
abbrev CalcLoopc5_116 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 75)))) (CalcLoopc5_117 o REST)
abbrev CalcLoopc5_115 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.binary s64 .add (.variable s64 (o + 74)) (.variable s64 (o + 25))))) (CalcLoopc5_116 o REST)
abbrev CalcLoopc5_114 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 72)) (.unary s64 .neg (.variable s64 (o + 16)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 80) s64 (.binary s64 .add (.variable s64 (o + 72)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_115 o REST)
abbrev CalcLoopc5_113 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 72)))) (CalcLoopc5_114 o REST)
abbrev CalcLoopc5_112 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.binary s64 .add (.variable s64 (o + 71)) (.variable s64 (o + 25))))) (CalcLoopc5_113 o REST)
abbrev CalcLoopc5_111 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 46)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 78) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_112 o REST)
abbrev CalcLoopc5_110 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 45)))) (CalcLoopc5_111 o REST)
abbrev CalcLoopc5_109 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 77) s64 (.cast s64 (.literal i32 (0))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_110 o REST)
abbrev CalcLoopc5_108 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 44)))) (CalcLoopc5_109 o REST)
abbrev CalcLoopc5_107 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 76) s64 (.variable s64 (o + 46)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_108 o REST)
abbrev CalcLoopc5_106 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 43)))) (CalcLoopc5_107 o REST)
abbrev CalcLoopc5_105 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 75) s64 (.variable s64 (o + 16)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_106 o REST)
abbrev CalcLoopc5_104 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 42)))) (CalcLoopc5_105 o REST)
abbrev CalcLoopc5_103 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 74) s64 (.variable s64 (o + 20)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_104 o REST)
abbrev CalcLoopc5_102 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 41)))) (CalcLoopc5_103 o REST)
abbrev CalcLoopc5_101 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 24)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 73) s64 (.variable s64 (o + 46)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc5_102 o REST)
abbrev CalcLoopc5_100 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 40)))) (CalcLoopc5_101 o REST)
abbrev CalcLoopc5 (o : Nat) (REST : Command) : Command := CalcLoopc5_100 o REST
abbrev CalcLoopc6_140 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc6_139 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 90)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 86)) (.variable s64 (o + 87)))) (.binary bT .eq (.variable s64 (o + 80)) (.variable s64 (o + 87)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 93) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_140 o REST)
abbrev CalcLoopc6_138 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 80)))) (CalcLoopc6_139 o REST)
abbrev CalcLoopc6_137 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 90)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (o + 86)) (.variable s64 (o + 87)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 92) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_138 o REST)
abbrev CalcLoopc6_136 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 86)))) (CalcLoopc6_137 o REST)
abbrev CalcLoopc6_135 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 90)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 91) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_136 o REST)
abbrev CalcLoopc6_134 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 87)))) (CalcLoopc6_135 o REST)
abbrev CalcLoopc6_133 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 26)) (.literal i32 (1))) (.binary bT .lt (.variable s64 (o + 87)) (.variable s64 (o + 23)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 90) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_134 o REST)
abbrev CalcLoopc6_132 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc6_133 o REST)
abbrev CalcLoopc6_131 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 85)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 84)) (.variable s64 (o + 16)))) (.binary bT .lt (.variable s64 (o + 22)) (.variable s64 (o + 84)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 89) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_132 o REST)
abbrev CalcLoopc6_130 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 84)))) (CalcLoopc6_131 o REST)
abbrev CalcLoopc6_129 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 85)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 79)) (.variable s64 (o + 81)))) (.binary bT .eq (.variable s64 (o + 79)) (.variable s64 (o + 82)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 88) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_130 o REST)
abbrev CalcLoopc6_128 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 82)))) (CalcLoopc6_129 o REST)
abbrev CalcLoopc6_127 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 85)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (o + 79)) (.variable s64 (o + 81)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 87) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_128 o REST)
abbrev CalcLoopc6_126 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 81)))) (CalcLoopc6_127 o REST)
abbrev CalcLoopc6_125 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 85)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 86) s64 (.variable s64 (o + 22)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_126 o REST)
abbrev CalcLoopc6_124 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 79)))) (CalcLoopc6_125 o REST)
abbrev CalcLoopc6_123 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 26)) (.literal i32 (1))) (.binary bT .lt (.variable s64 (o + 22)) (.variable s64 (o + 79)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 85) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_124 o REST)
abbrev CalcLoopc6_122 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CalcLoopc6_123 o REST)
abbrev CalcLoopc6_121 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .ne (.variable s64 (o + 78)) (.variable s64 (o + 16))) (.sequence (.scope (.sequence (.primitive (.assign (o + 84) s64 (.binary s64 .add (.variable s64 (o + 78)) (.variable s64 (o + 25))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc6_122 o REST)
abbrev CalcLoopc6_120 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 78)))) (CalcLoopc6_121 o REST)
abbrev CalcLoopc6 (o : Nat) (REST : Command) : Command := CalcLoopc6_120 o REST
abbrev CalcLoopc7_160 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc7_159 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 21)))) (CalcLoopc7_160 o REST)
abbrev CalcLoopc7_158 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 20)))) (CalcLoopc7_159 o REST)
abbrev CalcLoopc7_157 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 8) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 94)))) (CalcLoopc7_158 o REST)
abbrev CalcLoopc7_156 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 7) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 83)))) (CalcLoopc7_157 o REST)
abbrev CalcLoopc7_155 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 76)))) (CalcLoopc7_156 o REST)
abbrev CalcLoopc7_154 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 88)))) (CalcLoopc7_155 o REST)
abbrev CalcLoopc7_153 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 91)))) (CalcLoopc7_154 o REST)
abbrev CalcLoopc7_152 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 73)))) (CalcLoopc7_153 o REST)
abbrev CalcLoopc7_151 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 93)))) (CalcLoopc7_152 o REST)
abbrev CalcLoopc7_150 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (o + 28))) (.variable s64 (o + 92)))) (CalcLoopc7_151 o REST)
abbrev CalcLoopc7_149 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 8) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 70)))) (CalcLoopc7_150 o REST)
abbrev CalcLoopc7_148 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 7) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 59)))) (CalcLoopc7_149 o REST)
abbrev CalcLoopc7_147 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 52)))) (CalcLoopc7_148 o REST)
abbrev CalcLoopc7_146 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 64)))) (CalcLoopc7_147 o REST)
abbrev CalcLoopc7_145 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 67)))) (CalcLoopc7_146 o REST)
abbrev CalcLoopc7_144 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 49)))) (CalcLoopc7_145 o REST)
abbrev CalcLoopc7_143 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 69)))) (CalcLoopc7_144 o REST)
abbrev CalcLoopc7_142 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (o + 27))) (.variable s64 (o + 68)))) (CalcLoopc7_143 o REST)
abbrev CalcLoopc7_141 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.logical true (.binary bT .eq (.variable i32 (o + 90)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 89)) (.variable s64 (o + 16)))) (.binary bT .lt (.variable s64 (o + 89)) (.variable s64 (o + 23)))) (.sequence (.scope (.sequence (.primitive (.assign (o + 94) s64 (.variable s64 (o + 23)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc7_142 o REST)
abbrev CalcLoopc7_140 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.variable s64 (o + 89)))) (CalcLoopc7_141 o REST)
abbrev CalcLoopc7 (o : Nat) (REST : Command) : Command := CalcLoopc7_140 o REST
abbrev CalcLoopc8_172 (o : Nat) (REST : Command) : Command := REST
abbrev CalcLoopc8_171 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 6) i32 (.binary i32 .add (.variable i32 (o + 6)) (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 15)))))) (CalcLoopc8_172 o REST)
abbrev CalcLoopc8_170 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 13) i32 (.cast u64 (.binary i32 .add (.variable i32 (o + 6)) (.literal i32 (1)))) (.variable i32 (o + 97)))) (CalcLoopc8_171 o REST)
abbrev CalcLoopc8_169 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 12) i32 (.cast u64 (.binary i32 .add (.variable i32 (o + 6)) (.literal i32 (1)))) (.variable i32 (o + 8)))) (CalcLoopc8_170 o REST)
abbrev CalcLoopc8_168 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 11) i32 (.cast u64 (.binary i32 .add (.variable i32 (o + 6)) (.literal i32 (1)))) (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 7))) (.literal i32 (1))))) (CalcLoopc8_169 o REST)
abbrev CalcLoopc8_167 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 13) i32 (.cast u64 (.variable i32 (o + 6))) (.variable i32 (o + 9)))) (CalcLoopc8_168 o REST)
abbrev CalcLoopc8_166 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 12) i32 (.cast u64 (.variable i32 (o + 6))) (.variable i32 (o + 97)))) (CalcLoopc8_167 o REST)
abbrev CalcLoopc8_165 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 11) i32 (.cast u64 (.variable i32 (o + 6))) (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 7))) (.literal i32 (2))))) (CalcLoopc8_166 o REST)
abbrev CalcLoopc8_164 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.divrem i32 false (.binary i32 .add (.variable i32 (o + 8)) (.variable i32 (o + 9))) (.literal i32 (2))))) (CalcLoopc8_165 o REST)
abbrev CalcLoopc8_163 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 7) s64 (.cast u64 (.variable i32 (o + 18))) (.variable s64 (o + 96)))) (CalcLoopc8_164 o REST)
abbrev CalcLoopc8_162 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 8) s64 (.cast u64 (.variable i32 (o + 18))) (.variable s64 (o + 95)))) (CalcLoopc8_163 o REST)
abbrev CalcLoopc8_161 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 19)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 96) s64 (.cast s64 (.literal i32 (0))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc8_162 o REST)
abbrev CalcLoopc8_160 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 19)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 95) s64 (.variable s64 (o + 16)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CalcLoopc8_161 o REST)
abbrev CalcLoopc8 (o : Nat) (REST : Command) : Command := CalcLoopc8_160 o REST
abbrev CalcLoopBody (o : Nat) : Command := CalcLoopc0 o (CalcLoopc1 o (CalcLoopc2 o (CalcLoopc3 o (CalcLoopc4 o (CalcLoopc5 o (CalcLoopc6 o (CalcLoopc7 o (CalcLoopc8 o (Sk)))))))))

def uc1 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def uc2 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def uc3 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def uc4 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def uc5 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }
def uc6 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def uc7 (s : BS) (idx : Nat) (a : Int) : BS := { s with ladd := s.ladd.set idx a }
def uc8 (s : BS) (idx : Nat) (a : Int) : BS := { s with lval := s.lval.set idx a }
def uc9 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def uc10 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def uc11 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def uc12 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def uc13 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }
def uc14 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def uc15 (s : BS) (idx : Nat) (a : Int) : BS := { s with ladd := s.ladd.set idx a }
def uc16 (s : BS) (idx : Nat) (a : Int) : BS := { s with lval := s.lval.set idx a }
def uc17 (s : BS) (idx : Nat) (a : Int) : BS := { s with lval := s.lval.set idx a }
def uc18 (s : BS) (idx : Nat) (a : Int) : BS := { s with ladd := s.ladd.set idx a }
def uc19 (s : BS) (idx : Nat) (a : Int) : BS := { s with sk := s.sk.set idx a }
def uc20 (s : BS) (idx : Nat) (a : Int) : BS := { s with sl := s.sl.set idx a }
def uc21 (s : BS) (idx : Nat) (a : Int) : BS := { s with sr := s.sr.set idx a }
def uc22 (s : BS) (idx : Nat) (a : Int) : BS := { s with sk := s.sk.set idx a }
def uc23 (s : BS) (idx : Nat) (a : Int) : BS := { s with sl := s.sl.set idx a }
def uc24 (s : BS) (idx : Nat) (a : Int) : BS := { s with sr := s.sr.set idx a }


end Proofs.BeatsExec
