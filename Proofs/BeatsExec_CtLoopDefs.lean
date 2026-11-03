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

abbrev CtLoopc0_20 (o : Nat) (REST : Command) : Command := REST
abbrev CtLoopc0_19 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 12) s64 (.variable s64 (o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc0_20 o REST)
abbrev CtLoopc0_18 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 5) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_19 o REST)
abbrev CtLoopc0_17 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 2) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_18 o REST)
abbrev CtLoopc0_16 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 4) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_17 o REST)
abbrev CtLoopc0_15 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 1) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_16 o REST)
abbrev CtLoopc0_14 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 3) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_15 o REST)
abbrev CtLoopc0_13 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_14 o REST)
abbrev CtLoopc0_12 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 15) (.cast u64 (.variable i32 (o + 4)))))) (CtLoopc0_13 o REST)
abbrev CtLoopc0_11 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 6) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 10)))) (CtLoopc0_12 o REST)
abbrev CtLoopc0_10 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 6)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 10) s64 (.variable s64 (o + 7)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc0_11 o REST)
abbrev CtLoopc0_9 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.read s64 (.local 6) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_10 o REST)
abbrev CtLoopc0_8 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 6)) (.literal i32 (1))) (.binary bT .ne (.variable s64 (o + 7)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 9) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc0_9 o REST)
abbrev CtLoopc0_7 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtLoopc0_8 o REST)
abbrev CtLoopc0_6 (o : Nat) (REST : Command) : Command := .sequence (.branch (.logical true (.binary bT .eq (.variable i32 (o + 6)) (.literal i32 (1))) (.binary bT .eq (.variable s64 (o + 7)) (.cast s64 (.literal i32 (1))))) (.sequence (.scope (.sequence (.primitive (.assign (o + 8) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc0_7 o REST)
abbrev CtLoopc0_5 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtLoopc0_6 o REST)
abbrev CtLoopc0_4 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare s64 true (.cast s64 (.binary i32 .sub (.variable i32 (o + 5)) (.variable i32 (o + 4)))))) (CtLoopc0_5 o REST)
abbrev CtLoopc0_3 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .lt (.variable i32 (o + 4)) (.variable i32 (o + 5))) (.sequence (.scope (.sequence (.primitive (.assign (o + 6) i32 (.literal i32 (1)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc0_4 o REST)
abbrev CtLoopc0_2 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (CtLoopc0_3 o REST)
abbrev CtLoopc0_1 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_2 o REST)
abbrev CtLoopc0_0 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable i32 (o + 3)))))) (CtLoopc0_1 o REST)
abbrev CtLoopc0 (o : Nat) (REST : Command) : Command := CtLoopc0_0 o REST
abbrev CtLoopc1_40 (o : Nat) (REST : Command) : Command := REST
abbrev CtLoopc1_39 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 22) i32 (.variable i32 (o + 18)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_40 o REST)
abbrev CtLoopc1_38 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 21) i32 (.variable i32 (o + 4)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_39 o REST)
abbrev CtLoopc1_37 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable i32 (o + 20)))))) (CtLoopc1_38 o REST)
abbrev CtLoopc1_36 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable i32 (o + 20)))))) (CtLoopc1_37 o REST)
abbrev CtLoopc1_35 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 10) (.cast u64 (.variable i32 (o + 19)))))) (CtLoopc1_36 o REST)
abbrev CtLoopc1_34 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.read i32 (.local 9) (.cast u64 (.variable i32 (o + 19)))))) (CtLoopc1_35 o REST)
abbrev CtLoopc1_33 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 3))) (.literal i32 (2))))) (CtLoopc1_34 o REST)
abbrev CtLoopc1_32 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.binary i32 .add (.binary i32 .mul (.literal i32 (2)) (.variable i32 (o + 3))) (.literal i32 (1))))) (CtLoopc1_33 o REST)
abbrev CtLoopc1_31 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.divrem i32 false (.binary i32 .add (.variable i32 (o + 4)) (.variable i32 (o + 5))) (.literal i32 (2))))) (CtLoopc1_32 o REST)
abbrev CtLoopc1_30 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 5) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 17)))) (CtLoopc1_31 o REST)
abbrev CtLoopc1_29 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 2) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 16)))) (CtLoopc1_30 o REST)
abbrev CtLoopc1_28 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 4) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 15)))) (CtLoopc1_29 o REST)
abbrev CtLoopc1_27 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 1) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 14)))) (CtLoopc1_28 o REST)
abbrev CtLoopc1_26 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 3) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 13)))) (CtLoopc1_27 o REST)
abbrev CtLoopc1_25 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (o + 3))) (.variable s64 (o + 12)))) (CtLoopc1_26 o REST)
abbrev CtLoopc1_24 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 17) s64 (.cast s64 (.literal i32 (1))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_25 o REST)
abbrev CtLoopc1_23 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 16) s64 (.cast s64 (.literal i32 (1))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_24 o REST)
abbrev CtLoopc1_22 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 15) s64 (.variable s64 (o + 0)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_23 o REST)
abbrev CtLoopc1_21 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 14) s64 (.unary s64 .neg (.variable s64 (o + 0))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_22 o REST)
abbrev CtLoopc1_20 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 8)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 13) s64 (.variable s64 (o + 11)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc1_21 o REST)
abbrev CtLoopc1 (o : Nat) (REST : Command) : Command := CtLoopc1_20 o REST
abbrev CtLoopc2_49 (o : Nat) (REST : Command) : Command := REST
abbrev CtLoopc2_48 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 3) i32 (.binary i32 .add (.variable i32 (o + 3)) (.literal i32 (1))))) (CtLoopc2_49 o REST)
abbrev CtLoopc2_47 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 2) i32 (.binary i32 .add (.variable i32 (o + 2)) (.variable i32 (o + 9))))) (CtLoopc2_48 o REST)
abbrev CtLoopc2_46 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 14) i32 (.cast u64 (.variable i32 (o + 2))) (.variable i32 (o + 3)))) (CtLoopc2_47 o REST)
abbrev CtLoopc2_45 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 10) i32 (.cast u64 (.variable i32 (o + 20))) (.variable i32 (o + 24)))) (CtLoopc2_46 o REST)
abbrev CtLoopc2_44 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 9) i32 (.cast u64 (.variable i32 (o + 20))) (.variable i32 (o + 23)))) (CtLoopc2_45 o REST)
abbrev CtLoopc2_43 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 10) i32 (.cast u64 (.variable i32 (o + 19))) (.variable i32 (o + 22)))) (CtLoopc2_44 o REST)
abbrev CtLoopc2_42 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 9) i32 (.cast u64 (.variable i32 (o + 19))) (.variable i32 (o + 21)))) (CtLoopc2_43 o REST)
abbrev CtLoopc2_41 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 24) i32 (.variable i32 (o + 5)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc2_42 o REST)
abbrev CtLoopc2_40 (o : Nat) (REST : Command) : Command := .sequence (.branch (.binary bT .eq (.variable i32 (o + 9)) (.literal i32 (1))) (.sequence (.scope (.sequence (.primitive (.assign (o + 23) i32 (.variable i32 (o + 18)))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (CtLoopc2_41 o REST)
abbrev CtLoopc2 (o : Nat) (REST : Command) : Command := CtLoopc2_40 o REST
abbrev CtLoopBody (o : Nat) : Command := CtLoopc0 o (CtLoopc1 o (CtLoopc2 o (Sk)))

def uk1 (s : BS) (idx : Nat) (a : Int) : BS := { s with len := s.len.set idx a }
def uk2 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxv := s.mxv.set idx a }
def uk3 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnv := s.mnv.set idx a }
def uk4 (s : BS) (idx : Nat) (a : Int) : BS := { s with smx := s.smx.set idx a }
def uk5 (s : BS) (idx : Nat) (a : Int) : BS := { s with smn := s.smn.set idx a }
def uk6 (s : BS) (idx : Nat) (a : Int) : BS := { s with mxc := s.mxc.set idx a }
def uk7 (s : BS) (idx : Nat) (a : Int) : BS := { s with mnc := s.mnc.set idx a }
def uk8 (s : BS) (idx : Nat) (a : Int) : BS := { s with lo := s.lo.set idx a }
def uk9 (s : BS) (idx : Nat) (a : Int) : BS := { s with hi := s.hi.set idx a }
def uk10 (s : BS) (idx : Nat) (a : Int) : BS := { s with lo := s.lo.set idx a }
def uk11 (s : BS) (idx : Nat) (a : Int) : BS := { s with hi := s.hi.set idx a }
def uk12 (s : BS) (idx : Nat) (a : Int) : BS := { s with ent := s.ent.set idx a }


end Proofs.BeatsExec
