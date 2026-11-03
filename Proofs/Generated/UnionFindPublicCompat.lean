-- Generated constructor layouts and all nonstatic method receivers from the audited class.
import Proofs.CppClassCopyCommands
import Proofs.CppConstructorView
import Proofs.CppNestedCall
import Proofs.CppMoveCallBindings
import Proofs.CppMoveObjectReceiver

-- Generated from audited Clang vector operations and scalar syntax.

namespace Proofs.UnionFindPublicCompatInstance.Construction.Stages
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

-- Initializer/body stage: runFuel retains fields; callFuel retires them.
def «UnionFind_construct0» : NProgram := ⟨[],.unit,(.sequence (.primitive (.declareVector ⟨32, true, false⟩ true)) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.primitive .skip))))⟩
def «UnionFind_construct0_fields» : List (String × Nat) := [("_ps",0), ("_num_groups",1), ("_n",2)]
-- Initializer/body stage: runFuel retains fields; callFuel retires them.
def «UnionFind_construct1» : NProgram := ⟨[.scalar ⟨32, true, false⟩ false true],.unit,(.sequence (.primitive (.fillVector ⟨32, true, false⟩ true (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 0)) (.unary ⟨32, true, false⟩ .neg (.literal ⟨32, true, false⟩ (1))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 0))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 0))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .ge (.variable ⟨32, true, false⟩ 0) (.literal ⟨32, true, false⟩ (0))))) (.primitive .skip)))))⟩
def «UnionFind_construct1_fields» : List (String × Nat) := [("_ps",1), ("_num_groups",2), ("_n",3)]

end Proofs.UnionFindPublicCompatInstance.Construction.Stages

namespace Proofs.UnionFindPublicCompatInstance.Construction
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish
def qualifiedClass : String := "cp::UnionFind"
def sourceSHA256 : String := "e3c9c02a982a93615d7c607788e4d88fb3196e06ff4cb417e677ccc080e91026"
def profileFor (targetConst : Bool) : Proofs.CppClassCopy.Profile := ⟨⟨32, true, false⟩,(true && (!targetConst || false)),[(⟨32, true, false⟩,(true && (!targetConst || false))), (⟨32, true, false⟩,(true && (!targetConst || false)))]⟩
def profile : Proofs.CppClassCopy.Profile := profileFor false
def constProfile : Proofs.CppClassCopy.Profile := profileFor true
def copy (state : NState) (source : ObjectRef) : Option (NState × ObjectRef) :=
  Proofs.CppClassCopy.copyClass state source profile
def copyConst (state : NState) (source : ObjectRef) : Option (NState × ObjectRef) :=
  Proofs.CppClassCopy.copyClass state source constProfile
def copyCommand (source : ObjectRef) (targetConst : Bool) : Option Command :=
  Proofs.CppClassCopyCommands.copyCommand source (profileFor targetConst)
def runCopyFuel (fuel : Nat) (state : NState) (source : ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome NStep :=
  Proofs.CppClassCopyCommands.runCopyFuel fuel state source (profileFor targetConst)
def «UnionFind_construct0» : NProgram := Stages.«UnionFind_construct0»
def «UnionFind_construct0_vectorSlot» : Nat := 0
def «UnionFind_construct0_scalarFields» : List ScalarField := [⟨1,⟨32, true, false⟩⟩, ⟨2,⟨32, true, false⟩⟩]
def «UnionFind_construct0_exportFuel» (fuel : Nat) (caller : NState) (args : List NArgument) :
    Proofs.CppLoop.Outcome (NState × ObjectRef) :=
  «UnionFind_construct0».constructFuel fuel caller args «UnionFind_construct0_vectorSlot»
    (.integer ⟨32, true, false⟩) «UnionFind_construct0_scalarFields»
def «UnionFind_construct0_exportViewFuel» (fuel : Nat) (caller : NState) (args : List NArgument)
    (targetConst : Bool) : Proofs.CppLoop.Outcome (NState × ObjectRef) :=
  Proofs.CppConstructorView.constructProfileFuel «UnionFind_construct0» fuel caller args
    «UnionFind_construct0_vectorSlot» «UnionFind_construct0_scalarFields» (profileFor targetConst)
def «UnionFind_construct1» : NProgram := Stages.«UnionFind_construct1»
def «UnionFind_construct1_vectorSlot» : Nat := 1
def «UnionFind_construct1_scalarFields» : List ScalarField := [⟨2,⟨32, true, false⟩⟩, ⟨3,⟨32, true, false⟩⟩]
def «UnionFind_construct1_exportFuel» (fuel : Nat) (caller : NState) (args : List NArgument) :
    Proofs.CppLoop.Outcome (NState × ObjectRef) :=
  «UnionFind_construct1».constructFuel fuel caller args «UnionFind_construct1_vectorSlot»
    (.integer ⟨32, true, false⟩) «UnionFind_construct1_scalarFields»
def «UnionFind_construct1_exportViewFuel» (fuel : Nat) (caller : NState) (args : List NArgument)
    (targetConst : Bool) : Proofs.CppLoop.Outcome (NState × ObjectRef) :=
  Proofs.CppConstructorView.constructProfileFuel «UnionFind_construct1» fuel caller args
    «UnionFind_construct1_vectorSlot» «UnionFind_construct1_scalarFields» (profileFor targetConst)
end Proofs.UnionFindPublicCompatInstance.Construction
-- Generated from audited Clang vector operations and scalar syntax.

namespace Proofs.UnionFindPublicCompatInstance.Calls.Methods
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «UnionFind_find_root» : NProgram := ⟨[.vector ⟨32, true, false⟩ false, .scalar ⟨32, true, false⟩ true false, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 3 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 3))) (.primitive .skip)))⟩
def «UnionFind_unite» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ true true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 4)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 4) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 6)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 6) (.variable ⟨32, true, false⟩ 5))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 6))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 7))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 7 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 7))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 6) (.variable ⟨32, true, false⟩ 7)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6)) (.variable ⟨32, true, false⟩ 7))) (.sequence (.primitive (.assign 6 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 8))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 7))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 8))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 4))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 11)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 11) (.variable ⟨32, true, false⟩ 10))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 11))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 12))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 12 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 12))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 11) (.variable ⟨32, true, false⟩ 12)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 11))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 11)) (.variable ⟨32, true, false⟩ 12))) (.sequence (.primitive (.assign 11 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 13))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 12))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 13))) (.sequence (.branch (.binary ⟨1, false, true⟩ .eq (.variable ⟨32, true, false⟩ 9) (.variable ⟨32, true, false⟩ 14)) (.sequence (.scope (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 9))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.unary ⟨32, true, false⟩ .neg (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 9)))) (.unary ⟨32, true, false⟩ .neg (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 14))))) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 9))) (.sequence (.primitive (.assign 9 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 14))) (.sequence (.primitive (.assign 14 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 15))) (.primitive .skip))))) (.primitive .skip)) (.primitive .skip)) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 9)) (.binary ⟨32, true, false⟩ .add (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 9))) (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 14)))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 14)) (.variable ⟨32, true, false⟩ 9))) (.sequence (.primitive (.assign 1 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .sub (.variable ⟨32, true, false⟩ 1) (.literal ⟨32, true, false⟩ (1))))) (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 9))) (.primitive .skip)))))))))))))))))))))))))⟩
def «UnionFind_same_2» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ true true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨1, false, true⟩,(.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 4)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 4) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 6)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 6) (.variable ⟨32, true, false⟩ 5))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 6))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 7))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 7 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 7))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 6) (.variable ⟨32, true, false⟩ 7)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6)) (.variable ⟨32, true, false⟩ 7))) (.sequence (.primitive (.assign 6 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 8))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 7))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 4))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 10)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 10) (.variable ⟨32, true, false⟩ 9))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 10))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 11))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 11 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 11))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 10) (.variable ⟨32, true, false⟩ 11)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 10))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 10)) (.variable ⟨32, true, false⟩ 11))) (.sequence (.primitive (.assign 10 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 12))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 11))) (.sequence (.primitive (.ret (.binary ⟨1, false, true⟩ .eq (.variable ⟨32, true, false⟩ 8) (.variable ⟨32, true, false⟩ 12)))) (.primitive .skip))))))))))))))))))⟩
def «UnionFind_root» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ true true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 4 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 4)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3)) (.variable ⟨32, true, false⟩ 4))) (.sequence (.primitive (.assign 3 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 5))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 4))) (.primitive .skip))))))⟩
def «UnionFind_size_1» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ true true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.primitive (.check (.logical true (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 5)) (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 5) (.variable ⟨32, true, false⟩ 4))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 5))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 6 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 5) (.variable ⟨32, true, false⟩ 6)) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 5))))) (.sequence (.primitive (.write (.local 0) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 5)) (.variable ⟨32, true, false⟩ 6))) (.sequence (.primitive (.assign 5 ⟨32, true, false⟩ (.variable ⟨32, true, false⟩ 7))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 6))) (.sequence (.primitive (.ret (.unary ⟨32, true, false⟩ .neg (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 7)))))) (.primitive .skip))))))))))⟩
def «UnionFind_num_groups_0» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ true true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 1))) (.primitive .skip))⟩
def «UnionFind_same_2_2» : NProgram := ⟨[.vector ⟨32, true, false⟩ false, .scalar ⟨32, true, false⟩ true false, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨1, false, true⟩,(.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.cast ⟨32, true, false⟩ (.size (.integer ⟨32, true, false⟩) (.local 0)))))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 4)))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 4) (.cast ⟨32, true, false⟩ (.size (.integer ⟨32, true, false⟩) (.local 0)))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 6 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 6))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 7))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 4))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 10))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 10 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 10))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 10))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 11))) (.sequence (.primitive (.ret (.binary ⟨1, false, true⟩ .eq (.variable ⟨32, true, false⟩ 8) (.variable ⟨32, true, false⟩ 12)))) (.primitive .skip))))))))))))))))⟩
def «UnionFind_size_1_2» : NProgram := ⟨[.vector ⟨32, true, false⟩ false, .scalar ⟨32, true, false⟩ true false, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .le (.literal ⟨32, true, false⟩ (0)) (.variable ⟨32, true, false⟩ 3)))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.cast ⟨32, true, false⟩ (.size (.integer ⟨32, true, false⟩) (.local 0)))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ge (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 5))) (.literal ⟨32, true, false⟩ (0))) (.sequence (.scope (.sequence (.primitive (.assign 5 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 5))))) (.primitive .skip))) (.primitive .skip))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 5))) (.sequence (.primitive (.ret (.unary ⟨32, true, false⟩ .neg (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 6)))))) (.primitive .skip))))))))⟩
def «UnionFind_num_groups_0_2» : NProgram := ⟨[.vector ⟨32, true, false⟩ false, .scalar ⟨32, true, false⟩ true false, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 1))) (.primitive .skip))⟩

end Proofs.UnionFindPublicCompatInstance.Calls.Methods

namespace Proofs.UnionFindPublicCompatInstance.Calls
open Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppLoop
def sourceSHA256 : String := "e3c9c02a982a93615d7c607788e4d88fb3196e06ff4cb417e677ccc080e91026"
def fieldNames : List String := ["_ps", "_num_groups", "_n"]
def «UnionFind_find_root_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 1 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_find_root_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 1) :
    «UnionFind_find_root_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_find_root_arguments»,fields,arity]
def «UnionFind_find_root_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_find_root_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_find_root» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_find_root_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_find_root_arguments» receiver arguments = some expanded) :
    «UnionFind_find_root_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_find_root» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_find_root_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_find_root_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_find_root» = true := by decide +kernel
def «UnionFind_unite_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 2 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_unite_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 2) :
    «UnionFind_unite_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_unite_arguments»,fields,arity]
theorem «UnionFind_unite_resolve_of_receiver» (caller : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object ⟨32, true, false⟩)
    (expressions : List (NExpr × Int))
    (ready : Proofs.CppMoveReceiverResolve.Ready caller ⟨32, true, false⟩ expressions)
    (arity : expressions.length = 2) :
    ∃ expanded last,
      «UnionFind_unite_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧
      resolveArguments caller ⟨32, true, false⟩ Methods.«UnionFind_unite».parameters expanded =
        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ⟨32, true, false⟩
          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by
  have mapped := «UnionFind_unite_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)
    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object ⟨32, true, false⟩ receiver expressions ready
  have params : Methods.«UnionFind_unite».parameters =
      (.vector ⟨32, true, false⟩ true :: .scalar ⟨32, true, false⟩ true true :: .scalar ⟨32, true, false⟩ false true ::
        Proofs.CppMoveReceiverResolve.parameters ⟨32, true, false⟩ expressions) := by
    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const',arity]
    rfl
  rw [← params] at run
  exact ⟨_,last,mapped,run⟩
def «UnionFind_unite_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_unite_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_unite» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_unite_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_unite_arguments» receiver arguments = some expanded) :
    «UnionFind_unite_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_unite» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_unite_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_unite_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_unite» = true := by decide +kernel
def «UnionFind_same_2_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 2 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_same_2_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 2) :
    «UnionFind_same_2_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_same_2_arguments»,fields,arity]
theorem «UnionFind_same_2_resolve_of_receiver» (caller : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object ⟨32, true, false⟩)
    (expressions : List (NExpr × Int))
    (ready : Proofs.CppMoveReceiverResolve.Ready caller ⟨32, true, false⟩ expressions)
    (arity : expressions.length = 2) :
    ∃ expanded last,
      «UnionFind_same_2_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧
      resolveArguments caller ⟨32, true, false⟩ Methods.«UnionFind_same_2».parameters expanded =
        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ⟨32, true, false⟩
          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by
  have mapped := «UnionFind_same_2_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)
    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object ⟨32, true, false⟩ receiver expressions ready
  have params : Methods.«UnionFind_same_2».parameters =
      (.vector ⟨32, true, false⟩ true :: .scalar ⟨32, true, false⟩ true true :: .scalar ⟨32, true, false⟩ false true ::
        Proofs.CppMoveReceiverResolve.parameters ⟨32, true, false⟩ expressions) := by
    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const',arity]
    rfl
  rw [← params] at run
  exact ⟨_,last,mapped,run⟩
def «UnionFind_same_2_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_same_2_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_same_2» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_same_2_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_same_2_arguments» receiver arguments = some expanded) :
    «UnionFind_same_2_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_same_2» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_same_2_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_same_2_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_same_2» = true := by decide +kernel
def «UnionFind_root_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 1 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_root_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 1) :
    «UnionFind_root_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_root_arguments»,fields,arity]
theorem «UnionFind_root_resolve_of_receiver» (caller : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object ⟨32, true, false⟩)
    (expressions : List (NExpr × Int))
    (ready : Proofs.CppMoveReceiverResolve.Ready caller ⟨32, true, false⟩ expressions)
    (arity : expressions.length = 1) :
    ∃ expanded last,
      «UnionFind_root_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧
      resolveArguments caller ⟨32, true, false⟩ Methods.«UnionFind_root».parameters expanded =
        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ⟨32, true, false⟩
          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by
  have mapped := «UnionFind_root_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)
    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object ⟨32, true, false⟩ receiver expressions ready
  have params : Methods.«UnionFind_root».parameters =
      (.vector ⟨32, true, false⟩ true :: .scalar ⟨32, true, false⟩ true true :: .scalar ⟨32, true, false⟩ false true ::
        Proofs.CppMoveReceiverResolve.parameters ⟨32, true, false⟩ expressions) := by
    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const',arity]
    rfl
  rw [← params] at run
  exact ⟨_,last,mapped,run⟩
def «UnionFind_root_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_root_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_root» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_root_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_root_arguments» receiver arguments = some expanded) :
    «UnionFind_root_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_root» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_root_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_root_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_root» = true := by decide +kernel
def «UnionFind_size_1_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 1 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_size_1_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 1) :
    «UnionFind_size_1_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_size_1_arguments»,fields,arity]
theorem «UnionFind_size_1_resolve_of_receiver» (caller : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object ⟨32, true, false⟩)
    (expressions : List (NExpr × Int))
    (ready : Proofs.CppMoveReceiverResolve.Ready caller ⟨32, true, false⟩ expressions)
    (arity : expressions.length = 1) :
    ∃ expanded last,
      «UnionFind_size_1_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧
      resolveArguments caller ⟨32, true, false⟩ Methods.«UnionFind_size_1».parameters expanded =
        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ⟨32, true, false⟩
          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by
  have mapped := «UnionFind_size_1_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)
    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object ⟨32, true, false⟩ receiver expressions ready
  have params : Methods.«UnionFind_size_1».parameters =
      (.vector ⟨32, true, false⟩ true :: .scalar ⟨32, true, false⟩ true true :: .scalar ⟨32, true, false⟩ false true ::
        Proofs.CppMoveReceiverResolve.parameters ⟨32, true, false⟩ expressions) := by
    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const',arity]
    rfl
  rw [← params] at run
  exact ⟨_,last,mapped,run⟩
def «UnionFind_size_1_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_size_1_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_size_1» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_size_1_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_size_1_arguments» receiver arguments = some expanded) :
    «UnionFind_size_1_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_size_1» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_size_1_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_size_1_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_size_1» = true := by decide +kernel
def «UnionFind_num_groups_0_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 0 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_num_groups_0_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 0) :
    «UnionFind_num_groups_0_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_num_groups_0_arguments»,fields,arity]
theorem «UnionFind_num_groups_0_resolve_of_receiver» (caller : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object ⟨32, true, false⟩)
    (expressions : List (NExpr × Int))
    (ready : Proofs.CppMoveReceiverResolve.Ready caller ⟨32, true, false⟩ expressions)
    (arity : expressions.length = 0) :
    ∃ expanded last,
      «UnionFind_num_groups_0_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧
      resolveArguments caller ⟨32, true, false⟩ Methods.«UnionFind_num_groups_0».parameters expanded =
        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ⟨32, true, false⟩
          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by
  have mapped := «UnionFind_num_groups_0_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)
    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object ⟨32, true, false⟩ receiver expressions ready
  have params : Methods.«UnionFind_num_groups_0».parameters =
      (.vector ⟨32, true, false⟩ true :: .scalar ⟨32, true, false⟩ true true :: .scalar ⟨32, true, false⟩ false true ::
        Proofs.CppMoveReceiverResolve.parameters ⟨32, true, false⟩ expressions) := by
    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const',arity]
    rfl
  rw [← params] at run
  exact ⟨_,last,mapped,run⟩
def «UnionFind_num_groups_0_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_num_groups_0_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_num_groups_0» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_num_groups_0_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_num_groups_0_arguments» receiver arguments = some expanded) :
    «UnionFind_num_groups_0_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_num_groups_0» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_num_groups_0_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_num_groups_0_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_num_groups_0» = true := by decide +kernel
def «UnionFind_same_2_2_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 2 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_same_2_2_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 2) :
    «UnionFind_same_2_2_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_same_2_2_arguments»,fields,arity]
def «UnionFind_same_2_2_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_same_2_2_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_same_2_2» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_same_2_2_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_same_2_2_arguments» receiver arguments = some expanded) :
    «UnionFind_same_2_2_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_same_2_2» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_same_2_2_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_same_2_2_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_same_2_2» = true := by decide +kernel
def «UnionFind_size_1_2_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 1 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_size_1_2_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 1) :
    «UnionFind_size_1_2_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_size_1_2_arguments»,fields,arity]
def «UnionFind_size_1_2_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_size_1_2_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_size_1_2» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_size_1_2_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_size_1_2_arguments» receiver arguments = some expanded) :
    «UnionFind_size_1_2_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_size_1_2» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_size_1_2_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_size_1_2_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_size_1_2» = true := by decide +kernel
def «UnionFind_num_groups_0_2_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 0 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments)
theorem «UnionFind_num_groups_0_2_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 0) :
    «UnionFind_num_groups_0_2_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .scalarReference slot0, .value (.variable ⟨32, true, false⟩ slot1)] ++ arguments) := by
  simp [«UnionFind_num_groups_0_2_arguments»,fields,arity]
def «UnionFind_num_groups_0_2_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («UnionFind_num_groups_0_2_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_num_groups_0_2» fuel caller ⟨32, true, false⟩ prepared
theorem «UnionFind_num_groups_0_2_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «UnionFind_num_groups_0_2_arguments» receiver arguments = some expanded) :
    «UnionFind_num_groups_0_2_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«UnionFind_num_groups_0_2» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«UnionFind_num_groups_0_2_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «UnionFind_num_groups_0_2_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«UnionFind_num_groups_0_2» = true := by decide +kernel
end Proofs.UnionFindPublicCompatInstance.Calls

namespace Proofs.UnionFindPublicCompatInstance
def qualifiedClass : String := "cp::UnionFind"
def sourceSHA256 : String := "e3c9c02a982a93615d7c607788e4d88fb3196e06ff4cb417e677ccc080e91026"
theorem construction_source : Construction.sourceSHA256 = sourceSHA256 := rfl
theorem method_source : Calls.sourceSHA256 = sourceSHA256 := rfl
end Proofs.UnionFindPublicCompatInstance
