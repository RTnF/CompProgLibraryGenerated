-- Generated syntax-directed scalar state IR.
import Proofs.CppState

namespace Proofs.ExtremaInstances
open Proofs.CppScalar Proofs.CppState

def «chmax__int__int» : StateProgram :=
  ⟨[⟨⟨32, true, false⟩, true, true⟩, ⟨⟨32, true, false⟩, true, false⟩], ⟨1, false, true⟩,
   (.scope (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 0) (.variable ⟨32, true, false⟩ 1)) (.scope (.scope (.sequence (.assign 0 (.variable ⟨32, true, false⟩ 1)) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (1)))) .skip)))) .skip) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (0)))) .skip)))⟩

def «chmax__unsigned_int__unsigned_int» : StateProgram :=
  ⟨[⟨⟨32, false, false⟩, true, true⟩, ⟨⟨32, false, false⟩, true, false⟩], ⟨1, false, true⟩,
   (.scope (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, false, false⟩ 0) (.variable ⟨32, false, false⟩ 1)) (.scope (.scope (.sequence (.assign 0 (.variable ⟨32, false, false⟩ 1)) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (1)))) .skip)))) .skip) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (0)))) .skip)))⟩

def «chmin__int__int» : StateProgram :=
  ⟨[⟨⟨32, true, false⟩, true, true⟩, ⟨⟨32, true, false⟩, true, false⟩], ⟨1, false, true⟩,
   (.scope (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 1) (.variable ⟨32, true, false⟩ 0)) (.scope (.scope (.sequence (.assign 0 (.variable ⟨32, true, false⟩ 1)) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (1)))) .skip)))) .skip) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (0)))) .skip)))⟩

def «chmin__unsigned_int__unsigned_int» : StateProgram :=
  ⟨[⟨⟨32, false, false⟩, true, true⟩, ⟨⟨32, false, false⟩, true, false⟩], ⟨1, false, true⟩,
   (.scope (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, false, false⟩ 1) (.variable ⟨32, false, false⟩ 0)) (.scope (.scope (.sequence (.assign 0 (.variable ⟨32, false, false⟩ 1)) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (1)))) .skip)))) .skip) (.sequence (.ret (.cast ⟨1, false, true⟩ (.literal ⟨32, true, false⟩ (0)))) .skip)))⟩

end Proofs.ExtremaInstances
