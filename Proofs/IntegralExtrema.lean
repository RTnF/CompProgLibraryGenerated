-- Generated integral template family from primary syntax.
-- Class, enum and floating arguments remain unresolved in the JSON IR.
import Proofs.CppTemplate

namespace Proofs.IntegralExtrema
open Proofs.CppTemplate

def «chmax» : TemplateProgram :=
  ⟨2, [⟨(.parameter 0), true, true⟩, ⟨(.parameter 1), true, false⟩], (.scalar .boolean),
   (.scope (.sequence (.branch (.comparison .lt (.variable (.parameter 0) 0) (.variable (.parameter 1) 1)) (.scope (.scope (.sequence (.assign 0 (.variable (.parameter 1) 1)) (.sequence (.ret (.cast (.scalar .boolean) (.literal (.scalar .i32) (1)))) .skip)))) .skip) (.sequence (.ret (.cast (.scalar .boolean) (.literal (.scalar .i32) (0)))) .skip)))⟩

def «chmin» : TemplateProgram :=
  ⟨2, [⟨(.parameter 0), true, true⟩, ⟨(.parameter 1), true, false⟩], (.scalar .boolean),
   (.scope (.sequence (.branch (.comparison .lt (.variable (.parameter 1) 1) (.variable (.parameter 0) 0)) (.scope (.scope (.sequence (.assign 0 (.variable (.parameter 1) 1)) (.sequence (.ret (.cast (.scalar .boolean) (.literal (.scalar .i32) (1)))) .skip)))) .skip) (.sequence (.ret (.cast (.scalar .boolean) (.literal (.scalar .i32) (0)))) .skip)))⟩

end Proofs.IntegralExtrema
