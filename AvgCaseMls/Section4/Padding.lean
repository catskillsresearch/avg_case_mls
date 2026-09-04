import AvgCaseMls.Section4.RankFamily
import AvgCaseMls.Foundation.TapeMacros

/-!
# Low-level unary padding used in Section 4
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation
open AvgCaseMls.Foundation.TapeMacros

namespace UnaryRank

def padOneProgram : Program := .machine appendZeroMachine

def padOneTime : Nat → Nat := appendZeroTime

theorem padOneTime_polynomial : IsPolynomial padOneTime :=
  appendZeroTime_polynomial

theorem padOneTime_monotone : Monotone padOneTime :=
  appendZeroTime_monotone

theorem padOne_computes :
    ComputesWithin padOneProgram (fun x => x ++ [false]) padOneTime :=
  appendZero_computes

theorem padOne_code (n : Nat) :
    eval appendZeroMachine (padOneTime (code n).length) (code n) =
      some ⟨true, code (n + 1), padOneTime (code n).length⟩ := by
  simpa [padOneTime, appendZeroTime, code] using
    appendZero_correct (code n)

end UnaryRank

end AvgCaseMls.Section4
