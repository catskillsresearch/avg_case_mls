/-
Runnable snippet for arxiv.md, displayed with the second collapse theorem.

In the timed model, language-level completeness is equivalent to NP membership
plus injective polynomial-time hardness; the rank domination clause contributes
nothing.  Full proof in `AvgCaseMls/DominationCollapse.lean`.

Checked against AvgCaseMls.DominationCollapse.
-/
import AvgCaseMls.DominationCollapse

namespace Exposition.DominationFree

open AvgCaseMls.Foundation AvgCaseMls.Section4

theorem isNPAverageCompleteLanguage_iff (L : Set Bitstring) :
    IsNPAverageCompleteLanguage L ↔
      InNP L ∧ ∀ source : DistributionalProblem, InDistNP source →
        Nonempty (PolyTimeInjectiveReduction source L) :=
  AvgCaseMls.Section4.isNPAverageCompleteLanguage_iff L

end Exposition.DominationFree
