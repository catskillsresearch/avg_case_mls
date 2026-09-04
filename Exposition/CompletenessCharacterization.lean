/-
Runnable snippet for arxiv.md, displayed with the first collapse theorem.

Language-level NP-average completeness in the report's untimed vocabulary is
equivalent to the language being neither empty nor everything.  The full proof
is in `AvgCaseMls/EncodingCollapse.lean`; it constructs the degenerate law as
target and uses a two-valued reduction map.

Checked against AvgCaseMls.EncodingCollapse.
-/
import AvgCaseMls.EncodingCollapse

namespace Exposition.CompletenessCharacterization

open AvCom

theorem npAverageCompleteLanguage_iff_nontrivial (L : Set Bitstring) :
    TR1995.IsNPAverageCompleteLanguage L ↔ (L ≠ ∅ ∧ L ≠ Set.univ) :=
  AvgCaseMls.EncodingCollapse.npAverageCompleteLanguage_iff_nontrivial L

end Exposition.CompletenessCharacterization
