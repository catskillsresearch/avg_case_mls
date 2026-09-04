/-
Runnable gist for arxiv.md, displayed with the corollary that the report's
Theorem 4.4 carries no content in its own vocabulary.

The hypotheses of the report's Theorem 4.4 are that the reduction is
injective, polynomial time invertible, and honest.  The proof term below
mentions only `r.map` and `r.reduces`.  Every other field of
`FaithfulReduction` is unused, and so is the `InNP L₂` hypothesis, which
`inNP_trivial` supplies for free.

Checked against AvgCaseMls.EncodingCollapse and AvgCaseMls.HonestReduction.
-/
import AvgCaseMls.EncodingCollapse
import AvgCaseMls.HonestReduction

namespace Gists.Theorem44Vacuous

open AvCom AvgCaseMls.EncodingCollapse

/-- Completeness transfers along any map satisfying the correctness
biconditional, with no further hypotheses at all. -/
theorem npAverageCompleteLanguage_of_reduces {L₁ L₂ : Set Bitstring}
    (map : Bitstring → Bitstring) (reduces : ∀ x, x ∈ L₁ ↔ map x ∈ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁) :
    TR1995.IsNPAverageCompleteLanguage L₂ := by
  -- Push a member and a non-member of `L₁` through `map`.
  obtain ⟨hne, hnu⟩ := (npAverageCompleteLanguage_iff_nontrivial L₁).mp h₁
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨b, hb⟩ := exists_not_mem_of_ne_univ hnu
  exact npAverageCompleteLanguage_of_nontrivial ((reduces a).mp ha)
    (fun h => hb ((reduces b).mpr h))

/-- The report's Theorem 4.4, with its hypotheses visibly unused. -/
theorem theorem_4_4_uses_only_correctness {L₁ L₂ : Set Bitstring}
    (r : HonestReduction.FaithfulReduction L₁ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁) (_ : InNP L₂) :
    TR1995.IsNPAverageCompleteLanguage L₂ :=
  npAverageCompleteLanguage_of_reduces r.map r.reduces h₁

end Gists.Theorem44Vacuous
