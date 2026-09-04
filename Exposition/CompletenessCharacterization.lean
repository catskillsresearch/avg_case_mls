/-
Runnable snippet for arxiv.md, displayed with the first collapse theorem.

Language-level NP-average completeness in the report's untimed vocabulary is
equivalent to the language being neither empty nor everything.  The degenerate
law supplies the target: its rank vanishes identically, so domination reads
`0 ≤ _`, and the reduction map may be the two-valued function sending members
of the source to a fixed member of `L` and non-members to a fixed non-member.

Checked against AvgCaseMls.EncodingCollapse.
-/
import AvgCaseMls.EncodingCollapse

namespace Exposition.CompletenessCharacterization

open AvCom AvgCaseMls.EncodingCollapse

theorem npAverageCompleteLanguage_iff_nontrivial (L : Set Bitstring) :
    TR1995.IsNPAverageCompleteLanguage L ↔ (L ≠ ∅ ∧ L ≠ Set.univ) := by
  classical
  constructor
  · -- Forward: reduce from `univ` to find a member, from `∅` to find a
    -- non-member.  Only the correctness field of the reduction is touched.
    rintro ⟨-, hreduce⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨μ, -, f, hcorrect, -, -⟩ :=
        hreduce ⟨Set.univ, zeroDistribution⟩ (inDistNP_zeroDistribution _)
      intro hL
      have hmem : f [] ∈ L := (hcorrect []).mp (Set.mem_univ _)
      rw [hL] at hmem
      exact hmem
    · obtain ⟨μ, -, f, hcorrect, -, -⟩ :=
        hreduce ⟨∅, zeroDistribution⟩ (inDistNP_zeroDistribution _)
      exact ne_univ_of_exists_not_mem ⟨f [], fun h => (hcorrect []).mpr h⟩
  · -- Backward: nontriviality is all the definition asks for.
    rintro ⟨hne, hnu⟩
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨b, hb⟩ := exists_not_mem_of_ne_univ hnu
    refine ⟨inNP_trivial L, ?_⟩
    intro source _
    refine ⟨zeroDistribution, zeroDistribution_polRankable,
      fun x => if x ∈ source.L then a else b, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ source.L <;> simp [hx, ha, hb]
    · -- Constant output length, so the length bound is satisfied.
      exact ⟨lenBot a + lenBot b, 0, by
        intro x
        by_cases hx : x ∈ source.L <;> simp [hx, lenBot]⟩
    · -- Domination is `0 ≤ _`, because the target rank is identically zero.
      exact ⟨1, 1, one_pos, one_pos, fun x => by simp⟩

end Exposition.CompletenessCharacterization
