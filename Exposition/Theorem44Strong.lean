/-
Runnable snippet for arxiv.md, displayed with Theorem 6 (TR1995 Theorem 4.4
on the timed layer).

Honest invertible reductions preserve language-level completeness when target
laws are polynomial-time rankable.  The proof pushes the source law forward
along the reduction map; rankability of the pushforward is rebuilt from range
recognition, the polynomial-time inverse, and the honesty bound.

Full proof in `AvgCaseMls/Section4.lean`.
-/
import AvgCaseMls.Section4

namespace Exposition.Theorem44Strong

open AvgCaseMls.Foundation AvgCaseMls.Section4

theorem theorem_4_4 {L₁ L₂ : Set Bitstring}
    (r : HonestInvertibleReduction L₁ L₂)
    (hL₂NP : InNP L₂)
    (hL₁ : IsNPAverageCompleteLanguage L₁) :
    IsNPAverageCompleteLanguage L₂ := by
  refine ⟨hL₂NP, ?_⟩
  intro source hsource
  obtain ⟨μ, hμRankable, sourceToL₁⟩ := hL₁.2 source hsource
  exact ⟨r.transport μ, r.transport_rankable hμRankable,
    ⟨InjectiveDistributionalReduction.trans sourceToL₁.some
      (r.distributionalReduction μ)⟩⟩

end Exposition.Theorem44Strong
