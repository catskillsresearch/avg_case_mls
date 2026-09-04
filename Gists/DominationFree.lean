/-
Runnable gist for arxiv.md, displayed with the second collapse theorem.

Moving to the timed model repairs the verifier and the reduction map, but not
the domination condition.  Language-level completeness there is *equivalent* to
NP membership plus injective polynomial-time hardness: the rank domination
clause contributes nothing, because the degenerate law is still an admissible
target and its rank is identically zero.

`PolyTimeInjectiveReduction` is the reduction data with the three rank fields
deleted, so the statement below says exactly "domination is free".

Checked against AvgCaseMls.DominationCollapse.
-/
import AvgCaseMls.DominationCollapse

namespace Gists.DominationFree

open AvgCaseMls.Foundation AvgCaseMls.Section4

theorem isNPAverageCompleteLanguage_iff (L : Set Bitstring) :
    IsNPAverageCompleteLanguage L ↔
      InNP L ∧ ∀ source : DistributionalProblem, InDistNP source →
        Nonempty (PolyTimeInjectiveReduction source L) := by
  constructor
  · -- Forward: discard the domination data.
    rintro ⟨hInNP, hreduce⟩
    refine ⟨hInNP, ?_⟩
    intro source hsource
    obtain ⟨_, _, ⟨r⟩⟩ := hreduce source hsource
    exact ⟨PolyTimeInjectiveReduction.ofDistributional r⟩
  · -- Backward: supply the degenerate law and discharge domination with the
    -- zero rank factor.  Nothing about the source law is consulted.
    rintro ⟨hInNP, hhard⟩
    refine ⟨hInNP, ?_⟩
    intro source hsource
    obtain ⟨r⟩ := hhard source hsource
    exact ⟨zeroLaw, zeroLaw_rankable, ⟨r.toZeroLaw⟩⟩

end Gists.DominationFree
