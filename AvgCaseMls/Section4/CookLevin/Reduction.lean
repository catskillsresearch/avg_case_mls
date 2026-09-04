import AvgCaseMls.Foundation.Reduction
import AvgCaseMls.Section4.CookLevin.SATCodec

/-!
# Distributional packaging of the local Cook--Levin map

The source distribution is arbitrary. The target is its exact injective
pushforward along the total serialized local compiler, and hence has zero
mass off the compiler range and preserves rank on every source string.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

noncomputable def encodedBoundedAcceptanceProblem
    (sourceDistribution : Subprobability) : DistributionalProblem where
  language := EncodedBoundedAcceptance
  distribution := sourceDistribution

noncomputable def encodedLocalSATProblem
    (sourceDistribution : Subprobability) : DistributionalProblem where
  language := EncodedSAT
  distribution := sourceDistribution.pushforward compileEncodedLocalSAT
    compileEncodedLocalSAT_injective

@[simp] theorem encodedLocalSATProblem_prob_compile
    (sourceDistribution : Subprobability) (source : Bitstring) :
    (encodedLocalSATProblem sourceDistribution).distribution.prob
        (compileEncodedLocalSAT source) =
      sourceDistribution.prob source := by
  exact Subprobability.pushforward_prob_map sourceDistribution
    compileEncodedLocalSAT compileEncodedLocalSAT_injective source

theorem encodedLocalSATProblem_prob_eq_zero_off_range
    (sourceDistribution : Subprobability) (target : Bitstring)
    (hoff : target ∉ Set.range compileEncodedLocalSAT) :
    (encodedLocalSATProblem sourceDistribution).distribution.prob target = 0 := by
  exact Subprobability.pushforwardProb_eq_zero_of_not_mem_range
    sourceDistribution compileEncodedLocalSAT hoff

@[simp] theorem encodedLocalSATProblem_rank_compile
    (sourceDistribution : Subprobability) (source : Bitstring) :
    (encodedLocalSATProblem sourceDistribution).distribution.rank
        (compileEncodedLocalSAT source) =
      sourceDistribution.rank source := by
  exact Subprobability.rank_pushforward_map sourceDistribution
    compileEncodedLocalSAT compileEncodedLocalSAT_injective source

theorem encodedLocalSATProblem_correct (sourceDistribution : Subprobability)
    (source : Bitstring) :
    source ∈ (encodedBoundedAcceptanceProblem sourceDistribution).language ↔
      compileEncodedLocalSAT source ∈
        (encodedLocalSATProblem sourceDistribution).language :=
  (compileEncodedLocalSAT_mem_iff source).symm

end AvgCaseMls.Section4.CookLevin
