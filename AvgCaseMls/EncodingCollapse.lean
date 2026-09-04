/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/
import AvgCaseMls.TR1995
import AvgCaseMls.HonestReduction

/-!
# The finite-support encoding of RS93 domination collapses

This file records a negative result about the `AvCom` layer, which encodes
Reischuk--Schindelhauer average-case completeness using finite-support
subprobabilities and a rank function that returns `0` off support.

Three independent weaknesses combine:

* `AvCom.InNP` bounds certificate *length* but places no complexity bound on
  the verifier, so it holds for every language ([`inNP_trivial`]).
* `AvCom.Distribution` requires total mass `≤ 1` rather than `= 1`, so the
  everywhere-zero measure is a legal distribution ([`zeroDistribution`]).
* `AvCom.rank` returns `0` wherever the probability is `0`, so that measure has
  rank identically `0` and the domination inequality becomes `0 ≤ _`.

Consequently `TR1995.IsNPAverageCompleteLanguage` is equivalent to the purely
set-theoretic statement that the language is neither empty nor everything
([`npAverageCompleteLanguage_iff_nontrivial`]), and TR1995 Theorem 4.4 follows
from the single `reduces` field of `HonestReduction.FaithfulReduction`, using
none of injectivity, invertibility, range recognition, or honesty
([`npAverageCompleteLanguage_of_reduces`]).

The moral is not that the report is wrong but that this encoding of its
vocabulary carries no complexity content.  `AvgCaseMls.Foundation` and
`AvgCaseMls.Section4` supply the timed replacements.
-/

namespace AvgCaseMls.EncodingCollapse

open AvCom

/-! ## The everywhere-zero distribution -/

/-- The everywhere-zero measure, which `prob_sum_le_one` admits because it
bounds total mass by `1` instead of fixing it at `1`. -/
def zeroDistribution : Distribution where
  support := ∅
  prob := fun _ => 0
  prob_nonneg := fun _ => le_refl 0
  prob_zero_outside := fun _ _ => rfl
  prob_sum_le_one := by simp

@[simp] theorem rank_zeroDistribution (x : Bitstring) :
    rank zeroDistribution x = 0 := by
  simp [rank, zeroDistribution]

/-- Rank is identically `0`, so the constant polynomial `0` bounds it. -/
theorem zeroDistribution_polRankable : IsPolRankable zeroDistribution :=
  ⟨fun _ => 0, ⟨0, 0, by simp⟩, fun x => by simp⟩

/-! ## `AvCom.InNP` holds for every language -/

/--
`AvCom.InNP` is provable for *every* language.  The definition quantifies over
an arbitrary function `verify : Bitstring → Bitstring → Bool` and constrains
only the certificate length, never the cost of running `verify`; the classical
decision procedure for `L` therefore witnesses it with the empty certificate.
-/
theorem inNP_trivial (L : Set Bitstring) : InNP L := by
  classical
  refine ⟨fun x _ => decide (x ∈ L), fun _ => 0, ⟨0, 0, by simp⟩, ?_⟩
  intro x
  exact ⟨fun hx => ⟨[], by simp [len], by simpa using hx⟩,
         fun ⟨_, _, hv⟩ => by simpa using hv⟩

/-- Every language paired with the zero measure is a distributional NP problem. -/
theorem inDistNP_zeroDistribution (S : Set Bitstring) :
    InDistNP ⟨S, zeroDistribution⟩ :=
  ⟨inNP_trivial S, zeroDistribution_polRankable⟩

/-! ## Set-theoretic characterization -/

theorem exists_not_mem_of_ne_univ {L : Set Bitstring}
    (h : L ≠ Set.univ) : ∃ b, b ∉ L := by
  by_contra hc
  exact h (Set.eq_univ_of_forall fun x => not_not.mp fun hx => hc ⟨x, hx⟩)

theorem ne_univ_of_exists_not_mem {L : Set Bitstring}
    (h : ∃ b, b ∉ L) : L ≠ Set.univ := by
  obtain ⟨b, hb⟩ := h
  intro hL
  rw [hL] at hb
  exact hb (Set.mem_univ b)

/--
**The collapse.**  Language-level NP-average completeness in the `AvCom`
encoding is equivalent to the language being a nontrivial subset of
`Bitstring`.

For the interesting direction, take the target distribution to be
[`zeroDistribution`]: its rank vanishes identically, so the domination
inequality reads `0 ≤ _` and is free, and the reduction map may be taken to be
the two-valued function sending members of the source language to a fixed
member of `L` and non-members to a fixed non-member.  That map satisfies the
correctness biconditional by construction and has constant output length.
Nothing about computability is required of it, because `AvCom` never asks for
any.
-/
theorem npAverageCompleteLanguage_iff_nontrivial (L : Set Bitstring) :
    TR1995.IsNPAverageCompleteLanguage L ↔ (L ≠ ∅ ∧ L ≠ Set.univ) := by
  classical
  constructor
  · rintro ⟨-, hreduce⟩
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
  · rintro ⟨hne, hnu⟩
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨b, hb⟩ := exists_not_mem_of_ne_univ hnu
    refine ⟨inNP_trivial L, ?_⟩
    intro source _
    refine ⟨zeroDistribution, zeroDistribution_polRankable,
      fun x => if x ∈ source.L then a else b, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ source.L <;> simp [hx, ha, hb]
    · exact ⟨lenBot a + lenBot b, 0, by
        intro x
        by_cases hx : x ∈ source.L <;> simp [hx, lenBot]⟩
    · exact ⟨1, 1, one_pos, one_pos, fun x => by simp⟩

/-- Every nontrivial language is NP-average complete in this encoding. -/
theorem npAverageCompleteLanguage_of_nontrivial {L : Set Bitstring}
    {a b : Bitstring} (ha : a ∈ L) (hb : b ∉ L) :
    TR1995.IsNPAverageCompleteLanguage L :=
  (npAverageCompleteLanguage_iff_nontrivial L).mpr
    ⟨Set.nonempty_iff_ne_empty.mp ⟨a, ha⟩, ne_univ_of_exists_not_mem ⟨b, hb⟩⟩

/-! ## TR1995 Theorem 4.4 needs only the correctness field -/

/--
Completeness transfers along *any* map satisfying the correctness
biconditional, with no further hypotheses whatsoever: push a member and a
non-member of `L₁` through `map` to see that `L₂` is again nontrivial.
-/
theorem npAverageCompleteLanguage_of_reduces {L₁ L₂ : Set Bitstring}
    (map : Bitstring → Bitstring) (reduces : ∀ x, x ∈ L₁ ↔ map x ∈ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁) :
    TR1995.IsNPAverageCompleteLanguage L₂ := by
  obtain ⟨hne, hnu⟩ := (npAverageCompleteLanguage_iff_nontrivial L₁).mp h₁
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨b, hb⟩ := exists_not_mem_of_ne_univ hnu
  exact npAverageCompleteLanguage_of_nontrivial ((reduces a).mp ha)
    (fun h => hb ((reduces b).mpr h))

/--
**TR1995 Theorem 4.4 carries no content in this encoding.**  The proof term
mentions only `r.map` and `r.reduces`.  The `injective`, `leftInverse`,
`recognizesRange`, `forwardLength`, and `honest` fields -- precisely the
hypotheses "injective, polynomial time invertible, and honest" that the
report's Theorem 4.4 is about -- are never used, and neither is the `InNP L₂`
hypothesis, which [`inNP_trivial`] supplies for free.
-/
theorem theorem_4_4_uses_only_correctness {L₁ L₂ : Set Bitstring}
    (r : HonestReduction.FaithfulReduction L₁ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁) (_ : InNP L₂) :
    TR1995.IsNPAverageCompleteLanguage L₂ :=
  npAverageCompleteLanguage_of_reduces r.map r.reduces h₁

end AvgCaseMls.EncodingCollapse
