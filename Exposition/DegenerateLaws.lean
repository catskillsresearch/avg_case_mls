/-
Runnable snippet for arxiv.md.  Displayed alongside the discussion of the two
degenerate laws that drive the collapse results.

Both layers bound total mass by `1` rather than fixing it at `1`, and both
return rank `0` off support.  The everywhere-zero measure is therefore a legal
law whose rank vanishes identically -- which is what makes the rank domination
inequality free.

Checked against AvgCaseMls.AvCom and AvgCaseMls.Section4.
-/
import AvgCaseMls.AvCom
import AvgCaseMls.Section4

namespace Exposition.DegenerateLaws

/-! ## The untimed layer -/

section Untimed
open AvCom

/-- `prob_sum_le_one` bounds total mass by `1`, so this is a legal law. -/
def zeroDistribution : Distribution where
  support := ∅
  prob := fun _ => 0
  prob_nonneg := fun _ => le_refl 0
  prob_zero_outside := fun _ _ => rfl
  prob_sum_le_one := by simp

/-- Its rank vanishes everywhere, because `rank` returns `0` off support. -/
@[simp] theorem rank_zeroDistribution (x : Bitstring) :
    rank zeroDistribution x = 0 := by
  simp [rank, zeroDistribution]

/-- And a constant rank function is polynomially rankable. -/
theorem zeroDistribution_polRankable : IsPolRankable zeroDistribution :=
  ⟨fun _ => 0, ⟨0, 0, by simp⟩, fun x => by simp⟩

end Untimed

/-! ## The timed layer -/

section Timed
open AvgCaseMls.Foundation

/-- `tsum_le_one` likewise only bounds the mass. -/
noncomputable def zeroLaw : Subprobability where
  prob := fun _ => 0
  summable_prob := summable_zero
  tsum_le_one := by simp
  finite_superlevel := fun _ hx => absurd rfl hx

@[simp] theorem zeroLaw_prob (x : Bitstring) : zeroLaw.prob x = 0 := rfl

@[simp] theorem zeroLaw_rank (x : Bitstring) : zeroLaw.rank x = 0 :=
  Subprobability.rank_eq_zero_of_prob_eq_zero _ _ rfl

/-- It is not a probability measure; this is the defect the repair fixes. -/
theorem zeroLaw_mass : zeroLaw.mass = 0 := by
  simp [Subprobability.mass]

/-- Rankable in the timed sense too: a one-step constant program computes it. -/
theorem zeroLaw_rankable : IsPolynomialTimeRankable zeroLaw := by
  refine ⟨.constant true (encodeNat 0), fun _ => 1, IsPolynomial.const 1,
    monotone_const, ?_⟩
  intro x
  exact ⟨⟨true, encodeNat 0, 1⟩, rfl, by simp⟩

end Timed

end Exposition.DegenerateLaws
