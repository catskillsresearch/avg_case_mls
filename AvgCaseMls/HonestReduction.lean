/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.TR1995

/-!
# Honest injective reductions and rank transport

This file formalizes the mathematical core of RS93, Theorem 7, and
TR1995-711, Theorem 4.4.  A finite-support distribution is transported along
an injective reduction.  Its mass, point probabilities, and probability-order
ranks are preserved exactly, so the reduction satisfies the domination
condition with constant one.

There is one unavoidable specialization.  Lean functions do not carry a
machine or an evaluation cost, so “polynomial time” cannot be stated in the
current `AvCom` model.  `FaithfulReduction` records the strongest available
extensional consequences: polynomial output-length growth, a total inverse
which recognizes the range and is a left inverse, and polynomial honesty.
The fields named `inverse` and `recognizesRange` express semantic
invertibility/range recognition, not a machine-level running-time theorem.

The finite-support restriction is inherited from `AvCom.Distribution`.
-/

open Finset

namespace HonestReduction

open AvCom

/--
An injective, invertible, honest language reduction, at the extensional level
supported by the current development.

`inverse` is only required to be meaningful on the range.  `inRange` makes
range recognition explicit instead of assigning an arbitrary inverse value
the status of a preimage.
-/
structure FaithfulReduction (L₁ L₂ : Set Bitstring) where
  map : Bitstring → Bitstring
  inverse : Bitstring → Bitstring
  inRange : Bitstring → Bool
  reduces : ∀ x, x ∈ L₁ ↔ map x ∈ L₂
  injective : Function.Injective map
  leftInverse : Function.LeftInverse inverse map
  recognizesRange : ∀ y, inRange y = true ↔ ∃ x, map x = y
  forwardLength :
    ∃ c k : Nat, ∀ x, lenBot (map x) ≤ c * lenBot x ^ k
  honest :
    ∃ c k : Nat, ∀ x, lenBot x ≤ c * lenBot (map x) ^ k

namespace FaithfulReduction

variable {L₁ L₂ : Set Bitstring} (r : FaithfulReduction L₁ L₂)

@[simp] theorem inRange_map (x : Bitstring) : r.inRange (r.map x) = true :=
  (r.recognizesRange (r.map x)).2 ⟨x, rfl⟩

@[simp] theorem inverse_map (x : Bitstring) : r.inverse (r.map x) = x :=
  r.leftInverse x

theorem map_inverse_of_inRange {y : Bitstring} (hy : r.inRange y = true) :
    r.map (r.inverse y) = y := by
  obtain ⟨x, rfl⟩ := (r.recognizesRange y).1 hy
  simp

/-- Honesty gives a polynomial output-length bound for the inverse on-range. -/
theorem inverseLength_of_inRange {y : Bitstring} (hy : r.inRange y = true) :
    ∃ c k : Nat, lenBot (r.inverse y) ≤ c * lenBot y ^ k := by
  obtain ⟨c, k, honest⟩ := r.honest
  refine ⟨c, k, ?_⟩
  calc
    lenBot (r.inverse y) ≤ c * lenBot (r.map (r.inverse y)) ^ k :=
      honest (r.inverse y)
    _ = c * lenBot y ^ k := by rw [r.map_inverse_of_inRange hy]

/-- The image of a finite support under the reduction. -/
def imageSupport (μ : Distribution) : Finset Bitstring :=
  μ.support.map ⟨r.map, r.injective⟩

/--
The source distribution transported to the image of `map`; points outside the
full range receive probability zero.  On range points, probability is read
through the explicit inverse.
-/
noncomputable def transportProb (μ : Distribution) (y : Bitstring) : Real :=
  if r.inRange y then μ.prob (r.inverse y) else 0

@[simp] theorem transportProb_map (μ : Distribution) (x : Bitstring) :
    r.transportProb μ (r.map x) = μ.prob x := by
  simp [transportProb]

/-- Push a finite-support distribution forward along an injective reduction. -/
noncomputable def transport (μ : Distribution) : Distribution where
  support := r.imageSupport μ
  prob := r.transportProb μ
  prob_nonneg y := by
    unfold transportProb
    split <;> simp_all [μ.prob_nonneg]
  prob_zero_outside y hy := by
    unfold transportProb
    split_ifs with hrange
    · obtain ⟨x, hx⟩ := (r.recognizesRange y).1 hrange
      subst y
      rw [r.inverse_map]
      apply μ.prob_zero_outside
      simpa [imageSupport] using hy
    · rfl
  prob_sum_le_one := by
    rw [show (r.imageSupport μ).sum (r.transportProb μ) = μ.support.sum μ.prob by
      simp [imageSupport]]
    exact μ.prob_sum_le_one

@[simp] theorem transport_support (μ : Distribution) :
    (r.transport μ).support = r.imageSupport μ :=
  rfl

@[simp] theorem transport_prob_map (μ : Distribution) (x : Bitstring) :
    (r.transport μ).prob (r.map x) = μ.prob x :=
  r.transportProb_map μ x

theorem transport_mass (μ : Distribution) :
    (r.transport μ).mass = μ.mass := by
  simp [Distribution.mass, transport, imageSupport]

/--
Probability-order rank is preserved exactly on mapped points.  This is the
finite-support realization of `ρ₂(f(x)) = ρ₁(x)` in RS93 Theorem 7.
-/
theorem rank_transport_map (μ : Distribution) (x : Bitstring) :
    rank (r.transport μ) (r.map x) = rank μ x := by
  unfold rank
  rw [r.transport_prob_map]
  split_ifs with hx
  · rfl
  · rw [show
      (r.transport μ).support.filter
          (fun z => μ.prob x ≤ (r.transport μ).prob z) =
        (μ.support.filter (fun z => μ.prob x ≤ μ.prob z)).map
          ⟨r.map, r.injective⟩ by
      ext y
      simp only [transport_support, imageSupport, mem_filter, mem_map]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hprob⟩
        exact ⟨z, ⟨hz, by simpa using hprob⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hprob⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, by simpa using hprob⟩]
    exact card_map ⟨r.map, r.injective⟩

/--
The transported map is a distributional reduction.  Rank domination is exact;
the extra `lenBot x` factor appears only because `AvCom.DistributionalReduction`
requires a positive rank exponent.
-/
theorem distributionalReduction (μ : Distribution) :
    DistributionalReduction ⟨L₁, μ⟩ ⟨L₂, r.transport μ⟩ := by
  obtain ⟨c, k, hlen⟩ := r.forwardLength
  refine ⟨r.map, r.reduces, ⟨c, k, hlen⟩, ⟨1, 1, one_pos, one_pos, ?_⟩⟩
  intro x
  rw [r.rank_transport_map]
  simp only [one_mul, pow_one]
  exact Nat.le_mul_of_pos_left _ (lenBot_ne_zero x)

end FaithfulReduction

/--
Every distribution in the current finite-support model is polynomially
rankable by a constant.  This is stronger than needed for transport, and also
pinpoints why the present model cannot represent the paper's rank-computation
cost argument.
-/
theorem finiteSupport_polRankable (μ : Distribution) : IsPolRankable μ :=
  ⟨fun _ => μ.support.card, IsPolynomial.const μ.support.card,
    IsTRankable.of_support _ _ fun x _ => rank.le_support_card μ x⟩

/--
The language-level conclusion of RS93 Theorem 7 / TR1995-711 Theorem 4.4.

Membership of `L₂` in NP is explicit: an injective many-one reduction from an
NP-complete language proves NP-hardness, but by itself does not prove that the
target is in NP.  The papers use the theorem for targets already known to lie
in NP.
-/
theorem npAverageCompleteLanguage_of_faithfulReduction
    {L₁ L₂ : Set Bitstring}
    (r : FaithfulReduction L₁ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁)
    (h₂NP : InNP L₂) :
    TR1995.IsNPAverageCompleteLanguage L₂ := by
  refine ⟨h₂NP, ?_⟩
  intro source hsource
  obtain ⟨μ, _hμ, hsourceToL₁⟩ := h₁.2 source hsource
  exact
    ⟨r.transport μ, finiteSupport_polRankable (r.transport μ),
      DistributionalReduction.trans hsourceToL₁ (r.distributionalReduction μ)⟩

end HonestReduction
