/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.AverageTime

namespace AvgCaseMls.Foundation

/-- Self-delimiting pairing: `0^|x| 1 x certificate`. -/
def pair (x certificate : Bitstring) : Bitstring :=
  List.replicate x.length false ++ true :: x ++ certificate

@[simp] theorem pair_length (x certificate : Bitstring) :
    (pair x certificate).length = 2 * x.length + certificate.length + 1 := by
  simp [pair]
  omega

def VerifiesWithin (program : Program) (x certificate : Bitstring)
    (time : Nat → Nat) : Prop :=
  ∃ r, program.eval (time (len (pair x certificate))) (pair x certificate) = some r ∧
    r.accept = true

theorem verifiesWithin_iff {program : Program} {accepted : Set Bitstring}
    {time : Nat → Nat} (h : DecidesWithin program accepted time)
    (x certificate : Bitstring) :
    VerifiesWithin program x certificate time ↔ pair x certificate ∈ accepted := by
  obtain ⟨r, hr, hcorrect⟩ := h (pair x certificate)
  constructor
  · rintro ⟨r', hr', haccept⟩
    rw [hr] at hr'
    cases hr'
    exact hcorrect.mp haccept
  · intro hmem
    exact ⟨r, hr, hcorrect.mpr hmem⟩

/--
Timed NP verification has both polynomial certificate size and polynomial fuel
for the concrete verifier execution.
-/
def InTimedNP (L : Set Bitstring) : Prop :=
  ∃ verifier : Program, ∃ acceptedPairs certificateBound timeBound,
    IsPolynomial certificateBound ∧
    IsPolynomial timeBound ∧
    DecidesWithin verifier acceptedPairs timeBound ∧
    ∀ x, x ∈ L ↔ ∃ certificate,
      len certificate ≤ certificateBound (len x) ∧
      pair x certificate ∈ acceptedPairs

/-- NP in the concrete verifier model. -/
abbrev InNP := InTimedNP

/-- NEXP via exponentially bounded certificates and deterministic verification. -/
def InNEXP (L : Set Bitstring) : Prop :=
  ∃ verifier acceptedPairs certificateBound timeBound,
    IsExponential certificateBound ∧
    IsExponential timeBound ∧
    DecidesWithin verifier acceptedPairs timeBound ∧
    ∀ x, x ∈ L ↔ ∃ certificate,
      len certificate ≤ certificateBound (len x) ∧
      pair x certificate ∈ acceptedPairs

end AvgCaseMls.Foundation
