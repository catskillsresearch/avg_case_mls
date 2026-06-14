/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AverageHardness
import AvgCaseMls.Serialization
import AvgCaseMls.DecideMLS

/-!
Phase **3A:** certificate-based NP membership for MLS satisfiability.

The semantic language [`SatMLS`] uses noncomputable [`evalFormula`]. The NP-verifiable
proxy [`SatMLSChecker`] decodes an input and runs [`decideMLSSat`]; see
[`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace MLS

open AvCom

/-- Poly-time verifiable MLS satisfiability on well-formed encodings. -/
def SatMLSChecker : Set Bitstring :=
  { s |
    match decodeFormula? s with
    | none => False
    | some (f, rest) => rest = [] ∧ decideMLSSat f = true }

/--
NP verifier: decode the formula from `x` and run [`decideMLSSat`]. The certificate is
unused (length bound `0`); see Phase **3A** fork in [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
def verifySatMLS (x _cert : Bitstring) : Bool :=
  match decodeFormula? x with
  | none => false
  | some (f, rest) => decide (rest = [] && decideMLSSat f)

def satCertBound (_n : Nat) : Nat := 0

theorem satCertBound_poly : IsPolynomial satCertBound :=
  IsPolynomial.const 0

theorem verifySatMLS_true_iff (x : Bitstring) :
    verifySatMLS x [] = true ↔ x ∈ SatMLSChecker := by
  simp [verifySatMLS, SatMLSChecker, Bool.and_eq_true, decide_eq_true_iff]
  split <;> simp [Bool.and_eq_true, decide_eq_true_iff]

theorem SatMLSChecker_in_NP : InNP SatMLSChecker :=
  InNP.intro satCertBound_poly fun x => by
    constructor
    · intro hx
      refine ⟨[], by simp [satCertBound], ?_⟩
      exact (verifySatMLS_true_iff x).mpr hx
    · intro ⟨cert, hlen, hver⟩
      have hc : cert = [] := by simpa [satCertBound] using hlen
      subst hc
      exact (verifySatMLS_true_iff x).mp hver

theorem SatMLSChecker_subset_SatMLS (s : Bitstring) (h : s ∈ SatMLSChecker)
    {f : Formula} (hf : serializeFormula f = s) (hfrag : InDecideSoundFormula f) :
    s ∈ SatMLS := by
  have hdec : decodeFormula? s = some (f, []) := by
    rw [← hf, decodeFormula?_serializeFormula]
  simp [SatMLSChecker, hdec] at h
  obtain ⟨env, he⟩ := decideMLSSat_sound f h hfrag
  exact ⟨f, hf, env, he⟩

end MLS
