/-
Runnable gist for arxiv.md, displayed with the proof that the report's
membership condition is vacuous.

`AvCom.InNP` quantifies over an arbitrary function
`verify : Bitstring → Bitstring → Bool` and constrains only the length of the
certificate.  Nothing bounds the cost of running `verify`, so the classical
decision procedure for `L` witnesses membership with the empty certificate.

Checked against AvgCaseMls.AvCom.
-/
import AvgCaseMls.AvCom

namespace Gists.InNPTrivial

open AvCom

/-- Every language is in the report's `NP`. -/
theorem inNP_trivial (L : Set Bitstring) : InNP L := by
  classical
  -- The verifier is the characteristic function of `L`; the certificate bound
  -- is the zero polynomial, so certificates must be empty.
  refine ⟨fun x _ => decide (x ∈ L), fun _ => 0, ⟨0, 0, by simp⟩, ?_⟩
  intro x
  exact ⟨fun hx => ⟨[], by simp [len], by simpa using hx⟩,
         fun ⟨_, _, hv⟩ => by simpa using hv⟩

end Gists.InNPTrivial
