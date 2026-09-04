/-
Runnable snippet for arxiv.md, displayed with the third collapse theorem.

`AvCom.DistTime` reads

    ∃ f : Bitstring → Nat, IsAvTime T f prob.μ

where `f` is meant to be the running time of a decider for `prob.L`.  Nothing
ties `f` to any decider, or to `prob.L` at all, so `f ≡ 0` witnesses it.  The
consequence propagates all the way to the conditional hardness results: the
package that states the average-case collapse proves its own collapse, so no
package can assert the separation those results assume.

Checked against AvgCaseMls.ComplexityAxioms.
-/
import AvgCaseMls.ComplexityAxioms

namespace Exposition.AvPVacuous

open AvCom

/-- The free runtime witness. `T_inv T 0 = 0`, so every truncated sum vanishes. -/
theorem distTime_trivial (T : Nat → Nat) (p : DistributionalProblem) :
    DistTime T p := by
  refine ⟨fun _ => 0, ?_⟩
  intro l hl
  have hzero :
      (rankLe p.μ l).sum (fun x => (T_inv T 0 : Real) / (lenBot x : Real)) = 0 := by
    simp [T_inv]
  rw [hzero]
  exact_mod_cast Nat.zero_le l

/-- So average polynomial time degenerates to rankability of the law, a
statement that does not mention the language. -/
theorem avP_iff_polRankable (p : DistributionalProblem) :
    AvP p ↔ IsPolRankable p.μ :=
  ⟨fun h => h.1,
   fun h => ⟨h, fun _ => 0, ⟨0, 0, by simp⟩, distTime_trivial _ _⟩⟩

/-- And the inclusion the collapse package characterizes is a theorem. -/
theorem distNP_subseteq_AvP :
    ∀ p : DistributionalProblem, InDistNP p → AvP p :=
  fun p hp => (avP_iff_polRankable p).mpr hp.2

/-- Hence any such package proves its own `NEXP = EXP` ... -/
theorem collapse_forces_NEXP_eq_EXP (theory : AverageCaseCollapseTheory) :
    theory.NEXP_eq_EXP :=
  theory.distNP_subseteq_AvP_iff_NEXP_eq_EXP.mp distNP_subseteq_AvP

/-- ... and none can assert the separation, so every conditional hardness
theorem downstream has an unsatisfiable hypothesis. -/
theorem no_theory_separates (theory : AverageCaseCollapseTheory) :
    ¬ theory.NEXP_neq_EXP :=
  fun hsep => hsep (collapse_forces_NEXP_eq_EXP theory)

end Exposition.AvPVacuous
