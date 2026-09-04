/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/
import AvgCaseMls.ComplexityAxioms
import AvgCaseMls.EncodingCollapse

/-!
# The conditional hardness chain is vacuous

`AvgCaseMls.EncodingCollapse` shows that the untimed `AvCom` encoding of
average-case *completeness* has no complexity content.  This file shows the
same for the average-case *tractability* class `AvCom.AvP`, and draws the
consequence for the conditional hardness results.

The defect is in `AvCom.DistTime`:

```
def DistTime (T : Nat → Nat) (prob : DistributionalProblem) : Prop :=
  ∃ f : Bitstring → Nat, IsAvTime T f prob.μ
```

The existentially quantified `f` is meant to be the running time of a decider
for `prob.L`, but nothing ties it to any decider, or to `prob.L` at all.
Taking `f ≡ 0` gives `T_inv T 0 = 0`, so every rank-truncated sum vanishes and
[`distTime_trivial`] holds for every bound and every problem.  Hence
[`avP_iff_polRankable`]: `AvP` is just polynomial rankability of the law, with
no reference to the language, and [`distNP_subseteq_AvP`] holds outright.

That is already fatal, but the consequence for
`AverageCaseCollapseTheory` is sharper.  That package asserts

```
distNP_subseteq_AvP_iff_NEXP_eq_EXP : (∀ p, InDistNP p → AvP p) ↔ NEXP_eq_EXP
```

Since the left side is a theorem, any such package proves its own
`NEXP_eq_EXP` ([`collapse_forces_NEXP_eq_EXP`]), so no package can assert the
separation ([`no_theory_separates`]).  Every theorem in `AvgCaseMls.NonAvP`
takes `theory.NEXP_neq_EXP` as a hypothesis, and that hypothesis is
unsatisfiable: the conditional hardness results are not merely conditional,
they are vacuous.
-/

namespace AvgCaseMls.HardnessCollapse

open AvCom

/-! ## `AvP` does not mention the language -/

/--
`DistTime` holds for every bound and every distributional problem.  The
existential runtime witness `f ≡ 0` is legal because `DistTime` never requires
`f` to be the running time of a decider for the language.
-/
theorem distTime_trivial (T : Nat → Nat) (p : DistributionalProblem) :
    DistTime T p := by
  refine ⟨fun _ => 0, ?_⟩
  intro l hl
  have hzero :
      (rankLe p.μ l).sum (fun x => (T_inv T 0 : Real) / (lenBot x : Real)) = 0 := by
    simp [T_inv]
  rw [hzero]
  exact_mod_cast Nat.zero_le l

/-- Consequently `AvP` degenerates to polynomial rankability of the law. -/
theorem avP_iff_polRankable (p : DistributionalProblem) :
    AvP p ↔ IsPolRankable p.μ :=
  ⟨fun h => h.1,
   fun h => ⟨h, fun _ => 0, ⟨0, 0, by simp⟩, distTime_trivial _ _⟩⟩

/-- Every distributional NP problem is in `AvP`, unconditionally. -/
theorem distNP_subseteq_AvP :
    ∀ p : DistributionalProblem, InDistNP p → AvP p :=
  fun p hp => (avP_iff_polRankable p).mpr hp.2

/-! ## No collapse theory can assert the separation -/

/--
Any `AverageCaseCollapseTheory` proves its own `NEXP_eq_EXP`, because its
characterizing field is an iff whose left-hand side is
[`distNP_subseteq_AvP`], a theorem.
-/
theorem collapse_forces_NEXP_eq_EXP (theory : AverageCaseCollapseTheory) :
    theory.NEXP_eq_EXP :=
  theory.distNP_subseteq_AvP_iff_NEXP_eq_EXP.mp distNP_subseteq_AvP

/--
**The conditional hardness chain is vacuous.**  No `AverageCaseCollapseTheory`
satisfies `NEXP_neq_EXP`, so every theorem in `AvgCaseMls.NonAvP` that assumes
it -- `nbhProb_not_AvP`, `satMLSProb_not_AvP`, `SatMLS_average_hard`,
`exists_simple_rankable_not_AvP`, `SatMLS_semantic_not_AvP`, and the rest --
has an unsatisfiable hypothesis.
-/
theorem no_theory_separates (theory : AverageCaseCollapseTheory) :
    ¬ theory.NEXP_neq_EXP :=
  fun hsep => hsep (collapse_forces_NEXP_eq_EXP theory)

end AvgCaseMls.HardnessCollapse
