/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom

open AvCom

/-!
Minimal complexity collapse hypothesis for conditional average-case hardness (Phase **5**).

Literature: TR1995-711 Corollary 5.1 consequence - NP-average complete targets are not in AvP
unless $\\text{NEXP} = \\text{EXP}$. Mathlib does not yet host this implication; we axiomatize
only the collapse hypothesis, not the full proof.
-/

/-- Nondeterministic exponential time is strictly larger than deterministic exponential time. -/
axiom NEXP_neq_EXP : Prop

def NEXP_eq_EXP : Prop := not  NEXP_neq_EXP

/--
Levin / TR1995-711 collapse equivalence: distNP is average-case tractable iff NEXP = EXP.

Literature: decades of structural complexity; full proof is out of scope for this project.
-/
axiom distNP_subseteq_AvP_iff_NEXP_eq_EXP :
  (forall p, InDistNP p -> AvP p) <-> NEXP_eq_EXP

/--
AvP pulls back along distributional reductions from a complete distNP target.

Literature: compose a poly-time decider for the target with the reduction map; deferred until
[`DistTime`] is linked to concrete deciders.
-/
axiom AvP_pullback {source target : DistributionalProblem}
    (hAvP : AvP target) (hRed : DistributionalReduction source target) :
    AvP source
