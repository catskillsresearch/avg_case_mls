/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Reduction

/-!
Phase **4C:** NP-average completeness of MLS satisfiability (TR1995-711 Corollary 5.1).

Literature: every distNP problem reduces to bounded halting (NBH); Phase **4B**
reduces NBH into [`satMLSProb`]. The two unfinished constructions are explicit
arguments below, not project axioms.
-/

namespace Completeness

open Reduction AvCom NBH

/-- Explicit package for the unfinished Levin universal NBH reduction. -/
structure LevinNBHData where
  reduces : ∀ source : DistributionalProblem, InDistNP source →
    DistributionalReduction source nbhProb

theorem nbhProb_NPAverageComplete (levin : LevinNBHData) :
    IsNPAverageComplete nbhProb :=
  IsNPAverageComplete.intro nbhProb_in_DistNP levin.reduces

/--
Corollary 5.1 (adapted): [`satMLSProb`] is NP-average complete, via NBH completeness and
[`nbhToSatMLS_red`].
-/
theorem satMLSProb_NPAverageComplete
    (levin : LevinNBHData) (compiler : NBHToMLSData) :
    IsNPAverageComplete satMLSProb :=
  IsNPAverageComplete.of_reductor satMLSProb_in_DistNP
    (nbhProb_NPAverageComplete levin) (nbhToSatMLS_red compiler)

end Completeness
