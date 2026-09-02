/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.Logic
import AvgCaseMls.Section3.Probability

/-!
# Random ordinary CNFs

The sample is an ordered function `Fin m → OrdinaryClause n k`. Thus two
equal clauses sampled at different coordinates remain distinct trials.
-/

namespace AvgCaseMls.Section3

abbrev OrdinaryCNF (n m k : Nat) := Fin m → OrdinaryClause n k

theorem ordinaryCNF_cardinality :
    Fintype.card (OrdinaryCNF n m k) = (n.choose k * 2 ^ k) ^ m := by
  rw [Fintype.card_fun, Fintype.card_fin, ordinaryClause_cardinality]

/--
`m` independent uniform draws from the ordinary clause space. The `Nonempty`
assumption is precisely the condition needed for a probability distribution;
in intended uses it follows from `k ≤ n`.
-/
noncomputable def randomCNF (n m k : Nat) [Nonempty (OrdinaryClause n k)] :
    FinitePMF (OrdinaryCNF n m k) :=
  FinitePMF.uniform (OrdinaryCNF n m k)

/-- The paper's random CNF under its natural feasibility condition. -/
noncomputable def randomCNFOfLE (n m k : Nat) (hk : k ≤ n) :
    FinitePMF (OrdinaryCNF n m k) := by
  letI : Nonempty (OrdinaryClause n k) := ordinaryClause_nonempty hk
  exact randomCNF n m k

@[simp] theorem randomCNF_apply (F : OrdinaryCNF n m k)
    [Nonempty (OrdinaryClause n k)] :
    (randomCNF n m k).prob F =
      1 / (Fintype.card (OrdinaryClause n k) : ℝ) ^ m := by
  rw [randomCNF, FinitePMF.uniform_apply, Fintype.card_fun, Fintype.card_fin]
  norm_cast

/--
The joint density factors as the product of the `m` uniform one-clause
densities, the finite-space formulation of independent uniform sampling.
-/
theorem randomCNF_density_factors (F : OrdinaryCNF n m k)
    [Nonempty (OrdinaryClause n k)] :
    (randomCNF n m k).prob F =
      ∏ _i : Fin m, (FinitePMF.uniform (OrdinaryClause n k)).prob (F _i) := by
  rw [randomCNF_apply]
  simp [FinitePMF.uniform_apply, one_div]

def eraseOrdinary (F : OrdinaryCNF n m k) : CNF n m :=
  fun i => (F i).lits

@[simp] theorem eraseOrdinary_card (F : OrdinaryCNF n m k) (i : Fin m) :
    (eraseOrdinary F i).card = k := (F i).lits_card

theorem eraseOrdinary_no_complement (F : OrdinaryCNF n m k) (i : Fin m)
    {l : Literal n} (hl : l ∈ eraseOrdinary F i) :
    l.complement ∉ eraseOrdinary F i :=
  (F i).complement_not_mem hl

end AvgCaseMls.Section3
