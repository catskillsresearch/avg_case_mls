/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.Logic
import AvgCaseMls.Section3.Probability
import AvgCaseMls.Section3.RandomCNF
import AvgCaseMls.Section3.Hypergraph
import AvgCaseMls.Section3.SDR
import AvgCaseMls.Section3.LocalSparsity
import AvgCaseMls.Section3.PropertyQ
import AvgCaseMls.Section3.Lemma4
import AvgCaseMls.Section3.Lemma5
import AvgCaseMls.Section3.Unsatisfiability

/-!
# Foundations for TR1995 / Chvátal--Szemerédi Section 3

This aggregate intentionally contains definitions and elementary correctness
lemmas only. It does not postulate local sparsity or any of CS87 Lemmas 1--5.
The Lemma 5 modules contain the completed unconditional proof components.
-/
