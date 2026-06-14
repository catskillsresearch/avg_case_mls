/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS
import AvgCaseMls.EMLS
import AvgCaseMls.DecideMLS
import AvgCaseMls.AvCom

/-!
Smoke tests for the MLS embedding and computable fragments of the AvCom definitions.

Run printed values:

```bash
./run_lean_tests.sh
# or
lake build AvgCaseMls.Tests 2>&1 | grep "^info: AvgCaseMls/Tests"
```
-/

namespace AvgCaseMls.Tests

open MLS EMLS AvCom

/-! ### MLS embedding (§6) -/

example : decideMLSSat (Formula.rel (Relation.eq Term.empty Term.empty)) = true := rfl

example : decideMLSSat (Formula.rel (Relation.neq Term.empty Term.empty)) = false := rfl

example : decideMLSSat (Formula.rel (Relation.mem Term.empty Term.empty)) = false := rfl

/-! ### FOS80 EMLS conjuncts (§7) -/

example : decideConjunct [.neq 0 0] = false := rfl

example : decideConjunct [.mem 0 1, .notMem 0 1] = false := rfl

example : decideConjunct [.eqEmpty 0] = true := rfl

example :
    decideMLSSat (Formula.and (Formula.rel (Relation.mem (Term.var 0) (Term.var 1)))
      (Formula.rel (Relation.not_mem (Term.var 0) (Term.var 1)))) = false := rfl

/-! ### AvCom helpers (§5) -/

example : len ([] : Bitstring) = 0 := rfl

example : len [true, false] = 2 := rfl

example : IsPolynomial (fun n => n + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

#eval decideMLSSat (Formula.rel (Relation.eq Term.empty Term.empty))
#eval decideConjunct [.mem 0 1]
#eval decideConjunct [.mem 0 0]
#eval len ([] : Bitstring)
#eval len [true, false, true]

end AvgCaseMls.Tests
