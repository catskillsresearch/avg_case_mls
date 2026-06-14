/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS
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

open MLS AvCom

/-! ### MLS embedding (§3) -/

example : decideMLS (Formula.rel (Relation.eq Term.empty Term.empty)) = true := rfl

example : decideMLS (Formula.rel (Relation.neq Term.empty Term.empty)) = false := rfl

example : decideMLS (Formula.rel (Relation.mem Term.empty Term.empty)) = false := rfl

/-! ### AvCom helpers (§2) -/

example : len ([] : Bitstring) = 0 := rfl

example : len [true, false] = 2 := rfl

example : IsPolynomial (fun n => n + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

#eval decideMLS (Formula.rel (Relation.eq Term.empty Term.empty))
#eval decideMLS (Formula.rel (Relation.neq Term.empty Term.empty))
#eval len ([] : Bitstring)
#eval len [true, false, true]

end AvgCaseMls.Tests
