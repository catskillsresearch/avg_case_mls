/-
Runnable versions of the proofs displayed in `arxiv.md`.

Each snippet restates the theorem under discussion and re-proves it (or points
to the library proof when the argument exceeds ten lines), importing its
dependencies from `AvgCaseMls`.  Build with `lake build Exposition`, or run
`scripts/check_exposition.sh` to check each file independently.
-/

import Exposition.ResolutionLowerBound
import Exposition.Example41
import Exposition.Reductions
import Exposition.Theorem44Strong

import Exposition.DegenerateLaws
import Exposition.InNPTrivial
import Exposition.CompletenessCharacterization
import Exposition.Theorem44Vacuous
import Exposition.DominationFree
import Exposition.AvPVacuous

import Exposition.Repair
