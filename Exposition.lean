/-
Runnable versions of the proofs displayed in `arxiv.md`.

Each snippet restates the theorem under discussion and re-proves it, importing
its dependencies from `AvgCaseMls`, so that the Lean next to each English
proof in the paper is genuinely checkable rather than illustrative.  Build
with `lake build Exposition`, or run `scripts/check_exposition.sh` to check
each file independently.
-/

-- The positive results.
import Exposition.ResolutionLowerBound
import Exposition.Example41
import Exposition.Reductions

-- The three collapses.
import Exposition.DegenerateLaws
import Exposition.InNPTrivial
import Exposition.CompletenessCharacterization
import Exposition.Theorem44Vacuous
import Exposition.DominationFree
import Exposition.AvPVacuous

-- The repairs.
import Exposition.Repair
