/-
Runnable versions of the proofs displayed in `arxiv.md`.

Each gist restates the theorem under discussion and re-proves it, importing
its dependencies from `AvgCaseMls`, so that the Lean next to each English
proof in the paper is genuinely checkable rather than illustrative.  Build
with `lake build Gists`, or run `scripts/check_gists.sh` to check each file
independently.
-/

-- The positive results.
import Gists.ResolutionLowerBound
import Gists.Example41
import Gists.Reductions

-- The three collapses.
import Gists.DegenerateLaws
import Gists.InNPTrivial
import Gists.CompletenessCharacterization
import Gists.Theorem44Vacuous
import Gists.DominationFree
import Gists.AvPVacuous

-- The repairs.
import Gists.Repair
