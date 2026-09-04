import AvgCaseMls.Foundation.TapeMacros.Core
import AvgCaseMls.Foundation.TapeMacros.Assembler
import AvgCaseMls.Foundation.TapeMacros.Scan
import AvgCaseMls.Foundation.TapeMacros.Codec
import AvgCaseMls.Foundation.TapeMacros.Unary
import AvgCaseMls.Foundation.TapeMacros.Arithmetic
import AvgCaseMls.Foundation.TapeMacros.Blocks
import AvgCaseMls.Foundation.TapeMacros.Serialization
import AvgCaseMls.Foundation.TapeMacros.Dynamic
import AvgCaseMls.Foundation.TapeMacros.CanonicalParser
import AvgCaseMls.Foundation.TapeMacros.HeaderBoundary

/-!
# Verified two-stack tape-machine macros

This umbrella module exports the low-level machine correctness interfaces,
blank-delimiter scanner, sequential fuel closure theorems, and the binary,
unary-padding, and pairing codec specifications.
-/
