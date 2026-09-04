/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Distribution
import AvgCaseMls.Foundation.Codec

namespace AvgCaseMls.Foundation

def ComputesWithin (program : Program) (f : Bitstring → Bitstring)
    (T : Nat → Nat) : Prop :=
  ∀ x, ∃ r, program.eval (T (len x)) x = some r ∧ r.output = f x

def ComputesNatWithin (program : Program) (f : Bitstring → Nat)
    (T : Nat → Nat) : Prop :=
  ComputesWithin program (fun x => encodeNat (f x)) T

def PolynomialTimeComputable (f : Bitstring → Bitstring) : Prop :=
  ∃ program T, IsPolynomial T ∧ Monotone T ∧ ComputesWithin program f T

def PolynomialTimeComputableNat (f : Bitstring → Nat) : Prop :=
  ∃ program T, IsPolynomial T ∧ Monotone T ∧
    ComputesNatWithin program f T

/--
Algorithmic rankability: the exact rank function (not merely an upper bound) is
computed by the executable machine model in polynomially bounded fuel.
-/
def IsPolynomialTimeRankable (μ : Subprobability) : Prop :=
  PolynomialTimeComputableNat μ.rank

/-- A separate growth property, useful but intentionally weaker than rankability. -/
def HasPolynomialRankBound (μ : Subprobability) : Prop :=
  ∃ V, IsPolynomial V ∧ ∀ x, μ.rank x ≤ V (len x)

theorem IsPolynomialTimeRankable.has_computer {μ : Subprobability}
    (h : IsPolynomialTimeRankable μ) :
    ∃ program T, IsPolynomial T ∧ Monotone T ∧
      ComputesNatWithin program μ.rank T :=
  h

end AvgCaseMls.Foundation
