/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Distribution

namespace AvgCaseMls.Foundation

/-- Canonical unary output convention for natural-valued machine computations. -/
def encodeNat (n : Nat) : Bitstring := List.replicate n true

def ComputesWithin (M : Machine) (f : Bitstring → Bitstring) (T : Nat → Nat) : Prop :=
  ∀ x, ∃ r, eval M (T (len x)) x = some r ∧ r.output = f x

def ComputesNatWithin (M : Machine) (f : Bitstring → Nat) (T : Nat → Nat) : Prop :=
  ComputesWithin M (fun x => encodeNat (f x)) T

def PolynomialTimeComputable (f : Bitstring → Bitstring) : Prop :=
  ∃ M T, IsPolynomial T ∧ ComputesWithin M f T

def PolynomialTimeComputableNat (f : Bitstring → Nat) : Prop :=
  ∃ M T, IsPolynomial T ∧ ComputesNatWithin M f T

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
    ∃ M T, IsPolynomial T ∧ ComputesNatWithin M μ.rank T :=
  h

end AvgCaseMls.Foundation
