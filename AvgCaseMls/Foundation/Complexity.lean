/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Machine
import AvgCaseMls.AvCom

namespace AvgCaseMls.Foundation

def len (x : Bitstring) : Nat := x.length

def IsPolynomial (T : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n, T n ≤ c * n ^ k + c

/--
Single-exponential time: `T(n) ≤ c * 2^(p(n)) + c` for a polynomial exponent.
This is the usual `2^poly(n)` scale used for EXP and NEXP.
-/
def IsExponential (T : Nat → Nat) : Prop :=
  ∃ p : Nat → Nat, ∃ c : Nat,
    IsPolynomial p ∧ 0 < c ∧ ∀ n, T n ≤ c * 2 ^ p n + c

def HaltsWith (M : Machine) (x : Bitstring) (r : Result) : Prop :=
  ∃ fuel, eval M fuel x = some r

/-- Total correctness for a Boolean language, against the executable evaluator. -/
def Decides (M : Machine) (L : Set Bitstring) : Prop :=
  ∀ x, ∃ r, HaltsWith M x r ∧ (r.accept = true ↔ x ∈ L)

/-- Uniform fuel bound, including correctness of the observed result. -/
def DecidesWithin (M : Machine) (L : Set Bitstring) (T : Nat → Nat) : Prop :=
  ∀ x, ∃ r, eval M (T (len x)) x = some r ∧ (r.accept = true ↔ x ∈ L)

def InP (L : Set Bitstring) : Prop :=
  ∃ M T, IsPolynomial T ∧ DecidesWithin M L T

def InEXP (L : Set Bitstring) : Prop :=
  ∃ M T, IsExponential T ∧ DecidesWithin M L T

theorem DecidesWithin.decides {M : Machine} {L : Set Bitstring} {T : Nat → Nat}
    (h : DecidesWithin M L T) : Decides M L := by
  intro x
  obtain ⟨r, hr, hcorrect⟩ := h x
  exact ⟨r, ⟨T (len x), hr⟩, hcorrect⟩

namespace IsPolynomial

theorem id : IsPolynomial id := ⟨1, 1, fun n => by simp⟩

theorem const (d : Nat) : IsPolynomial (fun _ => d) :=
  ⟨d, 0, fun n => by simp⟩

end IsPolynomial

namespace IsExponential

theorem const (d : Nat) : IsExponential (fun _ => d) := by
  refine ⟨fun _ => 0, max 1 d, IsPolynomial.const 0, by omega, fun n => ?_⟩
  simp
  omega

end IsExponential

/-- The new and legacy polynomial predicates are definitionally identical. -/
theorem isPolynomial_legacy_iff (T : Nat → Nat) :
    IsPolynomial T ↔ AvCom.IsPolynomial T := Iff.rfl

@[simp] theorem len_legacy (x : Bitstring) : len x = AvCom.len x := rfl

end AvgCaseMls.Foundation
