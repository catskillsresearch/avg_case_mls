/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Machine
import AvgCaseMls.AvCom
import Mathlib.Tactic

namespace AvgCaseMls.Foundation

def len (x : Bitstring) : Nat := x.length

inductive IsPolynomial : (Nat → Nat) → Prop where
  | bounded {T : Nat → Nat} (c k : Nat)
      (bound : ∀ n, T n ≤ c * n ^ k + c) : IsPolynomial T
  | add {f g : Nat → Nat} :
      IsPolynomial f → IsPolynomial g → IsPolynomial (fun n => f n + g n)
  | mul {f g : Nat → Nat} :
      IsPolynomial f → IsPolynomial g → IsPolynomial (fun n => f n * g n)
  | comp {f g : Nat → Nat} :
      IsPolynomial f → IsPolynomial g → IsPolynomial (fun n => f (g n))

/--
Single-exponential time: `T(n) ≤ c * 2^(p(n)) + c` for a polynomial exponent.
This is the usual `2^poly(n)` scale used for EXP and NEXP.
-/
def IsExponential (T : Nat → Nat) : Prop :=
  ∃ p : Nat → Nat, ∃ c : Nat,
    IsPolynomial p ∧ 0 < c ∧ ∀ n, T n ≤ c * 2 ^ p n + c

def HaltsWith (program : Program) (x : Bitstring) (r : Result) : Prop :=
  ∃ fuel, program.eval fuel x = some r

/-- Total correctness for a Boolean language, against the executable evaluator. -/
def Decides (program : Program) (L : Set Bitstring) : Prop :=
  ∀ x, ∃ r, HaltsWith program x r ∧ (r.accept = true ↔ x ∈ L)

/-- Uniform fuel bound, including correctness of the observed result. -/
def DecidesWithin (program : Program) (L : Set Bitstring) (T : Nat → Nat) : Prop :=
  ∀ x, ∃ r, program.eval (T (len x)) x = some r ∧ (r.accept = true ↔ x ∈ L)

def InP (L : Set Bitstring) : Prop :=
  ∃ program T, IsPolynomial T ∧ DecidesWithin program L T

def InEXP (L : Set Bitstring) : Prop :=
  ∃ program T, IsExponential T ∧ DecidesWithin program L T

theorem DecidesWithin.decides {program : Program} {L : Set Bitstring} {T : Nat → Nat}
    (h : DecidesWithin program L T) : Decides program L := by
  intro x
  obtain ⟨r, hr, hcorrect⟩ := h x
  exact ⟨r, ⟨T (len x), hr⟩, hcorrect⟩

namespace IsPolynomial

theorem id : IsPolynomial id := .bounded 1 1 (fun n => by simp)

theorem const (d : Nat) : IsPolynomial (fun _ => d) :=
  .bounded d 0 (fun n => by simp)

end IsPolynomial

namespace IsExponential

theorem const (d : Nat) : IsExponential (fun _ => d) := by
  refine ⟨fun _ => 0, max 1 d, IsPolynomial.const 0, by omega, fun n => ?_⟩
  simp
  omega

end IsExponential

@[simp] theorem len_legacy (x : Bitstring) : len x = AvCom.len x := rfl

end AvgCaseMls.Foundation
