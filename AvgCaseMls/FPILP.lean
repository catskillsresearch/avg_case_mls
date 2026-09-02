/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.SAT
import Mathlib

/-!
# The SAT to 0/1 integer-linear feasibility reduction

This file formalizes the construction used in Cox--Ericson--Mishra (1995),
Theorem 5.3.  The project-wide `SAT` syntax uses unbounded `Nat` variable names
and assignments `Nat → Prop`.  The reduction below deliberately retains a
local, `Fin n`-indexed specialization: replacing it directly by `SAT.CNF`
would discard the type-level guarantee that every literal has one of the
`n` variables constrained by the generated 0/1 bounds.  Recovering that
guarantee over `SAT.CNF` would require a separate well-formedness hypothesis,
and the central equivalence would no longer be unconditional.

An `FPILP n` instance is a conjunction of inequalities between integer linear
expressions in exactly those `n` variables.  The reduction emits the bounds
`0 ≤ xᵢ` and `xᵢ ≤ 1`, followed by one inequality

`∑ positive xᵢ + ∑ negative (1 - xᵢ) ≥ 1`

for each clause.
-/

namespace TR1995.FPILPSource

/-! ## Fin-indexed specialization of propositional CNF

Unlike `SAT.Literal`, this literal type makes the variable bound intrinsic.
This is the invariant used by `bounds_force_zero_one` in the reverse direction.
-/

inductive Literal (n : Nat) where
  | pos : Fin n → Literal n
  | neg : Fin n → Literal n
  deriving DecidableEq, Repr

abbrev Clause (n : Nat) := List (Literal n)
abbrev CNF (n : Nat) := List (Clause n)
abbrev Assignment (n : Nat) := Fin n → Bool

def Literal.eval {n : Nat} (a : Assignment n) : Literal n → Bool
  | .pos i => a i
  | .neg i => !(a i)

def Clause.Satisfied {n : Nat} (a : Assignment n) (c : Clause n) : Prop :=
  ∃ l ∈ c, l.eval a = true

def CNF.Satisfied {n : Nat} (a : Assignment n) (φ : CNF n) : Prop :=
  ∀ c ∈ φ, c.Satisfied a

def CNF.Satisfiable {n : Nat} (φ : CNF n) : Prop :=
  ∃ a, φ.Satisfied a

/-! ## The 0/1 integer-linear feasibility fragment -/

/-- The two affine terms needed by the reduction: `xᵢ` and `1 - xᵢ`. -/
inductive Term (n : Nat) where
  | var : Fin n → Term n
  | oneMinus : Fin n → Term n
  deriving DecidableEq, Repr

def Term.eval {n : Nat} (x : Fin n → Int) : Term n → Int
  | .var i => x i
  | .oneMinus i => 1 - x i

/-- An inequality `rhs ≤ ∑ lhs`. -/
structure Inequality (n : Nat) where
  lhs : List (Term n)
  rhs : Int
  deriving DecidableEq, Repr

def Inequality.Holds {n : Nat} (x : Fin n → Int) (q : Inequality n) : Prop :=
  q.rhs ≤ (q.lhs.map (Term.eval x)).sum

/-- A finite conjunction of integer-linear inequalities in `n` variables. -/
structure FPILP (n : Nat) where
  constraints : List (Inequality n)
  deriving DecidableEq, Repr

def FPILP.Feasible {n : Nat} (p : FPILP n) : Prop :=
  ∃ x : Fin n → Int, ∀ q ∈ p.constraints, q.Holds x

def lowerBound {n : Nat} (i : Fin n) : Inequality n :=
  ⟨[.var i], 0⟩

def upperBound {n : Nat} (i : Fin n) : Inequality n :=
  ⟨[.oneMinus i], 0⟩

def bounds (n : Nat) : List (Inequality n) :=
  (List.finRange n).flatMap fun i => [lowerBound i, upperBound i]

def Literal.toTerm {n : Nat} : Literal n → Term n
  | .pos i => .var i
  | .neg i => .oneMinus i

def clauseInequality {n : Nat} (c : Clause n) : Inequality n :=
  ⟨c.map Literal.toTerm, 1⟩

/-- The exact clause-by-clause construction in Theorem 5.3. -/
def satToFPILP {n : Nat} (φ : CNF n) : FPILP n :=
  ⟨bounds n ++ φ.map clauseInequality⟩

/-! ## Semantic correctness -/

private theorem boolValue_eq_zero_or_one (b : Bool) :
    (if b then (1 : Int) else 0) = 0 ∨ (if b then (1 : Int) else 0) = 1 := by
  cases b <;> simp

private theorem encodedTerm_eval {n : Nat} (a : Assignment n) (l : Literal n) :
    (l.toTerm.eval fun i => if a i then 1 else 0) =
      if l.eval a then 1 else 0 := by
  cases l with
  | pos i => rfl
  | neg i =>
      cases h : a i <;> simp [Literal.eval, Literal.toTerm, Term.eval, h]

private theorem encodedTerm_nonneg {n : Nat} (a : Assignment n) (l : Literal n) :
    0 ≤ l.toTerm.eval (fun i => if a i then 1 else 0) := by
  rw [encodedTerm_eval]
  split <;> simp

private theorem clause_forward {n : Nat} (a : Assignment n) (c : Clause n)
    (h : c.Satisfied a) :
    (clauseInequality c).Holds (fun i => if a i then 1 else 0) := by
  rcases h with ⟨l, hl, heval⟩
  unfold Inequality.Holds clauseInequality
  simp only [List.map_map]
  have hone : l.toTerm.eval (fun i => if a i then 1 else 0) = 1 := by
    rw [encodedTerm_eval, heval]
    rfl
  have hmem : l.toTerm.eval (fun i => if a i then 1 else 0) ∈
      (c.map fun l => l.toTerm.eval (fun i => if a i then 1 else 0)) := by
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hnonneg : ∀ z ∈
      (c.map fun l => l.toTerm.eval (fun i => if a i then 1 else 0)), 0 ≤ z := by
    intro z hz
    obtain ⟨l', -, rfl⟩ := List.mem_map.mp hz
    exact encodedTerm_nonneg a l'
  have hsum : l.toTerm.eval (fun i => if a i then 1 else 0) ≤
      (c.map fun l => l.toTerm.eval (fun i => if a i then 1 else 0)).sum :=
    List.single_le_sum hnonneg _ hmem
  change (1 : Int) ≤
    (c.map fun l => l.toTerm.eval (fun i => if a i then 1 else 0)).sum
  simpa [hone] using hsum

private theorem bounds_forward {n : Nat} (a : Assignment n) :
    ∀ q ∈ bounds n, q.Holds (fun i => if a i then 1 else 0) := by
  intro q hq
  simp only [bounds, List.mem_flatMap] at hq
  rcases hq with ⟨i, -, hi⟩
  have hsplit : q = lowerBound i ∨ q ∈ [upperBound i] := by
    simpa only [List.mem_cons] using hi
  rcases hsplit with (rfl | hi)
  · cases hai : a i <;> simp [Inequality.Holds, lowerBound, Term.eval, hai]
  · have hsplit' : q = upperBound i ∨ q ∈ [] := by
      simpa only [List.mem_cons] using hi
    rcases hsplit' with (rfl | hi)
    · cases hai : a i <;> simp [Inequality.Holds, upperBound, Term.eval, hai]
    · exact False.elim (List.not_mem_nil hi)

private theorem bounds_force_zero_one {n : Nat} {x : Fin n → Int}
    (h : ∀ q ∈ bounds n, q.Holds x) (i : Fin n) :
    x i = 0 ∨ x i = 1 := by
  have hlo : (lowerBound i).Holds x := h _ (by
    simp only [bounds, List.mem_flatMap]
    exact ⟨i, by simp, by simp⟩)
  have hhi : (upperBound i).Holds x := h _ (by
    simp only [bounds, List.mem_flatMap]
    exact ⟨i, by simp, by simp⟩)
  simp [Inequality.Holds, lowerBound, upperBound, Term.eval] at hlo hhi
  omega

private theorem decodedTerm_eval {n : Nat} {x : Fin n → Int}
    (hb : ∀ q ∈ bounds n, q.Holds x) (l : Literal n) :
    l.toTerm.eval x = if l.eval (fun i => x i = 1) then 1 else 0 := by
  have hi := bounds_force_zero_one hb (match l with | .pos i => i | .neg i => i)
  cases l with
  | pos i =>
      simp only [Literal.toTerm, Term.eval, Literal.eval]
      rcases hi with h | h <;> simp [h]
  | neg i =>
      simp only [Literal.toTerm, Term.eval, Literal.eval]
      rcases hi with h | h <;> simp [h]

private theorem exists_one_of_sum_ge_one {xs : List Int}
    (hz : ∀ z ∈ xs, z = 0 ∨ z = 1) (h : 1 ≤ xs.sum) :
    ∃ z ∈ xs, z = 1 := by
  induction xs with
  | nil => simp at h
  | cons z zs ih =>
      rcases hz z (by simp) with hzero | hone
      · have htail : ∀ y ∈ zs, y = 0 ∨ y = 1 := by
          intro y hy
          exact hz y (by simp [hy])
        have hsum : 1 ≤ zs.sum := by simpa [hzero] using h
        obtain ⟨y, hy, hyone⟩ := ih htail hsum
        exact ⟨y, by simp [hy], hyone⟩
      · exact ⟨z, by simp, hone⟩

private theorem clause_reverse {n : Nat} {x : Fin n → Int}
    (hb : ∀ q ∈ bounds n, q.Holds x) (c : Clause n)
    (hc : (clauseInequality c).Holds x) :
    c.Satisfied (fun i => x i = 1) := by
  unfold Inequality.Holds clauseInequality at hc
  simp only [List.map_map] at hc
  let values := c.map fun l => l.toTerm.eval x
  have hz : ∀ z ∈ values, z = 0 ∨ z = 1 := by
    intro z hzmem
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hzmem
    rw [decodedTerm_eval hb l]
    exact boolValue_eq_zero_or_one _
  obtain ⟨z, hzmem, hone⟩ := exists_one_of_sum_ge_one hz hc
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp hzmem
  refine ⟨l, hl, ?_⟩
  have ht : l.toTerm.eval x = 1 := heq.trans hone
  rw [decodedTerm_eval hb l] at ht
  by_contra hf
  have hevalFalse : l.eval (fun i => x i = 1) = false :=
    Bool.eq_false_of_not_eq_true hf
  simp [hevalFalse] at ht

/-- The reduction preserves and reflects satisfiability. -/
theorem satToFPILP_feasible_iff {n : Nat} (φ : CNF n) :
    (satToFPILP φ).Feasible ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨x, hx⟩
    have hb : ∀ q ∈ bounds n, q.Holds x := by
      intro q hq
      exact hx q (by simp [satToFPILP, hq])
    refine ⟨fun i => x i = 1, ?_⟩
    intro c hc
    apply clause_reverse hb c
    apply hx
    simp only [satToFPILP, List.mem_append, List.mem_map]
    exact Or.inr ⟨c, hc, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => if a i then 1 else 0, ?_⟩
    intro q hq
    simp only [satToFPILP, List.mem_append, List.mem_map] at hq
    rcases hq with hbound | ⟨c, hc, rfl⟩
    · exact bounds_forward a q hbound
    · exact clause_forward a c (ha c hc)

/-! ## Structural facts -/

theorem Literal.toTerm_injective {n : Nat} :
    Function.Injective (@Literal.toTerm n) := by
  intro l₁ l₂ h
  cases l₁ <;> cases l₂ <;> simp_all [Literal.toTerm]

private theorem list_map_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (List.map f) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact congrArg₂ List.cons (hf h.1) (ih h.2)

theorem clauseInequality_injective {n : Nat} :
    Function.Injective (@clauseInequality n) := by
  intro c d h
  have hm : c.map Literal.toTerm = d.map Literal.toTerm :=
    congrArg Inequality.lhs h
  exact list_map_injective Literal.toTerm_injective hm

/-- The construction retains the original clause list verbatim (under `toTerm`). -/
theorem satToFPILP_injective {n : Nat} :
    Function.Injective (@satToFPILP n) := by
  intro φ ψ h
  have hc : bounds n ++ φ.map clauseInequality =
      bounds n ++ ψ.map clauseInequality :=
    congrArg FPILP.constraints h
  have hm := List.append_cancel_left hc
  exact list_map_injective clauseInequality_injective hm

theorem bounds_length (n : Nat) : (bounds n).length = 2 * n := by
  simp [bounds, Nat.mul_comm]

/-- There are two bound inequalities per variable and one per clause. -/
theorem satToFPILP_constraint_count {n : Nat} (φ : CNF n) :
    (satToFPILP φ).constraints.length = 2 * n + φ.length := by
  simp [satToFPILP, bounds_length]

def literalCount {n : Nat} (φ : CNF n) : Nat :=
  (φ.map List.length).sum

def termCount {n : Nat} (p : FPILP n) : Nat :=
  (p.constraints.map fun q => q.lhs.length).sum

private theorem bounds_term_count (n : Nat) :
    ((bounds n).map fun q => q.lhs.length).sum = 2 * n := by
  have hall : ∀ q ∈ bounds n, q.lhs.length = 1 := by
    intro q hq
    simp only [bounds, List.mem_flatMap] at hq
    obtain ⟨i, -, hi⟩ := hq
    have hsplit : q = lowerBound i ∨ q ∈ [upperBound i] := by
      simpa only [List.mem_cons] using hi
    rcases hsplit with (rfl | hi)
    · rfl
    · have hsplit' : q = upperBound i ∨ q ∈ [] := by
        simpa only [List.mem_cons] using hi
      rcases hsplit' with (rfl | hi)
      · rfl
      · exact False.elim (List.not_mem_nil hi)
  have aux : ∀ (qs : List (Inequality n)),
      (∀ q ∈ qs, q.lhs.length = 1) →
      (qs.map fun q => q.lhs.length).sum = qs.length := by
    intro qs h
    induction qs with
    | nil => simp
    | cons q qs ih =>
        have hq := h q (by simp)
        have htail : ∀ r ∈ qs, r.lhs.length = 1 := by
          intro r hr
          exact h r (by simp [hr])
        simp [hq, ih htail, Nat.add_comm]
  rw [aux (bounds n) hall, bounds_length]

/-- The output has two bound terms per variable and one term per input literal. -/
theorem satToFPILP_term_count {n : Nat} (φ : CNF n) :
    termCount (satToFPILP φ) = 2 * n + literalCount φ := by
  have hclauses :
      (φ.map ((fun q => q.lhs.length) ∘ clauseInequality)).sum =
        (φ.map List.length).sum := by
    induction φ with
    | nil => simp
    | cons c φ ih =>
        simpa [clauseInequality] using congrArg (fun k => c.length + k) ih
  simp [termCount, satToFPILP, literalCount, bounds_term_count,
    List.sum_append, hclauses]

end TR1995.FPILPSource
