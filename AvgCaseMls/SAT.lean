/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.List.Defs

/-!
# CNF satisfiability

A small deep embedding of propositional literals and formulas in conjunctive
normal form. Empty clauses and the empty conjunction are included.
-/

namespace SAT

inductive Literal : Type
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving DecidableEq, Repr

abbrev Assignment := Nat → Prop
abbrev Clause := List Literal
abbrev CNF := List Clause

def evalLiteral (a : Assignment) : Literal → Prop
  | .pos i => a i
  | .neg i => ¬ a i

def evalClause (a : Assignment) (c : Clause) : Prop :=
  ∃ l ∈ c, evalLiteral a l

def evalCNF (a : Assignment) (φ : CNF) : Prop :=
  ∀ c ∈ φ, evalClause a c

def Satisfiable (φ : CNF) : Prop :=
  ∃ a, evalCNF a φ

/--
Structural size of a CNF: one node for the conjunction, one for each clause,
and one for each literal.
-/
def size (φ : CNF) : Nat :=
  1 + φ.length + (φ.map List.length).foldr (· + ·) 0

/--
`size` adds clause widths with `foldr` rather than `List.sum` so that
`Challenge` and `Solution` cannot elaborate the `Zero Nat` instance through
different parent structures; Palomar compares elaborated terms, and the two
import graphs reach `Zero Nat` by different routes.  This normalises the
`foldr` form back to the `List.sum` API the downstream proofs are written
against.
-/
@[simp] theorem foldr_add_eq_sum (l : List Nat) :
    l.foldr (· + ·) 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem evalClause_nil (a : Assignment) : ¬ evalClause a [] := by
  simp [evalClause]

@[simp] theorem evalClause_cons (a : Assignment) (l : Literal) (c : Clause) :
    evalClause a (l :: c) ↔ evalLiteral a l ∨ evalClause a c := by
  simp [evalClause]

@[simp] theorem evalCNF_nil (a : Assignment) : evalCNF a [] := by
  simp [evalCNF]

@[simp] theorem evalCNF_cons (a : Assignment) (c : Clause) (φ : CNF) :
    evalCNF a (c :: φ) ↔ evalClause a c ∧ evalCNF a φ := by
  simp [evalCNF]

@[simp] theorem size_nil : size [] = 1 := by
  simp [size]

@[simp] theorem size_cons (c : Clause) (φ : CNF) :
    size (c :: φ) = size φ + c.length + 1 := by
  simp [size]
  omega

end SAT
