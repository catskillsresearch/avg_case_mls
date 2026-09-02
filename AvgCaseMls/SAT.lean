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
  1 + φ.length + (φ.map List.length).sum

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
