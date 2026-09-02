/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.SetTheory.ZFC.Basic

/-!
Deep embedding of Multilevel Syllogistic (MLS) syntax and set-theoretic semantics.

Extracted from [`arxiv.md`](../arxiv.md) §6.
-/

namespace MLS

/-! ### Syntactic terms -/

inductive Term : Type
  | var   : Nat → Term
  | empty : Term
  | union : Term → Term → Term
  | inter : Term → Term → Term
  | diff  : Term → Term → Term
  deriving DecidableEq, Repr

/-! ### Set-theoretic relations -/

inductive Relation : Type
  | mem     : Term → Term → Relation
  | not_mem : Term → Term → Relation
  | eq      : Term → Term → Relation
  | neq     : Term → Term → Relation
  deriving DecidableEq, Repr

/-! ### Propositional formulas -/

inductive Formula : Type
  | rel : Relation → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or  : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | iff : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-! ### ZFC semantics

MLS is interpreted in Mathlib's concrete `ZFSet` model.  Earlier versions of
this project declared the carrier, operations, foundation, and tags as project
axioms.  Using the library model makes those dependencies ordinary theorems.
-/

abbrev ZFSet := _root_.ZFSet.{0}

namespace ZFSet

def empty : ZFSet := ∅
def union (x y : ZFSet) : ZFSet := x ∪ y
def inter (x y : ZFSet) : ZFSet := x ∩ y
def diff (x y : ZFSet) : ZFSet := x \ y
def mem (x y : ZFSet) : Prop := x ∈ y

/-- Foundation in Mathlib's ZFC model. -/
theorem regularity (x : ZFSet) : ¬ mem x x :=
  _root_.ZFSet.mem_irrefl x

/-- Iterated-singleton towers used as pairwise distinct nonempty witnesses. -/
def tower : Nat → ZFSet
  | 0 => ∅
  | n + 1 => {tower n}

def tag (n : Nat) : ZFSet := tower (n + 1)

theorem tower_succ_ne_empty (n : Nat) : tower (n + 1) ≠ empty := by
  intro h
  have hmem : tower n ∈ tower (n + 1) := by simp [tower]
  rw [h] at hmem
  exact (_root_.ZFSet.notMem_empty (tower n)) hmem

theorem tag_ne_empty (n : Nat) : tag n ≠ empty :=
  tower_succ_ne_empty n

theorem tower_eq {m n : Nat} (h : tower m = tower n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          exact False.elim (tower_succ_ne_empty n h.symm)
  | succ m ih =>
      cases n with
      | zero =>
          exact False.elim (tower_succ_ne_empty m h)
      | succ n =>
          have hmn : tower m = tower n := by
            simpa [tower] using h
          exact congrArg Nat.succ (ih hmn)

theorem tower_injective : Function.Injective tower :=
  fun _ _ => tower_eq

theorem tag_injective : Function.Injective tag := by
  intro m n h
  have : m + 1 = n + 1 := tower_eq h
  omega

end ZFSet

def Env : Type 1 := Nat → ZFSet

noncomputable def evalTerm (env : Env) : Term → ZFSet
  | Term.var n       => env n
  | Term.empty       => ZFSet.empty
  | Term.union t1 t2 => ZFSet.union (evalTerm env t1) (evalTerm env t2)
  | Term.inter t1 t2 => ZFSet.inter (evalTerm env t1) (evalTerm env t2)
  | Term.diff t1 t2  => ZFSet.diff (evalTerm env t1) (evalTerm env t2)

noncomputable def evalFormula (env : Env) : Formula → Prop
  | Formula.rel (Relation.mem t1 t2)     => ZFSet.mem (evalTerm env t1) (evalTerm env t2)
  | Formula.rel (Relation.not_mem t1 t2) => ¬ ZFSet.mem (evalTerm env t1) (evalTerm env t2)
  | Formula.rel (Relation.eq t1 t2)      => evalTerm env t1 = evalTerm env t2
  | Formula.rel (Relation.neq t1 t2)     => evalTerm env t1 ≠ evalTerm env t2
  | Formula.not f                        => ¬ evalFormula env f
  | Formula.and f1 f2                    => evalFormula env f1 ∧ evalFormula env f2
  | Formula.or f1 f2                     => evalFormula env f1 ∨ evalFormula env f2
  | Formula.imp f1 f2                    => evalFormula env f1 → evalFormula env f2
  | Formula.iff f1 f2                    => evalFormula env f1 ↔ evalFormula env f2

end MLS
