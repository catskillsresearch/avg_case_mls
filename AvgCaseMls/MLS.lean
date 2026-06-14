/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

/-!
Deep embedding of Multilevel Syllogistic (MLS) syntax and set-theoretic semantics.

Extracted from [`arxiv.md`](../arxiv.md) §2.
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

/-! ### Axiomatic semantics -/

axiom ZFSet : Type

axiom ZFSet.empty : ZFSet
axiom ZFSet.union : ZFSet → ZFSet → ZFSet
axiom ZFSet.inter : ZFSet → ZFSet → ZFSet
axiom ZFSet.diff  : ZFSet → ZFSet → ZFSet
axiom ZFSet.mem   : ZFSet → ZFSet → Prop

def Env : Type := Nat → ZFSet

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
