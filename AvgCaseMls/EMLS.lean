/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS

/-!
**Phase 2B complete:** `Literal`, `literalToFormula`, `conjunctToFormula`, `Literal.holds`, translation lemmas; `relationToLiteral?` for §7 normalization.

Literals follow Ferro–Omodeo–Schwartz [FOS80] §3 (`3-540-10009-1_8.pdf` in this repo):
conjunctions of (* ) $x = y \diamond z$, ($\in$) $x \in y$, ($\notin$) $x \notin y$, ($\neq$) $x \neq y$,
with $\diamond \in \{\cup,\cap,\setminus\}$ and $x,y,z$ set variables.
-/

namespace MLS.EMLS

/-! ### Elementary literals (FOS80 §3) -/

inductive BinOp
  | union
  | inter
  | diff
  deriving DecidableEq, Repr

inductive Literal
  | eqOp    : Nat → Nat → Nat → BinOp → Literal  -- (* )  x = y ◇ z
  | eqEmpty : Nat → Literal                      --       x = ∅
  | mem     : Nat → Nat → Literal                -- (∈)   x ∈ y
  | notMem  : Nat → Nat → Literal                -- (∉)   x ∉ y
  | neq     : Nat → Nat → Literal                -- (≠)   x ≠ y
  deriving DecidableEq, Repr

abbrev Conjunct := List Literal

def binOpToTerm (op : BinOp) (y z : Nat) : Term :=
  match op with
  | .union => Term.union (Term.var y) (Term.var z)
  | .inter => Term.inter (Term.var y) (Term.var z)
  | .diff  => Term.diff (Term.var y) (Term.var z)

def literalToFormula : Literal → Formula
  | .eqOp x y z op => Formula.rel (Relation.eq (Term.var x) (binOpToTerm op y z))
  | .eqEmpty x     => Formula.rel (Relation.eq (Term.var x) Term.empty)
  | .mem x y       => Formula.rel (Relation.mem (Term.var x) (Term.var y))
  | .notMem x y    => Formula.rel (Relation.not_mem (Term.var x) (Term.var y))
  | .neq x y       => Formula.rel (Relation.neq (Term.var x) (Term.var y))

def conjunctToFormula : Conjunct → Option Formula
  | [] => none
  | [l] => some (literalToFormula l)
  | l :: ls@(_ :: _) =>
      match conjunctToFormula ls with
      | none => none
      | some f => some (Formula.and (literalToFormula l) f)

/-! ### Semantics and translation lemmas (Phase 2B) -/

/-- Semantic satisfaction of an elementary literal under `env`. -/
noncomputable def Literal.holds (env : Env) : Literal → Prop
  | .eqOp x y z op =>
      evalTerm env (Term.var x) = evalTerm env (binOpToTerm op y z)
  | .eqEmpty x =>
      evalTerm env (Term.var x) = evalTerm env Term.empty
  | .mem x y =>
      ZFSet.mem (evalTerm env (Term.var x)) (evalTerm env (Term.var y))
  | .notMem x y =>
      ¬ ZFSet.mem (evalTerm env (Term.var x)) (evalTerm env (Term.var y))
  | .neq x y =>
      evalTerm env (Term.var x) ≠ evalTerm env (Term.var y)

/-! ### Step 4 semantic grounding (ZF regularity) -/

/--
A self-membership literal `x ∈ x` is unsatisfiable under the Axiom of Foundation.
Grounds syntactic Step 4 cycle detection for single-node loops.
-/
theorem step4_self_loop_unsat (env : Env) (x : Nat) :
    ¬ Literal.holds env (Literal.mem x x) := by
  intro hmem
  simp only [Literal.holds, evalTerm] at hmem
  exact ZFSet.regularity (env x) hmem

theorem literalToFormula_eval (env : Env) (lit : Literal) :
    evalFormula env (literalToFormula lit) ↔ Literal.holds env lit := by
  cases lit <;> simp [Literal.holds, literalToFormula, evalFormula, evalTerm, binOpToTerm]

private theorem conjunctToFormula_some_of_ne_nil {c : Conjunct} (h : c ≠ []) :
    ∃ f, conjunctToFormula c = some f := by
  cases c with
  | nil => contradiction
  | cons l ls =>
    cases ls with
    | nil => exact ⟨literalToFormula l, by simp [conjunctToFormula]⟩
    | cons l' ls' =>
      obtain ⟨f, hf⟩ := @conjunctToFormula_some_of_ne_nil (l' :: ls') (List.cons_ne_nil l' ls')
      exact ⟨Formula.and (literalToFormula l) f, by simp [conjunctToFormula, hf]⟩

theorem conjunctToFormula_none_iff (c : Conjunct) :
    conjunctToFormula c = none ↔ c = [] := by
  constructor
  · intro h
    cases c with
    | nil => rfl
    | cons l ls =>
      obtain ⟨f, hf⟩ := @conjunctToFormula_some_of_ne_nil (l :: ls) (List.cons_ne_nil l ls)
      rw [hf] at h
      cases h
  · intro h; subst h; simp [conjunctToFormula]

theorem conjunctToFormula_singleton (lit : Literal) :
    conjunctToFormula [lit] = some (literalToFormula lit) := by
  simp [conjunctToFormula]

theorem conjunctToFormula_eval (env : Env) (c : Conjunct) (f : Formula)
    (h : conjunctToFormula c = some f) :
    evalFormula env f ↔ ∀ lit ∈ c, Literal.holds env lit := by
  induction c generalizing f with
  | nil => simp [conjunctToFormula] at h
  | cons l ls ih =>
      cases ls with
      | nil =>
          simp [conjunctToFormula] at h
          subst h
          simp [literalToFormula_eval]
      | cons l' ls' =>
          simp [conjunctToFormula] at h
          cases h' : conjunctToFormula (l' :: ls') with
          | none =>
            exfalso
            have := @conjunctToFormula_some_of_ne_nil (l' :: ls') (List.cons_ne_nil l' ls')
            simp [h'] at this
          | some f' =>
            rw [h'] at h
            injection h with hf_eq
            subst hf_eq
            have ih' := ih f' h'
            simp only [literalToFormula_eval, List.mem_cons, evalFormula, ih']
            constructor
            · intro ⟨h0, h1⟩ lit hl
              cases hl with
              | inl hl => subst hl; exact h0
              | inr hl => exact h1 lit hl
            · intro hall
              exact ⟨hall l (by simp), fun lit hl => hall lit (Or.inr hl)⟩

/-! ### MLS relation ↔ literal (FOS80 §3 patterns) -/

def varTerm? : Term → Option Nat
  | Term.var n => some n
  | _ => none

theorem varTerm?_eq (t : Term) (n : Nat) (h : varTerm? t = some n) : t = Term.var n := by
  cases t <;> simp [varTerm?] at h <;> cases h <;> rfl

def binaryOpTerm? : Term → Option (Nat × Nat × BinOp)
  | Term.union (Term.var y) (Term.var z) => some (y, z, .union)
  | Term.inter (Term.var y) (Term.var z) => some (y, z, .inter)
  | Term.diff (Term.var y) (Term.var z) => some (y, z, .diff)
  | _ => none

def relationToLiteral? : Relation → Option Literal
  | Relation.mem t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .mem x y
  | Relation.not_mem t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .notMem x y
  | Relation.eq t1 Term.empty => do
      let x ← varTerm? t1
      return .eqEmpty x
  | Relation.eq (Term.var x) t2 => do
      let (y, z, op) ← binaryOpTerm? t2
      return .eqOp x y z op
  | Relation.neq t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .neq x y
  | _ => none

theorem relationToLiteral?_eval (env : Env) (r : Relation) (lit : Literal)
    (h : relationToLiteral? r = some lit) :
    evalFormula env (Formula.rel r) ↔ Literal.holds env lit := by
  revert lit
  cases r with
  | mem t1 t2 =>
    intro lit h
    cases ht1 : varTerm? t1 with
    | none => simp [relationToLiteral?, ht1] at h
    | some x =>
      cases ht2 : varTerm? t2 with
      | none => simp [relationToLiteral?, ht2] at h
      | some y =>
        simp [relationToLiteral?, ht1, ht2, Literal.holds, evalFormula, evalTerm] at h ⊢
        cases h
        rw [varTerm?_eq t1 x ht1, varTerm?_eq t2 y ht2]
        simp [evalTerm, Literal.holds]
  | not_mem t1 t2 =>
    intro lit h
    cases ht1 : varTerm? t1 with
    | none => simp [relationToLiteral?, ht1] at h
    | some x =>
      cases ht2 : varTerm? t2 with
      | none => simp [relationToLiteral?, ht2] at h
      | some y =>
        simp [relationToLiteral?, ht1, ht2, Literal.holds, evalFormula, evalTerm] at h ⊢
        cases h
        rw [varTerm?_eq t1 x ht1, varTerm?_eq t2 y ht2]
        simp [evalTerm, Literal.holds]
  | eq t1 t2 =>
    intro lit h
    by_cases ht2 : t2 = Term.empty
    · subst ht2
      cases ht1 : varTerm? t1 with
      | none => simp [relationToLiteral?, ht1] at h
      | some x =>
        simp [relationToLiteral?, ht1, Literal.holds, evalFormula, evalTerm] at h ⊢
        cases h
        rw [varTerm?_eq t1 x ht1]
        simp [evalTerm, Literal.holds]
    · by_cases hunion : ∃ x y z, t1 = Term.var x ∧ t2 = Term.union (Term.var y) (Term.var z)
      · obtain ⟨x, y, z, ht1, ht2⟩ := hunion
        subst ht1 ht2
        simp [relationToLiteral?, Literal.holds, evalFormula, evalTerm, binOpToTerm] at h ⊢
        cases h; simp [evalTerm, Literal.holds]
      · by_cases hinter : ∃ x y z, t1 = Term.var x ∧ t2 = Term.inter (Term.var y) (Term.var z)
        · obtain ⟨x, y, z, ht1, ht2⟩ := hinter
          subst ht1 ht2
          simp [relationToLiteral?, Literal.holds, evalFormula, evalTerm, binOpToTerm] at h ⊢
          cases h; simp [evalTerm, Literal.holds]
        · by_cases hdiff : ∃ x y z, t1 = Term.var x ∧ t2 = Term.diff (Term.var y) (Term.var z)
          · obtain ⟨x, y, z, ht1, ht2⟩ := hdiff
            subst ht1 ht2
            simp [relationToLiteral?, Literal.holds, evalFormula, evalTerm, binOpToTerm] at h ⊢
            cases h; simp [evalTerm, Literal.holds]
          · exfalso
            have hnone :
                relationToLiteral? (Relation.eq t1 t2) = none := by
              cases t1 with
              | empty =>
                cases t2 <;> simp [relationToLiteral?, varTerm?, binaryOpTerm?]
              | union u v =>
                cases t2 <;> simp [relationToLiteral?, varTerm?, binaryOpTerm?]
              | inter u v =>
                cases t2 <;> simp [relationToLiteral?, varTerm?, binaryOpTerm?]
              | diff u v =>
                cases t2 <;> simp [relationToLiteral?, varTerm?, binaryOpTerm?]
              | var x =>
                cases t2 with
                | empty => exact absurd rfl ht2
                | var n => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                | union u v =>
                  cases u with
                  | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | var y =>
                    cases v with
                    | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | var z =>
                      exfalso
                      apply hunion
                      exact ⟨x, y, z, rfl, rfl⟩
                | inter u v =>
                  cases u with
                  | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | var y =>
                    cases v with
                    | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | var z =>
                      exfalso
                      apply hinter
                      exact ⟨x, y, z, rfl, rfl⟩
                | diff u v =>
                  cases u with
                  | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                  | var y =>
                    cases v with
                    | empty => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | union _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | inter _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | diff _ _ => simp [relationToLiteral?, varTerm?, binaryOpTerm?]
                    | var z =>
                      exfalso
                      apply hdiff
                      exact ⟨x, y, z, rfl, rfl⟩
            rw [hnone] at h
            cases h
  | neq t1 t2 =>
    intro lit h
    cases ht1 : varTerm? t1 with
    | none => simp [relationToLiteral?, ht1] at h
    | some x =>
      cases ht2 : varTerm? t2 with
      | none => simp [relationToLiteral?, ht2] at h
      | some y =>
        simp [relationToLiteral?, ht1, ht2, Literal.holds, evalFormula, evalTerm] at h ⊢
        cases h
        rw [varTerm?_eq t1 x ht1, varTerm?_eq t2 y ht2]
        simp [evalTerm, Literal.holds]

def memLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .mem x y => some (x, y)
    | _ => none

def notMemLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .notMem x y => some (x, y)
    | _ => none

def neqLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .neq x y => some (x, y)
    | _ => none

def hasEqEmpty (c : Conjunct) (x : Nat) : Bool :=
  c.any fun | .eqEmpty y => decide (y = x) | _ => false

def hasEqOpLiteral (c : Conjunct) : Bool :=
  c.any fun | .eqOp _ _ _ _ => true | _ => false

end MLS.EMLS
