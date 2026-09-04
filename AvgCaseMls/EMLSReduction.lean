/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.EMLS
import AvgCaseMls.EMLSCodec
import AvgCaseMls.SAT
import AvgCaseMls.Section4.CookLevin.SATCodec
import Mathlib

/-!
# The constructive SAT-to-EMLS reduction

This file formalizes the construction in the proof of Theorem 5.2 of
TR1995-711.  A propositional variable has two set variables, one for its
positive literal and one for its negative literal.  Their intersection is
forced to be empty.  A clause is represented by a chain of fresh variables
computing the union of its literal sets, followed by membership of a
distinguished element in the root of that chain.

The paper writes the last link as `Sₙ = vₙ`.  Equality of two variables is not
an elementary literal in the `MLS.EMLS` syntax used by this development.
We therefore use the exact elementary specialization
`Sₙ = vₙ ∪ e`, together with `e = ∅`.  This is semantically equivalent, and
also handles singleton clauses uniformly.  Empty clauses are represented by
the foundation-false literal `y ∈ y`.

Variable numbers are split into disjoint classes.  In particular every
set-operation result introduced for a clause is a positive multiple of four,
and is explicitly indexed by the clause number and suffix number using
`Nat.pair`.
-/

namespace EMLSReduction

open MLS
open MLS.EMLS

abbrev Satisfies (env : Env) (c : Conjunct) : Prop :=
  ∀ lit ∈ c, Literal.holds env lit

def EMLSSatisfiable (c : Conjunct) : Prop :=
  ∃ env, Satisfies env c

def distinguishedVar : Nat := 0
def emptyVar : Nat := 3
def positiveVar (i : Nat) : Nat := 4 * i + 1
def negativeVar (i : Nat) : Nat := 4 * i + 2
def intersectionVar (i : Nat) : Nat := 4 * i + 7

/-- A fresh result variable for step `j` of clause `k`. -/
def gadgetVar (k j : Nat) : Nat :=
  4 * (Nat.pair k j + 1)

theorem gadgetVar_eq_iff {k k' j j' : Nat} :
    gadgetVar k j = gadgetVar k' j' ↔ k = k' ∧ j = j' := by
  constructor
  · intro h
    have hp : Nat.pair k j = Nat.pair k' j' := by
      have hs : Nat.pair k j + 1 = Nat.pair k' j' + 1 := by
        apply Nat.mul_left_cancel (by decide : 0 < 4)
        exact h
      omega
    exact Nat.pair_eq_pair.mp hp
  · rintro ⟨rfl, rfl⟩
    rfl

theorem gadgetVar_ne_positive (k j i : Nat) :
    gadgetVar k j ≠ positiveVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, positiveVar] at this

theorem gadgetVar_ne_negative (k j i : Nat) :
    gadgetVar k j ≠ negativeVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, negativeVar] at this

theorem gadgetVar_ne_intersection (k j i : Nat) :
    gadgetVar k j ≠ intersectionVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, intersectionVar] at this

theorem gadgetVar_ne_distinguished (k j : Nat) :
    gadgetVar k j ≠ distinguishedVar := by
  simp [gadgetVar, distinguishedVar]

theorem gadgetVar_ne_empty (k j : Nat) :
    gadgetVar k j ≠ emptyVar := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, emptyVar] at this

/-- See `MLSInReduction.literalToMLS` for why this avoids pattern matching. -/
def literalVar (l : SAT.Literal) : Nat :=
  l.casesOn (motive := fun _ => Nat) positiveVar negativeVar

/-- The two elementary literals enforcing disjoint complementary truth sets. -/
def complementGadget (i : Nat) : Conjunct :=
  [ .eqOp (intersectionVar i) (positiveVar i) (negativeVar i) .inter
  , .eqEmpty (intersectionVar i)
  ]

/-- See `MLSInReduction.literalToMLS` for why this avoids pattern matching. -/
def literalComplementGadget (l : SAT.Literal) : Conjunct :=
  l.casesOn (motive := fun _ => Conjunct) complementGadget complementGadget

/--
Set-operation links computing the union of all literal variables in a
nonempty suffix.  The final link unions with the explicitly empty variable.
-/
def clauseGadgets (k j : Nat) : SAT.Clause → Conjunct
  | [] => []
  | l :: [] =>
      [.eqOp (gadgetVar k j) (literalVar l) emptyVar .union]
  | l :: rest@(_ :: _) =>
      .eqOp (gadgetVar k j) (literalVar l) (gadgetVar k (j + 1)) .union ::
        clauseGadgets k (j + 1) rest

def clauseCore (k : Nat) : SAT.Clause → Conjunct
  | [] => [.mem distinguishedVar distinguishedVar]
  | c@(_ :: _) => clauseGadgets k 0 c ++ [.mem distinguishedVar (gadgetVar k 0)]

def clausesCoreFrom : Nat → SAT.CNF → Conjunct
  | _, [] => []
  | k, c :: φ => clauseCore k c ++ clausesCoreFrom (k + 1) φ

def complementCore (φ : SAT.CNF) : Conjunct :=
  φ.flatMap fun c => c.flatMap literalComplementGadget

/-- The semantic core of the paper reduction. -/
def semanticCore (φ : SAT.CNF) : Conjunct :=
  .eqEmpty emptyVar :: (complementCore φ ++ clausesCoreFrom 0 φ)

private def boolSet (P : Prop) [Decidable P] : MLS.ZFSet :=
  if P then ({MLS.ZFSet.empty} : MLS.ZFSet) else MLS.ZFSet.empty

private theorem mem_boolSet (P : Prop) [Decidable P] :
    MLS.ZFSet.mem MLS.ZFSet.empty (boolSet P) ↔ P := by
  by_cases h : P <;> simp [boolSet, h, MLS.ZFSet.mem, MLS.ZFSet.empty]

private theorem boolSet_or (P Q : Prop) [Decidable P] [Decidable Q] [Decidable (P ∨ Q)] :
    boolSet (P ∨ Q) = MLS.ZFSet.union (boolSet P) (boolSet Q) := by
  ext x
  by_cases hp : P <;> by_cases hq : Q <;>
    simp [boolSet, hp, hq, MLS.ZFSet.union, MLS.ZFSet.empty]

private theorem boolSet_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    boolSet P = boolSet Q := by
  by_cases hp : P
  · simp [boolSet, hp, h.mp hp]
  · have hq : ¬Q := fun hQ => hp (h.mpr hQ)
    simp [boolSet, hp, hq]

private theorem boolSet_irrel (P : Prop) (d₁ d₂ : Decidable P) :
    @boolSet P d₁ = @boolSet P d₂ := by
  congr

def clauseSuffix (φ : SAT.CNF) (k j : Nat) : SAT.Clause :=
  ((φ[k]?).getD []).drop j

/-- Canonical set model associated with a formula and Boolean assignment. -/
noncomputable def model (φ : SAT.CNF) (a : SAT.Assignment) : Env := fun n =>
  if n = distinguishedVar then MLS.ZFSet.empty
  else
    match n % 4 with
    | 1 => @boolSet (a ((n - 1) / 4)) (Classical.propDecidable _)
    | 2 => @boolSet (¬a ((n - 2) / 4)) (Classical.propDecidable _)
    | 3 => MLS.ZFSet.empty
    | _ =>
        let kj := Nat.unpair (n / 4 - 1)
        @boolSet (SAT.evalClause a (clauseSuffix φ kj.1 kj.2))
          (Classical.propDecidable _)

@[simp] theorem model_distinguished (φ : SAT.CNF) (a : SAT.Assignment) :
    model φ a distinguishedVar = MLS.ZFSet.empty := by
  simp [model, distinguishedVar]

@[simp] theorem model_empty (φ : SAT.CNF) (a : SAT.Assignment) :
    model φ a emptyVar = MLS.ZFSet.empty := by
  simp [model, distinguishedVar, emptyVar]

@[simp] theorem model_positive (φ : SAT.CNF) (a : SAT.Assignment) (i : Nat) :
    model φ a (positiveVar i) =
      @boolSet (a i) (Classical.propDecidable _) := by
  classical
  have hdiv : 4 * i / 4 = i := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left i (n := 4) (by decide)
  simp [model, distinguishedVar, positiveVar, hdiv]

@[simp] theorem model_negative (φ : SAT.CNF) (a : SAT.Assignment) (i : Nat) :
    model φ a (negativeVar i) =
      @boolSet (¬a i) (Classical.propDecidable _) := by
  classical
  simp [model, distinguishedVar, negativeVar]
  apply boolSet_irrel

@[simp] theorem model_intersection (φ : SAT.CNF) (a : SAT.Assignment) (i : Nat) :
    model φ a (intersectionVar i) = MLS.ZFSet.empty := by
  simp [model, distinguishedVar, intersectionVar]

@[simp] theorem model_gadget (φ : SAT.CNF) (a : SAT.Assignment) (k j : Nat) :
    model φ a (gadgetVar k j) =
      @boolSet (SAT.evalClause a (clauseSuffix φ k j))
        (Classical.propDecidable _) := by
  classical
  have hdiv : 4 * (Nat.pair k j + 1) / 4 =
      Nat.pair k j + 1 :=
    by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left _ (n := 4) (by decide)
  simp [model, distinguishedVar, gadgetVar, hdiv, Nat.unpair_pair]

private theorem model_literalVar (φ : SAT.CNF) (a : SAT.Assignment) (l : SAT.Literal) :
    model φ a (literalVar l) =
      @boolSet (SAT.evalLiteral a l) (Classical.propDecidable _) := by
  classical
  cases l with
  | pos i =>
      simp only [literalVar, SAT.evalLiteral]
      exact model_positive φ a i
  | neg i =>
      simp only [literalVar, SAT.evalLiteral]
      calc
        model φ a (negativeVar i) =
            @boolSet (¬a i) (Classical.propDecidable _) := model_negative φ a i
        _ = @boolSet (¬a i) (Classical.propDecidable _) := rfl

private theorem clauseGadgets_model (φ : SAT.CNF) (a : SAT.Assignment)
    (k j : Nat) (c : SAT.Clause) (hsuffix : clauseSuffix φ k j = c) :
    Satisfies (model φ a) (clauseGadgets k j c) := by
  classical
  induction c generalizing j with
  | nil =>
      intro lit h
      simp [clauseGadgets] at h
  | cons l rest ih =>
      cases rest with
      | nil =>
          intro lit h
          simp only [clauseGadgets, List.mem_singleton] at h
          subst h
          simp only [Literal.holds, binOpToTerm, evalTerm, model_gadget,
            model_literalVar, model_empty]
          rw [hsuffix]
          rw [boolSet_congr (SAT.evalClause_cons a l [])]
          simp only [SAT.evalClause_nil, or_false]
          simpa [boolSet] using boolSet_or (SAT.evalLiteral a l) False
      | cons l' rest =>
          have hnext :
              clauseSuffix φ k (j + 1) = l' :: rest := by
            unfold clauseSuffix at hsuffix ⊢
            rw [← List.tail_drop, hsuffix]
            rfl
          intro lit h
          simp only [clauseGadgets, List.mem_cons] at h
          rcases h with rfl | h
          · simp only [Literal.holds, binOpToTerm, evalTerm, model_gadget,
              model_literalVar]
            rw [hsuffix, hnext]
            rw [boolSet_congr (SAT.evalClause_cons a l (l' :: rest))]
            exact boolSet_or (SAT.evalLiteral a l) (SAT.evalClause a (l' :: rest))
          · exact ih (j + 1) hnext lit h

private theorem complementGadget_model (φ : SAT.CNF) (a : SAT.Assignment) (i : Nat) :
    Satisfies (model φ a) (complementGadget i) := by
  by_cases h : a i <;>
    simp [complementGadget, Satisfies, Literal.holds, binOpToTerm, evalTerm,
      boolSet, h, MLS.ZFSet.inter, MLS.ZFSet.empty]

private theorem complementCore_model (φ : SAT.CNF) (a : SAT.Assignment) :
    Satisfies (model φ a) (complementCore φ) := by
  intro lit hlit
  change lit ∈ φ.flatMap (fun c => c.flatMap fun l =>
    literalComplementGadget l) at hlit
  obtain ⟨c, hc, hlit⟩ := List.mem_flatMap.mp hlit
  obtain ⟨l, hl, hlit⟩ := List.mem_flatMap.mp hlit
  cases l <;> exact complementGadget_model φ a _ lit hlit

private theorem clauseCore_model (φ : SAT.CNF) (a : SAT.Assignment)
    (k : Nat) (c : SAT.Clause)
    (hlookup : φ[k]? = some c)
    (hc : SAT.evalClause a c) :
    Satisfies (model φ a) (clauseCore k c) := by
  cases c with
  | nil => simp [SAT.evalClause] at hc
  | cons l rest =>
      intro lit hlit
      simp only [clauseCore, List.mem_append, List.mem_singleton] at hlit
      cases hlit with
      | inl h =>
          apply clauseGadgets_model φ a k 0 (l :: rest)
          · simp [clauseSuffix, hlookup]
          · exact h
      | inr h =>
          subst h
          simp [Literal.holds, evalTerm, model_gadget, clauseSuffix,
            hlookup, mem_boolSet, hc]

private theorem clausesCoreFrom_model (original φ : SAT.CNF)
    (a : SAT.Assignment) (k : Nat)
    (hdrop : original.drop k = φ) (ha : SAT.evalCNF a φ) :
    Satisfies (model original a) (clausesCoreFrom k φ) := by
  induction φ generalizing k with
  | nil =>
      intro lit h
      simp [clausesCoreFrom] at h
  | cons c cs ih =>
      intro lit hlit
      simp only [clausesCoreFrom, List.mem_append] at hlit
      cases hlit with
      | inl h =>
          apply clauseCore_model original a k c
          · have hk := congrArg (fun xs : SAT.CNF => xs[0]?) hdrop
            simpa using hk
          · exact ha c (by simp)
          · exact h
      | inr h =>
          apply ih (k + 1)
          · have ht := congrArg List.tail hdrop
            rw [List.tail_drop] at ht
            exact ht
          · intro d hd
            exact ha d (by simp [hd])
          · exact h

theorem satisfiable_imp (φ : SAT.CNF) :
    SAT.Satisfiable φ → EMLSSatisfiable (semanticCore φ) := by
  rintro ⟨a, ha⟩
  refine ⟨model φ a, ?_⟩
  intro lit hlit
  simp only [semanticCore, List.mem_cons, List.mem_append] at hlit
  rcases hlit with rfl | h | h
  · simp [Literal.holds, evalTerm]
  · exact complementCore_model φ a lit h
  · exact clausesCoreFrom_model φ φ a 0 (by simp) ha lit h

private def assignmentOfModel (env : Env) : SAT.Assignment := fun i =>
  ZFSet.mem (env distinguishedVar) (env (positiveVar i))

private def rawLiteral (env : Env) (l : SAT.Literal) : Prop :=
  ZFSet.mem (env distinguishedVar) (env (literalVar l))

private theorem clauseGadgets_raw (env : Env) (hempty : env emptyVar = ZFSet.empty)
    (k j : Nat) (c : SAT.Clause) (hne : c ≠ [])
    (hg : Satisfies env (clauseGadgets k j c))
    (hroot : ZFSet.mem (env distinguishedVar) (env (gadgetVar k j))) :
    ∃ l ∈ c, rawLiteral env l := by
  induction c generalizing j with
  | nil => contradiction
  | cons l rest ih =>
      cases rest with
      | nil =>
          refine ⟨l, by simp, ?_⟩
          have heq := hg
            (.eqOp (gadgetVar k j) (literalVar l) emptyVar .union) (by
              simp [clauseGadgets])
          simp only [Literal.holds, binOpToTerm, evalTerm] at heq
          rw [heq, hempty] at hroot
          change env distinguishedVar ∈ env (literalVar l) ∪ MLS.ZFSet.empty at hroot
          rcases (_root_.ZFSet.mem_union.mp hroot) with hl | hf
          · exact hl
          · exact False.elim ((_root_.ZFSet.notMem_empty _) hf)
      | cons l' rest =>
          have heq := hg
            (.eqOp (gadgetVar k j) (literalVar l)
              (gadgetVar k (j + 1)) .union) (by simp [clauseGadgets])
          simp only [Literal.holds, binOpToTerm, evalTerm] at heq
          rw [heq] at hroot
          change env distinguishedVar ∈
            env (literalVar l) ∪ env (gadgetVar k (j + 1)) at hroot
          rw [_root_.ZFSet.mem_union] at hroot
          cases hroot with
          | inl hl => exact ⟨l, by simp, hl⟩
          | inr hr =>
              obtain ⟨w, hw, hraw⟩ := ih
                (j + 1)
                (by simp)
                (fun lit hlit => hg lit (by simp [clauseGadgets, hlit]))
                hr
              exact ⟨w, by simp [hw], hraw⟩

private theorem complement_for_literal {φ : SAT.CNF} {c : SAT.Clause}
    (hc : c ∈ φ) {l : SAT.Literal} (hl : l ∈ c) :
    ∀ lit ∈ literalComplementGadget l, lit ∈ complementCore φ := by
  intro lit hlit
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨l, hl, hlit⟩

private theorem negative_sound (env : Env) (i : Nat)
    (hg : Satisfies env (complementGadget i))
    (hn : ZFSet.mem (env distinguishedVar) (env (negativeVar i))) :
    ¬assignmentOfModel env i := by
  intro hp
  have hop := hg
    (.eqOp (intersectionVar i) (positiveVar i) (negativeVar i) .inter) (by
      simp [complementGadget])
  have hemp := hg (.eqEmpty (intersectionVar i)) (by simp [complementGadget])
  simp only [Literal.holds, binOpToTerm, evalTerm] at hop hemp
  have hi : env distinguishedVar ∈
      env (positiveVar i) ∩ env (negativeVar i) := by
    apply _root_.ZFSet.mem_inter.mpr
    exact ⟨hp, hn⟩
  change env (intersectionVar i) = env (positiveVar i) ∩ env (negativeVar i) at hop
  rw [← hop, hemp] at hi
  exact (_root_.ZFSet.notMem_empty _) hi

private theorem clauseCore_sound (φ : SAT.CNF) (env : Env)
    (hempty : env emptyVar = ZFSet.empty)
    (hcomp : Satisfies env (complementCore φ))
    (k : Nat) (c : SAT.Clause) (hc : c ∈ φ)
    (hcore : Satisfies env (clauseCore k c)) :
    SAT.evalClause (assignmentOfModel env) c := by
  cases c with
  | nil =>
      have hself := hcore (.mem distinguishedVar distinguishedVar) (by
        simp [clauseCore])
      exact False.elim (EMLS.step4_self_loop_unsat env distinguishedVar hself)
  | cons l rest =>
      have hg : Satisfies env (clauseGadgets k 0 (l :: rest)) := fun lit hlit =>
        hcore lit (by simp [clauseCore, hlit])
      have hm := hcore (.mem distinguishedVar (gadgetVar k 0)) (by
        simp [clauseCore])
      simp only [Literal.holds, evalTerm] at hm
      obtain ⟨w, hw, hraw⟩ :=
        clauseGadgets_raw env hempty k 0 (l :: rest) (by simp) hg hm
      refine ⟨w, hw, ?_⟩
      cases w with
      | pos i => exact hraw
      | neg i =>
          simp only [SAT.evalLiteral]
          apply negative_sound env i
          · intro lit hlit
            apply hcomp lit
            exact complement_for_literal hc hw lit hlit
          · exact hraw

private theorem clausesCoreFrom_sound (φ : SAT.CNF) (env : Env)
    (hempty : env emptyVar = ZFSet.empty)
    (hcomp : Satisfies env (complementCore φ))
    (k : Nat) (cs : SAT.CNF) (hsub : ∀ c ∈ cs, c ∈ φ)
    (hcore : Satisfies env (clausesCoreFrom k cs)) :
    SAT.evalCNF (assignmentOfModel env) cs := by
  induction cs generalizing k with
  | nil => simp [SAT.evalCNF]
  | cons c cs ih =>
      rw [SAT.evalCNF_cons]
      constructor
      · apply clauseCore_sound φ env hempty hcomp k c (hsub c (by simp))
        intro lit hlit
        apply hcore lit
        simp [clausesCoreFrom, hlit]
      · apply ih (k + 1)
        · intro d hd
          exact hsub d (by simp [hd])
        · intro lit hlit
          apply hcore lit
          simp [clausesCoreFrom, hlit]

theorem imp_satisfiable (φ : SAT.CNF) :
    EMLSSatisfiable (semanticCore φ) → SAT.Satisfiable φ := by
  rintro ⟨env, henv⟩
  have hemptyLit := henv (.eqEmpty emptyVar) (by simp [semanticCore])
  simp only [Literal.holds, evalTerm] at hemptyLit
  have hcomp : Satisfies env (complementCore φ) := by
    intro lit hlit
    exact henv lit (by simp [semanticCore, hlit])
  have hclauses : Satisfies env (clausesCoreFrom 0 φ) := by
    intro lit hlit
    exact henv lit (by simp [semanticCore, hlit])
  refine ⟨assignmentOfModel env, ?_⟩
  exact clausesCoreFrom_sound φ env hemptyLit hcomp 0 φ
    (fun c hc => hc) hclauses

/-- Exact semantic correctness of the constructive Theorem 5.2 reduction. -/
theorem satisfiable_iff (φ : SAT.CNF) :
    SAT.Satisfiable φ ↔ EMLSSatisfiable (semanticCore φ) :=
  ⟨satisfiable_imp φ, imp_satisfiable φ⟩

/-! ## Bit-accounted syntactic packaging and inversion

The source is serialized with the standard SAT codec.  A valid idempotence
literal carries the source length, and then one valid idempotence literal is
emitted for every source bit.  Thus no source syntax tree is hidden in one
unaccounted natural-number variable.
-/

private abbrev SourceBits := AvgCaseMls.Foundation.Bitstring

def sourceBits (φ : SAT.CNF) : List Bool :=
  AvgCaseMls.Section4.CookLevin.encodeSATCNF φ

def provenanceHeader (count : Nat) : Literal :=
  .eqOp (count + 4) (count + 4) (count + 4) .union

def provenanceBit : Bool → Literal
  | false => .eqOp 0 0 0 .union
  | true => .eqOp 1 1 1 .union

def provenanceBits (bits : SourceBits) : Conjunct :=
  bits.map provenanceBit

def provenance (φ : SAT.CNF) : Conjunct :=
  provenanceHeader (sourceBits φ).length :: provenanceBits (sourceBits φ)

/-- The injective EMLS reduction, with one target literal per source bit. -/
def toEMLS (φ : SAT.CNF) : Conjunct :=
  provenance φ ++ semanticCore φ

private def decodeProvenanceBits : Nat → Conjunct →
    Option (SourceBits × Conjunct)
  | 0, rest => some ([], rest)
  | count + 1, .eqOp 0 0 0 .union :: rest => do
      let (bits, suffix) ← decodeProvenanceBits count rest
      some (false :: bits, suffix)
  | count + 1, .eqOp 1 1 1 .union :: rest => do
      let (bits, suffix) ← decodeProvenanceBits count rest
      some (true :: bits, suffix)
  | _, _ => none

def decodeProvenance : Conjunct → Option (SourceBits × Conjunct)
  | .eqOp x y z .union :: rest =>
      if _h : x = y ∧ y = z ∧ 4 ≤ x then
        decodeProvenanceBits (x - 4) rest
      else none
  | _ => none

def fromEMLS (conjunct : Conjunct) : Option SAT.CNF := do
  let (bits, rest) ← decodeProvenance conjunct
  let φ ← AvgCaseMls.Section4.CookLevin.decodeSATCNF? bits
  if rest = semanticCore φ then some φ else none

private theorem decodeProvenanceBits_provenanceBits
    (bits : SourceBits) (rest : Conjunct) :
    decodeProvenanceBits bits.length (provenanceBits bits ++ rest) =
      some (bits, rest) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit
      · simp only [List.length_cons, provenanceBits, List.map_cons,
          provenanceBit, List.cons_append, decodeProvenanceBits]
        change (do
          let (tail, suffix) ←
            decodeProvenanceBits bits.length (provenanceBits bits ++ rest)
          some (false :: tail, suffix)) = some (false :: bits, rest)
        rw [ih]
        rfl
      · simp only [List.length_cons, provenanceBits, List.map_cons,
          provenanceBit, List.cons_append, decodeProvenanceBits]
        change (do
          let (tail, suffix) ←
            decodeProvenanceBits bits.length (provenanceBits bits ++ rest)
          some (true :: tail, suffix)) = some (true :: bits, rest)
        rw [ih]
        rfl

@[simp] theorem decodeProvenance_provenance (φ : SAT.CNF) (rest : Conjunct) :
    decodeProvenance (provenance φ ++ rest) =
      some (sourceBits φ, rest) := by
  simp [decodeProvenance, provenance, provenanceHeader,
    decodeProvenanceBits_provenanceBits]

@[simp] theorem fromEMLS_toEMLS (φ : SAT.CNF) :
    fromEMLS (toEMLS φ) = some φ := by
  simp [fromEMLS, toEMLS, sourceBits,
    AvgCaseMls.Section4.CookLevin.decodeSATCNF?_encode]

theorem toEMLS_injective : Function.Injective toEMLS := by
  intro φ ψ h
  have := congrArg fromEMLS h
  simpa using this

private theorem idempotence_holds (env : Env) (n : Nat) :
    Literal.holds env (.eqOp n n n .union) := by
  simp only [Literal.holds, binOpToTerm, evalTerm]
  apply _root_.ZFSet.ext
  intro x
  change (x ∈ env n) ↔ x ∈ env n ∪ env n
  rw [_root_.ZFSet.mem_union]
  tauto

private theorem provenance_holds (env : Env) (φ : SAT.CNF) :
    Satisfies env (provenance φ) := by
  intro literal hliteral
  change literal ∈
    provenanceHeader (sourceBits φ).length :: provenanceBits (sourceBits φ) at hliteral
  rcases List.mem_cons.mp hliteral with rfl | hliteral
  · exact idempotence_holds env _
  · obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hliteral
    cases bit <;> exact idempotence_holds env _

theorem toEMLS_satisfiable_iff (φ : SAT.CNF) :
    SAT.Satisfiable φ ↔ EMLSSatisfiable (toEMLS φ) := by
  rw [satisfiable_iff]
  constructor
  · rintro ⟨env, henv⟩
    refine ⟨env, ?_⟩
    intro lit hlit
    simp only [toEMLS, List.mem_append] at hlit
    rcases hlit with hlit | hlit
    · exact provenance_holds env φ lit hlit
    · exact henv lit hlit
  · rintro ⟨env, henv⟩
    exact ⟨env, fun lit hlit => henv lit (by simp [toEMLS, hlit])⟩

/-- Executable syntax-directed test for the exact reduction range. -/
def inRange (conjunct : Conjunct) : Bool :=
  match fromEMLS conjunct with
  | some φ => decide (toEMLS φ = conjunct)
  | none => false

theorem inRange_eq_true_iff (conjunct : Conjunct) :
    inRange conjunct = true ↔ conjunct ∈ Set.range toEMLS := by
  constructor
  · intro h
    simp only [inRange] at h
    split at h
    · rename_i φ hφ
      exact ⟨φ, by simpa using h⟩
    · simp at h
  · rintro ⟨φ, rfl⟩
    simp [inRange]

/-! ## Exact structural and linear bounds -/

def literalCount (φ : SAT.CNF) : Nat :=
  (φ.map List.length).sum

private theorem complementList_length (c : SAT.Clause) :
    (c.flatMap literalComplementGadget).length = 2 * c.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      cases l <;> simp [literalComplementGadget, complementGadget, ih] <;> omega

private theorem complementCore_length (φ : SAT.CNF) :
    (complementCore φ).length = 2 * literalCount φ := by
  induction φ with
  | nil => simp [complementCore, literalCount]
  | cons c φ ih =>
      simp only [complementCore, List.flatMap_cons, List.length_append,
        literalCount, List.map_cons, List.sum_cons]
      rw [complementList_length]
      change 2 * c.length + (complementCore φ).length =
        2 * (c.length + literalCount φ)
      rw [ih]
      omega

private theorem clauseGadgets_length (k j : Nat) (c : SAT.Clause) :
    (clauseGadgets k j c).length = c.length := by
  induction c generalizing j with
  | nil => simp [clauseGadgets]
  | cons l c ih =>
      cases c <;> simp [clauseGadgets, ih]

private theorem clauseCore_length (k : Nat) (c : SAT.Clause) :
    (clauseCore k c).length = c.length + 1 := by
  cases c with
  | nil => simp [clauseCore]
  | cons l c =>
      simp [clauseCore, clauseGadgets_length]

private theorem clausesCoreFrom_length (k : Nat) (φ : SAT.CNF) :
    (clausesCoreFrom k φ).length = literalCount φ + φ.length := by
  induction φ generalizing k with
  | nil => simp [clausesCoreFrom, literalCount]
  | cons c φ ih =>
      simp [clausesCoreFrom, clauseCore_length, literalCount, ih]
      omega

theorem semanticCore_length (φ : SAT.CNF) :
    (semanticCore φ).length = 1 + 3 * literalCount φ + φ.length := by
  simp [semanticCore, complementCore_length, clausesCoreFrom_length]
  omega

/-- Exact output length of the tagged constructive reduction. -/
theorem toEMLS_length (φ : SAT.CNF) :
    (toEMLS φ).length =
      (sourceBits φ).length + 2 + 3 * literalCount φ + φ.length := by
  simp [toEMLS, provenance, provenanceBits, semanticCore_length]
  omega

/-- Structural output length, now explicitly including every source bit. -/
theorem toEMLS_length_le (φ : SAT.CNF) :
    (toEMLS φ).length ≤ 4 * (sourceBits φ).length + 1 := by
  rw [toEMLS_length]
  have hsize :=
    AvgCaseMls.Section4.CookLevin.encodeSATCNF_size_ge φ
  change SAT.size φ ≤ (sourceBits φ).length at hsize
  simp [SAT.size, literalCount] at hsize ⊢
  omega

/-! ## Standard encoded languages -/

def encodedReduction (φ : SAT.CNF) : AvgCaseMls.Foundation.Bitstring :=
  AvgCaseMls.EMLSCodec.encodeConjunct (toEMLS φ)

theorem encodedReduction_correct (φ : SAT.CNF) :
    sourceBits φ ∈ AvgCaseMls.Section4.CookLevin.EncodedSAT ↔
      encodedReduction φ ∈ AvgCaseMls.EMLSCodec.EncodedEMLSSAT := by
  simpa [sourceBits, AvgCaseMls.Section4.CookLevin.EncodedSAT,
    encodedReduction, EMLSSatisfiable, Satisfies] using
      toEMLS_satisfiable_iff φ

theorem encodedReduction_injective : Function.Injective encodedReduction := by
  intro φ ψ h
  have hconj :=
    AvgCaseMls.EMLSCodec.encodeConjunct_injective h
  exact toEMLS_injective hconj

/--
Honesty at the wire level: the output contains at least one serialized EMLS
literal for every bit of the standard serialized SAT source.
-/
theorem encodedReduction_honest (φ : SAT.CNF) :
    (sourceBits φ).length ≤ (encodedReduction φ).length := by
  have hsource : (sourceBits φ).length ≤ (toEMLS φ).length := by
    rw [toEMLS_length]
    omega
  exact hsource.trans
    (AvgCaseMls.EMLSCodec.conjunct_length_le_encode (toEMLS φ))

/-! ## Binary index accounting -/

def satLiteralIndexWire : SAT.Literal → Nat
  | .pos i | .neg i => (AvgCaseMls.Foundation.encodeNat i).length

def clauseIndexWire (clause : SAT.Clause) : Nat :=
  (clause.map satLiteralIndexWire).sum

def sourceIndexWire (φ : SAT.CNF) : Nat :=
  (φ.map clauseIndexWire).sum

private theorem indexWire_le_encodeSATLiterals (literals : List SAT.Literal) :
    (literals.map satLiteralIndexWire).sum ≤
      (AvgCaseMls.Section4.CookLevin.encodeSATLiterals literals).length := by
  induction literals with
  | nil => simp [AvgCaseMls.Section4.CookLevin.encodeSATLiterals]
  | cons literal literals ih =>
      cases literal <;>
        simp [satLiteralIndexWire,
          AvgCaseMls.Section4.CookLevin.encodeSATLiterals,
          AvgCaseMls.Section4.CookLevin.encodeSATLiteral] at ih ⊢ <;>
        omega

private theorem indexWire_le_encodeSATClause (clause : SAT.Clause) :
    clauseIndexWire clause ≤
      (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length := by
  unfold clauseIndexWire AvgCaseMls.Section4.CookLevin.encodeSATClause
  simp only [List.length_append]
  exact (indexWire_le_encodeSATLiterals clause).trans
    (Nat.le_add_left _ _)

private theorem indexWire_le_encodeSATClauses (φ : SAT.CNF) :
    sourceIndexWire φ ≤
      (AvgCaseMls.Section4.CookLevin.encodeSATClauses φ).length := by
  induction φ with
  | nil => simp [sourceIndexWire,
      AvgCaseMls.Section4.CookLevin.encodeSATClauses]
  | cons clause φ ih =>
      simp only [sourceIndexWire, List.map_cons, List.sum_cons,
        AvgCaseMls.Section4.CookLevin.encodeSATClauses,
        List.length_append]
      exact Nat.add_le_add (indexWire_le_encodeSATClause clause) ih

theorem sourceIndexWire_le_source (φ : SAT.CNF) :
    sourceIndexWire φ ≤ (sourceBits φ).length := by
  unfold sourceBits AvgCaseMls.Section4.CookLevin.encodeSATCNF
  simp only [List.length_append]
  exact (indexWire_le_encodeSATClauses φ).trans
    (Nat.le_add_left _ _)

private theorem renamedIndexWire_le (i r : Nat) (hr : r ≤ 7) :
    (AvgCaseMls.Foundation.encodeNat (4 * i + r)).length ≤
      (AvgCaseMls.Foundation.encodeNat i).length + 6 := by
  have hi := Nat.lt_size_self i
  have hpow : 2 ^ (Nat.size i + 3) = 8 * 2 ^ Nat.size i := by
    rw [pow_add]
    norm_num
    omega
  have hlt : 4 * i + r < 2 ^ (Nat.size i + 3) := by
    rw [hpow]
    nlinarith
  have hs : Nat.size (4 * i + r) ≤ Nat.size i + 3 :=
    Nat.size_le.mpr hlt
  have hsbits :
      (Nat.bits (4 * i + r)).length ≤ (Nat.bits i).length + 3 := by
    simpa only [Nat.size_eq_bits_len] using hs
  rw [AvgCaseMls.Foundation.length_encodeNat,
    AvgCaseMls.Foundation.length_encodeNat]
  omega

private theorem pair_le_square (k j : Nat) :
    Nat.pair k j ≤ (k + j + 1) ^ 2 := by
  unfold Nat.pair
  split <;> nlinarith

private theorem gadgetIndexWire_le (n k j : Nat)
    (hk : k ≤ n) (hj : j ≤ n) :
    (AvgCaseMls.Foundation.encodeNat (gadgetVar k j)).length ≤
      32 * (n + 1) ^ 2 + 9 := by
  have hp := pair_le_square k j
  have hsum : k + j + 1 ≤ 2 * (n + 1) := by omega
  have hsquare : (k + j + 1) ^ 2 ≤ 4 * (n + 1) ^ 2 := by
    nlinarith
  have hvar : gadgetVar k j ≤ 16 * (n + 1) ^ 2 + 4 := by
    unfold gadgetVar
    nlinarith
  exact (AvgCaseMls.Foundation.length_encodeNat_le _).trans (by
    nlinarith)

private def literalWireMass (conjunct : Conjunct) : Nat :=
  (conjunct.map AvgCaseMls.EMLSCodec.literalWireSize).sum

private def gadgetWireBound (n : Nat) : Nat :=
  32 * (n + 1) ^ 2 + 9

private theorem gadgetIndexWire_le_bound (n k j : Nat)
    (hk : k ≤ n) (hj : j ≤ n) :
    (AvgCaseMls.Foundation.encodeNat (gadgetVar k j)).length ≤
      gadgetWireBound n := by
  simpa [gadgetWireBound] using gadgetIndexWire_le n k j hk hj

private theorem literalVarWire_le (literal : SAT.Literal) :
    (AvgCaseMls.Foundation.encodeNat (literalVar literal)).length ≤
      satLiteralIndexWire literal + 6 := by
  cases literal with
  | pos i => exact renamedIndexWire_le i 1 (by omega)
  | neg i => exact renamedIndexWire_le i 2 (by omega)

private theorem complementGadget_wire_le (literal : SAT.Literal) :
    literalWireMass (literalComplementGadget literal) ≤
      4 * satLiteralIndexWire literal + 40 := by
  cases literal with
  | pos i | neg i =>
      have h1 := renamedIndexWire_le i 1 (by omega)
      have h2 := renamedIndexWire_le i 2 (by omega)
      have h7 := renamedIndexWire_le i 7 (by omega)
      simp [literalWireMass, literalComplementGadget, complementGadget,
        AvgCaseMls.EMLSCodec.literalWireSize, satLiteralIndexWire,
        intersectionVar, positiveVar, negativeVar] at h1 h2 h7 ⊢
      omega

private theorem complementList_wire_le (clause : SAT.Clause) :
    literalWireMass (clause.flatMap literalComplementGadget) ≤
      4 * clauseIndexWire clause + 40 * clause.length := by
  induction clause with
  | nil => simp [literalWireMass, clauseIndexWire]
  | cons literal clause ih =>
      simp [literalWireMass, clauseIndexWire] at ih ⊢
      have h := complementGadget_wire_le literal
      unfold literalWireMass at h
      omega

private theorem complementCore_wire_le (φ : SAT.CNF) :
    literalWireMass (complementCore φ) ≤
      4 * sourceIndexWire φ + 40 * literalCount φ := by
  induction φ with
  | nil => simp [literalWireMass, complementCore, sourceIndexWire, literalCount]
  | cons clause φ ih =>
      simp [complementCore, literalWireMass, sourceIndexWire,
        literalCount] at ih ⊢
      have hc := complementList_wire_le clause
      unfold literalWireMass at hc
      omega

private theorem clauseGadgets_wire_le (n k j : Nat) (clause : SAT.Clause)
    (hk : k ≤ n) (hj : j + clause.length ≤ n) :
    literalWireMass (clauseGadgets k j clause) ≤
      (2 * gadgetWireBound n + 100) * clause.length +
        clauseIndexWire clause := by
  induction clause generalizing j with
  | nil => simp [literalWireMass, clauseGadgets, clauseIndexWire]
  | cons literal rest ih =>
      cases rest with
      | nil =>
          simp at hj
          have hj0 : j ≤ n := by omega
          have hg := gadgetIndexWire_le_bound n k j hk hj0
          have hl := literalVarWire_le literal
          have he :
              (AvgCaseMls.Foundation.encodeNat emptyVar).length = 5 := by
            native_decide
          simp only [literalWireMass, clauseGadgets,
            AvgCaseMls.EMLSCodec.literalWireSize,
            clauseIndexWire, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, List.length_cons, List.length_nil]
          rw [he]
          omega
      | cons next rest =>
          simp at hj
          have hj0 : j ≤ n := by omega
          have hj1 : j + 1 ≤ n := by omega
          have hg0 := gadgetIndexWire_le_bound n k j hk hj0
          have hg1 := gadgetIndexWire_le_bound n k (j + 1) hk hj1
          have hl := literalVarWire_le literal
          have htail := ih (j + 1) (by
            have heq :
                (j + 1) + (next :: rest).length =
                  j + (literal :: next :: rest).length := by
                    simp only [List.length_cons]
                    omega
            rw [heq]
            exact hj)
          simp only [AvgCaseMls.Foundation.length_encodeNat] at hg0 hg1 hl
          unfold literalWireMass clauseIndexWire at htail
          rw [clauseGadgets]
          simp only [literalWireMass, List.map_cons, List.sum_cons,
            AvgCaseMls.EMLSCodec.literalWireSize]
          simp only [clauseIndexWire, List.map_cons, List.sum_cons,
            List.length_cons]
          simp [Nat.mul_add, Nat.add_mul] at htail ⊢
          omega

private theorem clauseCore_wire_le (n k : Nat) (clause : SAT.Clause)
    (hk : k ≤ n) (hc : clause.length ≤ n) :
    literalWireMass (clauseCore k clause) ≤
      (2 * gadgetWireBound n + 100) * clause.length +
        clauseIndexWire clause + gadgetWireBound n + 100 := by
  cases clause with
  | nil =>
      simp [literalWireMass, clauseCore, clauseIndexWire,
        AvgCaseMls.EMLSCodec.literalWireSize, gadgetWireBound,
        distinguishedVar]
  | cons literal rest =>
      have hg := clauseGadgets_wire_le n k 0 (literal :: rest) hk (by simpa)
      have hroot := gadgetIndexWire_le_bound n k 0 hk (by omega)
      simp only [AvgCaseMls.Foundation.length_encodeNat] at hroot
      simp [literalWireMass, clauseCore,
        AvgCaseMls.EMLSCodec.literalWireSize, distinguishedVar] at hg ⊢
      simp [Nat.mul_add, Nat.add_mul] at hg ⊢
      omega

private theorem clausesCoreFrom_wire_le (n k : Nat) (φ : SAT.CNF)
    (hk : k + φ.length ≤ n)
    (hlit : literalCount φ ≤ n) :
    literalWireMass (clausesCoreFrom k φ) ≤
      (2 * gadgetWireBound n + 100) * literalCount φ +
        sourceIndexWire φ + (gadgetWireBound n + 100) * φ.length := by
  induction φ generalizing k with
  | nil => simp [literalWireMass, clausesCoreFrom, literalCount, sourceIndexWire]
  | cons clause φ ih =>
      have hclause : clause.length ≤ n := by
        simp [literalCount] at hlit
        omega
      have hcore := clauseCore_wire_le n k clause (by omega) hclause
      have htail := ih (k + 1) (by simp at hk ⊢; omega) (by
        simp [literalCount] at hlit ⊢
        omega)
      simp [clausesCoreFrom, literalWireMass, literalCount,
        sourceIndexWire] at hcore htail ⊢
      simp [Nat.mul_add, Nat.add_mul] at hcore htail ⊢
      omega

private theorem semanticCore_wire_le (φ : SAT.CNF) :
    literalWireMass (semanticCore φ) ≤
      5 * sourceIndexWire φ +
      (2 * gadgetWireBound (sourceBits φ).length + 141) * literalCount φ +
      (gadgetWireBound (sourceBits φ).length + 100) * φ.length + 20 := by
  let n := (sourceBits φ).length
  have hsize :=
    AvgCaseMls.Section4.CookLevin.encodeSATCNF_size_ge φ
  have hφ : φ.length ≤ n := by
    change SAT.size φ ≤ n at hsize
    simp [SAT.size] at hsize
    omega
  have hlit : literalCount φ ≤ n := by
    change SAT.size φ ≤ n at hsize
    change 1 + φ.length + literalCount φ ≤ n at hsize
    omega
  have hcomp := complementCore_wire_le φ
  have hclauses := clausesCoreFrom_wire_le n 0 φ (by simpa) hlit
  simp [semanticCore, literalWireMass,
    AvgCaseMls.EMLSCodec.literalWireSize, emptyVar] at hcomp hclauses ⊢
  dsimp [n] at hclauses hφ hlit ⊢
  have hemptyBits : (Nat.bits 3).length = 2 := by native_decide
  rw [hemptyBits]
  simp [Nat.add_mul] at hclauses ⊢
  omega

private theorem provenanceBits_wire_le (bits : SourceBits) :
    literalWireMass (provenanceBits bits) ≤ 14 * bits.length := by
  induction bits with
  | nil => simp [literalWireMass, provenanceBits]
  | cons bit bits ih =>
      cases bit <;>
        simp [literalWireMass, provenanceBits, provenanceBit,
          AvgCaseMls.EMLSCodec.literalWireSize] at ih ⊢ <;>
        omega

private theorem provenance_wire_le (φ : SAT.CNF) :
    literalWireMass (provenance φ) ≤ 20 * (sourceBits φ).length + 32 := by
  let n := (sourceBits φ).length
  have hbits := provenanceBits_wire_le (sourceBits φ)
  have hn :=
    AvgCaseMls.Foundation.length_encodeNat_le (n + 4)
  simp only [AvgCaseMls.Foundation.length_encodeNat] at hn
  simp [literalWireMass, provenance, provenanceHeader,
    AvgCaseMls.EMLSCodec.literalWireSize] at hbits ⊢
  dsimp [n] at hn ⊢
  omega

def encodedWireBound (n : Nat) : Nat :=
  1000 * (n + 2) ^ 3

theorem encodedWireBound_polynomial :
    AvgCaseMls.Foundation.IsPolynomial encodedWireBound := by
  apply AvgCaseMls.Foundation.IsPolynomial.bounded 27000 3
  intro n
  unfold encodedWireBound
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : 1 ≤ n + 1 := by omega
      nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]

/--
True forward wire bound for the standard EMLS serialization.  Both source
variable names and `(clause,step)` gadget names are charged through the binary
natural codec.
-/
theorem encodedReduction_wire_le (φ : SAT.CNF) :
    (encodedReduction φ).length ≤
      encodedWireBound (sourceBits φ).length := by
  let n := (sourceBits φ).length
  have hsize :=
    AvgCaseMls.Section4.CookLevin.encodeSATCNF_size_ge φ
  have hindex := sourceIndexWire_le_source φ
  have hstruct : φ.length + literalCount φ + 1 ≤ n := by
    change SAT.size φ ≤ n at hsize
    simpa [SAT.size, literalCount, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsize
  have hsemantic := semanticCore_wire_le φ
  have hprovenance := provenance_wire_le φ
  have hmass :
      literalWireMass (toEMLS φ) =
        literalWireMass (provenance φ) +
          literalWireMass (semanticCore φ) := by
    simp [toEMLS, literalWireMass]
  have hcount := toEMLS_length_le φ
  have hheader :=
    AvgCaseMls.Foundation.length_encodeNat_le (toEMLS φ).length
  unfold encodedReduction
  rw [AvgCaseMls.EMLSCodec.encodeConjunct_length]
  unfold AvgCaseMls.EMLSCodec.conjunctWireSize
  change
    (AvgCaseMls.Foundation.encodeNat (toEMLS φ).length).length +
      literalWireMass (toEMLS φ) ≤ _
  rw [hmass]
  dsimp [n] at hindex hstruct hsemantic hprovenance hcount ⊢
  unfold gadgetWireBound at hsemantic
  unfold encodedWireBound
  nlinarith [hheader, sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]

end EMLSReduction
