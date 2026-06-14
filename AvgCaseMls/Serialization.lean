/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom
import AvgCaseMls.DecideMLS

/-!
Phase **2D:** binary encoding of MLS formulas and a syntactic step budget for [`decideMLS`].

See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md) for encoding choices. Polynomial
size bounds (Phase **3B**) can cite [`formulaSize`] and [`len_serializeFormula`].
-/

namespace MLS

open AvCom EMLS

/-! ### Nat and syntax tags -/

/-- Unary Nat encoding: `n` copies of `true` followed by `false`. -/
def encodeNat : Nat → Bitstring
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def termTag : Term → Bitstring
  | .var _ => [false, false, false]
  | .empty => [false, false, true]
  | .union _ _ => [false, true, false]
  | .inter _ _ => [false, true, true]
  | .diff _ _ => [true, false, false]

def relationTag : Relation → Bitstring
  | .mem _ _ => [false, false]
  | .not_mem _ _ => [false, true]
  | .eq _ _ => [true, false]
  | .neq _ _ => [true, true]

def formulaTag : Formula → Bitstring
  | .rel _ => [false, false, false]
  | .not _ => [false, false, true]
  | .and _ _ => [false, true, false]
  | .or _ _ => [false, true, true]
  | .imp _ _ => [true, false, false]
  | .iff _ _ => [true, false, true]

@[simp] theorem len_encodeNat (n : Nat) : len (encodeNat n) = n + 1 := by
  induction n with
  | zero => simp [encodeNat, len]
  | succ n ih =>
    simp only [encodeNat, len, List.length_cons]
    rw [← len_eq, ih]

@[simp] theorem length_encodeNat (n : Nat) : (encodeNat n).length = n + 1 := by
  simpa [len_eq] using len_encodeNat n

@[simp] theorem len_termTag (t : Term) : len (termTag t) = 3 := by
  cases t <;> simp [termTag, len]

@[simp] theorem len_relationTag (r : Relation) : len (relationTag r) = 2 := by
  cases r <;> simp [relationTag, len]

@[simp] theorem len_formulaTag (f : Formula) : len (formulaTag f) = 3 := by
  cases f <;> simp [formulaTag, len]

/-! ### Wire sizes (exact serialized length) -/

def wireSizeNat (n : Nat) : Nat := n + 1

def wireSizeTerm : Term → Nat
  | .var n => 3 + wireSizeNat n
  | .empty => 3
  | .union t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .inter t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .diff t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeRelation : Relation → Nat
  | .mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .not_mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .eq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .neq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeFormula : Formula → Nat
  | .rel r => 3 + wireSizeRelation r
  | .not f => 3 + wireSizeFormula f
  | .and f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .or f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .imp f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .iff f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2

abbrev formulaSize := wireSizeFormula

/-! ### Serialization -/

def serializeTerm : Term → Bitstring
  | .var n => termTag (.var n) ++ encodeNat n
  | .empty => termTag Term.empty
  | .union t1 t2 => termTag (.union t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .inter t1 t2 => termTag (.inter t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .diff t1 t2 => termTag (.diff t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeRelation : Relation → Bitstring
  | .mem t1 t2 => relationTag (.mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .not_mem t1 t2 => relationTag (.not_mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .eq t1 t2 => relationTag (.eq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .neq t1 t2 => relationTag (.neq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeFormula : Formula → Bitstring
  | .rel r => formulaTag (.rel r) ++ serializeRelation r
  | .not f => formulaTag (.not f) ++ serializeFormula f
  | .and f1 f2 => formulaTag (.and f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .or f1 f2 => formulaTag (.or f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .imp f1 f2 => formulaTag (.imp f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .iff f1 f2 => formulaTag (.iff f1 f2) ++ serializeFormula f1 ++ serializeFormula f2

theorem length_serializeTerm (t : Term) : (serializeTerm t).length = wireSizeTerm t := by
  induction t with
  | var n =>
    simp [serializeTerm, wireSizeTerm, wireSizeNat, termTag, List.length_append, length_encodeNat]
    omega
  | empty => simp [serializeTerm, wireSizeTerm, termTag]
  | union t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega
  | inter t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega
  | diff t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega

theorem len_serializeTerm (t : Term) : len (serializeTerm t) = wireSizeTerm t := by
  simpa [len_eq] using length_serializeTerm t

theorem length_serializeRelation (r : Relation) : (serializeRelation r).length = wireSizeRelation r := by
  cases r with
  | mem t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | not_mem t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | eq t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | neq t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega

theorem len_serializeRelation (r : Relation) : len (serializeRelation r) = wireSizeRelation r := by
  simpa [len_eq] using length_serializeRelation r

theorem length_serializeFormula (f : Formula) : (serializeFormula f).length = wireSizeFormula f := by
  induction f with
  | rel r =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append,
      length_serializeRelation r]
    omega
  | not f ih =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih]
    omega
  | and f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | or f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | imp f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | iff f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega

theorem len_serializeFormula (f : Formula) : len (serializeFormula f) = wireSizeFormula f := by
  simpa [len_eq] using length_serializeFormula f

theorem wireSizeTerm_pos (t : Term) : 0 < wireSizeTerm t := by
  cases t <;> simp [wireSizeTerm, wireSizeNat]

theorem formulaSize_pos (f : Formula) : 0 < wireSizeFormula f := by
  cases f with
  | rel r =>
    cases r <;> simp [wireSizeFormula, wireSizeRelation, wireSizeTerm, wireSizeNat] <;> omega
  | not f =>
    simp only [wireSizeFormula]
    have h := formulaSize_pos f
    omega
  | and f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | or f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | imp f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | iff f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega

/-! ### Step budget for [`decideMLS`] -/

/-- Syntactic step budget for FOS80 Steps 2–4 on conjunct `c`. -/
def stepsConjunct (c : Conjunct) : Nat :=
  let n := c.length
  n * n + (neqLiterals c).length + (varsInConjunct c).length + 1

/--
Step budget for [`decideMLSSat`]: AST size plus conjunct decision work when
[`formulaToConjunct?`] succeeds.
-/
def stepsMLS (f : Formula) : Nat :=
  wireSizeFormula f +
    match formulaToConjunct? f with
    | none => 0
    | some c => stepsConjunct c

theorem stepsMLS_pos (f : Formula) : 0 < stepsMLS f := by
  simp only [stepsMLS]
  exact Nat.add_pos_left (formulaSize_pos f) _

end MLS
