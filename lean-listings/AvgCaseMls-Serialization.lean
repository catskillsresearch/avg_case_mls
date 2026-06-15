/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom
import AvgCaseMls.DecideMLS
import Mathlib.Tactic

/-!
Phase **2D:** binary encoding of MLS formulas and a syntactic step budget for [`decideMLS`].

See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md) for encoding choices. Polynomial
size bounds (Phase **3B**) can cite [`formulaSize`] and [`len_serializeFormula`].
-/

namespace MLS

open AvCom EMLS

/-! ### Nat and syntax tags -/

/-- Unary Nat encoding: `n` copies of `true` followed by `false`. -/
def encodeNat : Nat -> Bitstring
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def termTag : Term -> Bitstring
  | .var _ => [false, false, false]
  | .empty => [false, false, true]
  | .union _ _ => [false, true, false]
  | .inter _ _ => [false, true, true]
  | .diff _ _ => [true, false, false]

def relationTag : Relation -> Bitstring
  | .mem _ _ => [false, false]
  | .not_mem _ _ => [false, true]
  | .eq _ _ => [true, false]
  | .neq _ _ => [true, true]

def formulaTag : Formula -> Bitstring
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
    rw [<- len_eq, ih]

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

def wireSizeTerm : Term -> Nat
  | .var n => 3 + wireSizeNat n
  | .empty => 3
  | .union t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .inter t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .diff t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeRelation : Relation -> Nat
  | .mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .not_mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .eq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .neq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeFormula : Formula -> Nat
  | .rel r => 3 + wireSizeRelation r
  | .not f => 3 + wireSizeFormula f
  | .and f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .or f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .imp f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .iff f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2

abbrev formulaSize := wireSizeFormula

/-! ### Serialization -/

def serializeTerm : Term -> Bitstring
  | .var n => termTag (.var n) ++ encodeNat n
  | .empty => termTag Term.empty
  | .union t1 t2 => termTag (.union t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .inter t1 t2 => termTag (.inter t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .diff t1 t2 => termTag (.diff t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeRelation : Relation -> Bitstring
  | .mem t1 t2 => relationTag (.mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .not_mem t1 t2 => relationTag (.not_mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .eq t1 t2 => relationTag (.eq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .neq t1 t2 => relationTag (.neq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeFormula : Formula -> Bitstring
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

/-- Syntactic step budget for FOS80 Steps 2-4 on conjunct `c`. -/
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

/-! ### Phase 3B - syntax mass and polynomial encoding bounds -/

def termNodes : Term -> Nat
  | .var _ => 1
  | .empty => 1
  | .union t1 t2 => 1 + termNodes t1 + termNodes t2
  | .inter t1 t2 => 1 + termNodes t1 + termNodes t2
  | .diff t1 t2 => 1 + termNodes t1 + termNodes t2

def maxVarTerm : Term -> Nat
  | .var n => n
  | .empty => 0
  | .union t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .inter t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .diff t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)

def relationNodes : Relation -> Nat
  | .mem t1 t2 => 1 + termNodes t1 + termNodes t2
  | .not_mem t1 t2 => 1 + termNodes t1 + termNodes t2
  | .eq t1 t2 => 1 + termNodes t1 + termNodes t2
  | .neq t1 t2 => 1 + termNodes t1 + termNodes t2

def maxVarRelation : Relation -> Nat
  | .mem t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .not_mem t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .eq t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .neq t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)

def formulaNodes : Formula -> Nat
  | .rel r => 1 + relationNodes r
  | .not f => 1 + formulaNodes f
  | .and f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .or f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .imp f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .iff f1 f2 => 1 + formulaNodes f1 + formulaNodes f2

def maxVarFormula : Formula -> Nat
  | .rel r => maxVarRelation r
  | .not f => maxVarFormula f
  | .and f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .or f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .imp f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .iff f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)

/-- Single-parameter syntax mass: AST node count plus largest variable index. -/
def formulaAstMass (f : Formula) : Nat :=
  formulaNodes f + maxVarFormula f

theorem termNodes_pos (t : Term) : 0 < termNodes t := by
  cases t <;> simp [termNodes] <;> omega

theorem relationNodes_pos (r : Relation) : 0 < relationNodes r := by
  cases r <;> simp [relationNodes, termNodes] <;> omega

/-- Polynomial slack bound helper (Phase **3B**). Quadratic in `n + 2`. -/
def nodeBound (n : Nat) : Nat :=
  (n + 2) ^ 2 * 1000000000000 + 1000000000000

theorem nodeBound_mono {m n : Nat} (h : m <= n) : nodeBound m <= nodeBound n := by
  have hb : m + 2 <= n + 2 := Nat.add_le_add_right h 2
  have h2 := Nat.pow_le_pow_left hb 2
  simp [nodeBound]
  nlinarith

theorem formulaNodes_pos (f : Formula) : 0 < formulaNodes f := by
  cases f with
  | rel r => simp [formulaNodes, relationNodes_pos r]
  | not f => simp [formulaNodes, formulaNodes_pos f]
  | and f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | or f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | imp f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | iff f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]

def termMass (t : Term) : Nat := termNodes t + maxVarTerm t

def relationMass (r : Relation) : Nat := relationNodes r + maxVarRelation r

def formulaMass (f : Formula) : Nat := formulaNodes f + maxVarFormula f

theorem termMass_pos (t : Term) : 0 < termMass t := by
  cases t <;> simp [termMass, termNodes, maxVarTerm] <;> omega

theorem relationMass_pos (r : Relation) : 0 < relationMass r := by
  cases r <;> simp [relationMass, relationNodes, maxVarRelation, termNodes, termMass] <;> omega

theorem formulaMass_pos (f : Formula) : 0 < formulaMass f := by
  cases f <;> simp [formulaMass, formulaNodes, maxVarFormula, relationMass, relationNodes] <;>
    try linarith [relationMass_pos _, formulaMass_pos _, formulaNodes_pos _, relationNodes_pos _] <;>
    omega

theorem termMass_lt_combine_left (t1 t2 : Term) :
    termMass t1 + 1 < 1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2) := by
  simp [termMass, termNodes, maxVarTerm]
  have := termNodes_pos t2
  omega

theorem termMass_lt_combine_right (t1 t2 : Term) :
    termMass t2 + 1 < 1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2) := by
  simp [termMass, termNodes, maxVarTerm]
  have := termNodes_pos t1
  omega

theorem termMass_lt_union_left (t1 t2 : Term) : termMass t1 + 1 < termMass (.union t1 t2) := by
  simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_left t1 t2

theorem termMass_lt_union_right (t1 t2 : Term) : termMass t2 + 1 < termMass (.union t1 t2) := by
  simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_right t1 t2

theorem formulaMass_lt_combine_left (f1 f2 : Formula) :
    formulaMass f1 + 1 <
      1 + formulaNodes f1 + formulaNodes f2 + max (maxVarFormula f1) (maxVarFormula f2) := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  have := formulaNodes_pos f2
  omega

theorem formulaMass_lt_combine_right (f1 f2 : Formula) :
    formulaMass f2 + 1 <
      1 + formulaNodes f1 + formulaNodes f2 + max (maxVarFormula f1) (maxVarFormula f2) := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  have := formulaNodes_pos f1
  omega

theorem nodeBound_pow_gap (m : Nat) :
    1000000000000 * ((m + 3) ^ 2 - (m + 2) ^ 2) >= 3 := by
  have hsq : (m + 3) ^ 2 = (m + 2) ^ 2 + (2 * m + 5) := by ring_nf
  have : 3 <= 2 * m + 5 := by omega
  omega

theorem nodeBound_succ (m : Nat) : nodeBound m + 3 <= nodeBound (m + 1) := by
  simp [nodeBound]
  have hsq : (m + 3) ^ 2 = (m + 2) ^ 2 + (2 * m + 5) := by ring_nf
  nlinarith

theorem nodeBound_add3_le_succ (m : Nat) : 3 + nodeBound m <= nodeBound (m + 1) := by
  simpa [Nat.add_comm] using nodeBound_succ m

/-- Sum of two child [`nodeBound`]s fits at combined index `a + b + 1` (Phase **3B**). -/
theorem nodeBound_pair_sum_le {a b : Nat} (ha : 1 <= a) (hb : 1 <= b) :
    3 + nodeBound a + nodeBound b <= nodeBound (a + b + 1) := by
  simp [nodeBound]
  nlinarith [sq_nonneg (a : Int), sq_nonneg (b : Int)]

theorem termMass_combine_le (t1 t2 : Term) :
    termMass (.union t1 t2) <= termMass t1 + termMass t2 + 1 := by
  simp [termMass, termNodes, maxVarTerm]
  omega

theorem termMass_inter_le (t1 t2 : Term) :
    termMass (.inter t1 t2) <= termMass t1 + termMass t2 + 1 := by
  simp [termMass, termNodes, maxVarTerm]
  omega

theorem termMass_diff_le (t1 t2 : Term) :
    termMass (.diff t1 t2) <= termMass t1 + termMass t2 + 1 := by
  simp [termMass, termNodes, maxVarTerm]
  omega

theorem formulaMass_combine_le (f1 f2 : Formula) :
    formulaMass (f1.and f2) <= formulaMass f1 + formulaMass f2 + 1 := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  omega

theorem formulaMass_or_le (f1 f2 : Formula) :
    formulaMass (f1.or f2) <= formulaMass f1 + formulaMass f2 + 1 := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  omega

theorem formulaMass_imp_le (f1 f2 : Formula) :
    formulaMass (f1.imp f2) <= formulaMass f1 + formulaMass f2 + 1 := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  omega

theorem formulaMass_iff_le (f1 f2 : Formula) :
    formulaMass (f1.iff f2) <= formulaMass f1 + formulaMass f2 + 1 := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  omega

private theorem sqMass_le_nodeBound (m : Nat) : (m + 30) ^ 2 <= nodeBound m := by
  simp [nodeBound]
  nlinarith [sq_nonneg (m : Int)]

private def wireEndSlack : Nat := 603

private theorem wireSizeTerm_rec_bound (t : Term) :
    wireSizeTerm t <= (termNodes t + 1) * (maxVarTerm t + 4) + 3 * termNodes t := by
  induction t with
  | var n =>
    simp [wireSizeTerm, termNodes, maxVarTerm, wireSizeNat]
    ring_nf
    omega
  | empty => simp [wireSizeTerm, termNodes, maxVarTerm]
  | union t1 t2 ih1 ih2 | inter t1 t2 ih1 ih2 | diff t1 t2 ih1 ih2 =>
    have hM1 : maxVarTerm t1 <= max (maxVarTerm t1) (maxVarTerm t2) := Nat.le_max_left _ _
    have hM2 : maxVarTerm t2 <= max (maxVarTerm t1) (maxVarTerm t2) := Nat.le_max_right _ _
    have ih1' : wireSizeTerm t1 <=
        (termNodes t1 + 1) * (max (maxVarTerm t1) (maxVarTerm t2) + 4) + 3 * termNodes t1 := by
      nlinarith [ih1, hM1]
    have ih2' : wireSizeTerm t2 <=
        (termNodes t2 + 1) * (max (maxVarTerm t1) (maxVarTerm t2) + 4) + 3 * termNodes t2 := by
      nlinarith [ih2, hM2]
    simp [wireSizeTerm, termNodes, maxVarTerm]
    nlinarith [ih1', ih2', termNodes_pos t1, termNodes_pos t2]

private theorem wireSizeTerm_mul_bound (t : Term) :
    wireSizeTerm t <= (termNodes t + 1) * (maxVarTerm t + 4) + 3 * termNodes t + wireEndSlack := by
  nlinarith [wireSizeTerm_rec_bound t]

private theorem wireSizeTerm_mul_bound_le_nodeBound (t : Term) :
    (termNodes t + 1) * (maxVarTerm t + 4) + 3 * termNodes t + wireEndSlack <= nodeBound (termMass t) := by
  have h1 : (termNodes t + 1) * (maxVarTerm t + 4) + 3 * termNodes t + wireEndSlack <=
      (termMass t + 30) ^ 2 := by
    simp [termMass, wireEndSlack]
    nlinarith [sq_nonneg (termNodes t : Int), sq_nonneg (maxVarTerm t : Int), termNodes_pos t]
  exact Nat.le_trans h1 (sqMass_le_nodeBound (termMass t))

private theorem wireSizeTerm_le_nodeBound_aux (t : Term) : wireSizeTerm t <= nodeBound (termMass t) :=
  Nat.le_trans (wireSizeTerm_mul_bound t) (wireSizeTerm_mul_bound_le_nodeBound t)

private theorem wireSizeRelation_rec_bound (r : Relation) :
    wireSizeRelation r <= (relationNodes r + 1) * (maxVarRelation r + 4) + 3 * relationNodes r := by
  cases r with
  | mem t1 t2 | not_mem t1 t2 | eq t1 t2 | neq t1 t2 =>
    have hM1 : maxVarTerm t1 <= max (maxVarTerm t1) (maxVarTerm t2) := Nat.le_max_left _ _
    have hM2 : maxVarTerm t2 <= max (maxVarTerm t1) (maxVarTerm t2) := Nat.le_max_right _ _
    have ih1' : wireSizeTerm t1 <=
        (termNodes t1 + 1) * (max (maxVarTerm t1) (maxVarTerm t2) + 4) + 3 * termNodes t1 := by
      nlinarith [wireSizeTerm_rec_bound t1, hM1]
    have ih2' : wireSizeTerm t2 <=
        (termNodes t2 + 1) * (max (maxVarTerm t1) (maxVarTerm t2) + 4) + 3 * termNodes t2 := by
      nlinarith [wireSizeTerm_rec_bound t2, hM2]
    simp [wireSizeRelation, relationNodes, maxVarRelation, relationMass, termNodes, maxVarTerm]
    nlinarith [ih1', ih2', termNodes_pos t1, termNodes_pos t2]

private theorem wireSizeRelation_mul_bound (r : Relation) :
    wireSizeRelation r <= (relationNodes r + 1) * (maxVarRelation r + 4) + 3 * relationNodes r +
      wireEndSlack + 3 := by
  nlinarith [wireSizeRelation_rec_bound r]

private theorem wireSizeRelation_mul_bound_le_nodeBound (r : Relation) :
    (relationNodes r + 1) * (maxVarRelation r + 4) + 3 * relationNodes r + wireEndSlack + 3 <=
      nodeBound (relationMass r) := by
  have h1 : (relationNodes r + 1) * (maxVarRelation r + 4) + 3 * relationNodes r + wireEndSlack + 3 <=
      (relationMass r + 30) ^ 2 := by
    simp [relationMass, wireEndSlack, relationNodes, maxVarRelation]
    nlinarith [sq_nonneg (relationNodes r : Int), sq_nonneg (maxVarRelation r : Int), relationMass_pos r]
  exact Nat.le_trans h1 (sqMass_le_nodeBound (relationMass r))

private theorem wireSizeRelation_le_nodeBound_aux (r : Relation) :
    wireSizeRelation r <= nodeBound (relationMass r) :=
  Nat.le_trans (wireSizeRelation_mul_bound r) (wireSizeRelation_mul_bound_le_nodeBound r)

private theorem wireSizeFormula_rec_bound (f : Formula) :
    wireSizeFormula f <= (formulaNodes f + 1) * (maxVarFormula f + 4) + 3 * formulaNodes f := by
  induction f with
  | rel r =>
    have hr := wireSizeRelation_rec_bound r
    simp [wireSizeFormula, formulaNodes, maxVarFormula]
    nlinarith [hr, relationNodes_pos r]
  | not f ih =>
    simp [wireSizeFormula, formulaNodes, maxVarFormula]
    nlinarith [ih, formulaNodes_pos f]
  | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 | imp f1 f2 ih1 ih2 | iff f1 f2 ih1 ih2 =>
    have hM1 : maxVarFormula f1 <= max (maxVarFormula f1) (maxVarFormula f2) := Nat.le_max_left _ _
    have hM2 : maxVarFormula f2 <= max (maxVarFormula f1) (maxVarFormula f2) := Nat.le_max_right _ _
    have ih1' : wireSizeFormula f1 <=
        (formulaNodes f1 + 1) * (max (maxVarFormula f1) (maxVarFormula f2) + 4) + 3 * formulaNodes f1 := by
      nlinarith [ih1, hM1]
    have ih2' : wireSizeFormula f2 <=
        (formulaNodes f2 + 1) * (max (maxVarFormula f1) (maxVarFormula f2) + 4) + 3 * formulaNodes f2 := by
      nlinarith [ih2, hM2]
    simp [wireSizeFormula, formulaNodes, maxVarFormula]
    nlinarith [ih1', ih2', formulaNodes_pos f1, formulaNodes_pos f2]

private theorem wireSizeFormula_mul_bound (f : Formula) :
    wireSizeFormula f <= (formulaNodes f + 1) * (maxVarFormula f + 4) + 3 * formulaNodes f +
      wireEndSlack + 3 := by
  nlinarith [wireSizeFormula_rec_bound f]

private theorem wireSizeFormula_mul_bound_le_nodeBound (f : Formula) :
    (formulaNodes f + 1) * (maxVarFormula f + 4) + 3 * formulaNodes f + wireEndSlack + 3 <=
      nodeBound (formulaMass f) := by
  have h1 : (formulaNodes f + 1) * (maxVarFormula f + 4) + 3 * formulaNodes f + wireEndSlack + 3 <=
      (formulaMass f + 30) ^ 2 := by
    simp [formulaMass, wireEndSlack, formulaNodes, maxVarFormula]
    nlinarith [sq_nonneg (formulaNodes f : Int), sq_nonneg (maxVarFormula f : Int), formulaMass_pos f]
  exact Nat.le_trans h1 (sqMass_le_nodeBound (formulaMass f))

private theorem wireSizeFormula_le_nodeBound_aux (f : Formula) :
    wireSizeFormula f <= nodeBound (formulaMass f) :=
  Nat.le_trans (wireSizeFormula_mul_bound f) (wireSizeFormula_mul_bound_le_nodeBound f)

theorem formulaMass_eq_astMass (f : Formula) : formulaMass f = formulaAstMass f := by
  rfl

theorem wireSizeTerm_le_nodeBound (t : Term) :
    wireSizeTerm t <= nodeBound (termMass t) :=
  wireSizeTerm_le_nodeBound_aux t

theorem wireSizeRelation_le_nodeBound (r : Relation) :
    wireSizeRelation r <= nodeBound (relationMass r) :=
  wireSizeRelation_le_nodeBound_aux r

theorem formulaSize_le_nodeBound (f : Formula) :
    formulaSize f <= nodeBound (formulaMass f) :=
  wireSizeFormula_le_nodeBound_aux f

theorem formulaNodes_le_astMass (f : Formula) : formulaNodes f <= formulaAstMass f := by
  simp [formulaAstMass, Nat.le_add_right]

/-- Polynomial upper bound on encoded length from syntax mass. -/
def encodingBound (n : Nat) : Nat :=
  nodeBound n + 2

theorem encodingBound_mono {m n : Nat} (h : m <= n) :
    encodingBound m <= encodingBound n := by
  unfold encodingBound
  exact Nat.add_le_add_right (nodeBound_mono h) 2

theorem formulaSize_le_mass (f : Formula) :
    formulaSize f <= encodingBound (formulaAstMass f) := by
  have h := formulaSize_le_nodeBound f
  simpa [formulaMass_eq_astMass, encodingBound] using Nat.le_trans h (Nat.le_add_right _ 2)

theorem encodingBound_poly : IsPolynomial encodingBound := by
  refine <6000000000000, 2, fun n => ?_>
  simp only [encodingBound, nodeBound]
  have h : (n + 2) ^ 2 <= 5 * n ^ 2 + 5 := by
    cases n with
    | zero => decide
    | succ n => nlinarith
  nlinarith

theorem formulaSize_le_encodingBound (f : Formula) :
    formulaSize f <= encodingBound (formulaAstMass f) :=
  formulaSize_le_mass f

theorem formulaSize_le_polyMass (f : Formula) (n : Nat) (h : formulaAstMass f <= n) :
    formulaSize f <= encodingBound n :=
  Nat.le_trans (formulaSize_le_encodingBound f) (encodingBound_mono h)

/-! ### Phase 3A - deserialization (inverse of [`serializeFormula`]) -/

def stripPrefix? (xs expected : Bitstring) : Option Bitstring :=
  if h : xs.length >= expected.length /\ xs.take expected.length = expected then
    some (xs.drop expected.length)
  else
    none

def decodeNat? : Bitstring -> Option (Nat x Bitstring)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match decodeNat? rest with
    | none => none
    | some (n, rest') => some (n + 1, rest')

mutual
def decodeTermFuel (fuel : Nat) (bits : Bitstring) : Option (Term x Bitstring) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if bits.length < 3 then
      none
    else if bits.take 3 = [false, false, false] then
      match decodeNat? (bits.drop 3) with
      | some (n, rest) => some (.var n, rest)
      | none => none
    else if bits.take 3 = [false, false, true] then
      some (.empty, bits.drop 3)
    else if bits.take 3 = [false, true, false] then
      match decodeTermFuel fuel (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.union t1 t2, rest')
        | none => none
      | none => none
    else if bits.take 3 = [false, true, true] then
      match decodeTermFuel fuel (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.inter t1 t2, rest')
        | none => none
      | none => none
    else if bits.take 3 = [true, false, false] then
      match decodeTermFuel fuel (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.diff t1 t2, rest')
        | none => none
      | none => none
    else
      none

def decodeRelationFuel (fuel : Nat) (bits : Bitstring) : Option (Relation x Bitstring) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if bits.length < 2 then
      none
    else if bits.take 2 = [false, false] then
      match decodeTermFuel fuel (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.mem t1 t2, rest')
        | none => none
      | none => none
    else if bits.take 2 = [false, true] then
      match decodeTermFuel fuel (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.not_mem t1 t2, rest')
        | none => none
      | none => none
    else if bits.take 2 = [true, false] then
      match decodeTermFuel fuel (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.eq t1 t2, rest')
        | none => none
      | none => none
    else if bits.take 2 = [true, true] then
      match decodeTermFuel fuel (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTermFuel fuel rest with
        | some (t2, rest') => some (.neq t1 t2, rest')
        | none => none
      | none => none
    else
      none

def decodeFormulaFuel (fuel : Nat) (bits : Bitstring) : Option (Formula x Bitstring) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if bits.length < 3 then
      none
    else if bits.take 3 = [false, false, false] then
      match decodeRelationFuel fuel (bits.drop 3) with
      | some (r, rest) => some (.rel r, rest)
      | none => none
    else if bits.take 3 = [false, false, true] then
      match decodeFormulaFuel fuel (bits.drop 3) with
      | some (f, rest) => some (.not f, rest)
      | none => none
    else if bits.take 3 = [false, true, false] then
      match decodeFormulaFuel fuel (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormulaFuel fuel rest with
        | some (f2, rest') => some (.and f1 f2, rest')
        | none => none
      | none => none
    else if bits.take 3 = [false, true, true] then
      match decodeFormulaFuel fuel (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormulaFuel fuel rest with
        | some (f2, rest') => some (.or f1 f2, rest')
        | none => none
      | none => none
    else if bits.take 3 = [true, false, false] then
      match decodeFormulaFuel fuel (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormulaFuel fuel rest with
        | some (f2, rest') => some (.imp f1 f2, rest')
        | none => none
      | none => none
    else if bits.take 3 = [true, false, true] then
      match decodeFormulaFuel fuel (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormulaFuel fuel rest with
        | some (f2, rest') => some (.iff f1 f2, rest')
        | none => none
      | none => none
    else
      none
termination_by fuel
decreasing_by
  all_goals simp_wf <;> split <;> omega

def decodeTerm? (bits : Bitstring) : Option (Term x Bitstring) :=
  decodeTermFuel bits.length bits

def decodeRelation? (bits : Bitstring) : Option (Relation x Bitstring) :=
  decodeRelationFuel bits.length bits

def decodeFormula? (bits : Bitstring) : Option (Formula x Bitstring) :=
  decodeFormulaFuel bits.length bits

end

theorem decodeNat?_encodeNat (n : Nat) : decodeNat? (encodeNat n) = some (n, []) := by
  induction n with
  | zero => simp [decodeNat?, encodeNat]
  | succ n ih => simp [decodeNat?, encodeNat, ih]

theorem decodeNat?_suffix (n : Nat) (rest : Bitstring) :
    decodeNat? (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [decodeNat?, encodeNat]
  | succ n ih => simp [decodeNat?, encodeNat, ih, List.append_assoc]

private theorem take_prefix3 (p xs rest : Bitstring) (h : len p = 3) :
    List.take 3 (p ++ xs ++ rest) = p := by
  rw [len_eq] at h
  rw [List.append_assoc, List.take_append, h, Nat.sub_self, List.take_zero, List.append_nil]
  rw [<- h, List.take_length]

private theorem take_prefix2 (p xs rest : Bitstring) (h : len p = 2) :
    List.take 2 (p ++ xs ++ rest) = p := by
  rw [len_eq] at h
  rw [List.append_assoc, List.take_append, h, Nat.sub_self, List.take_zero, List.append_nil]
  rw [<- h, List.take_length]

@[simp] theorem take_termTag3 (t : Term) (mid rest : Bitstring) :
    List.take 3 (termTag t ++ mid ++ rest) = termTag t :=
  take_prefix3 (termTag t) mid rest (len_termTag t)

@[simp] theorem take_relationTag2 (r : Relation) (mid rest : Bitstring) :
    List.take 2 (relationTag r ++ mid ++ rest) = relationTag r :=
  take_prefix2 (relationTag r) mid rest (len_relationTag r)

@[simp] theorem take_formulaTag3 (f : Formula) (mid rest : Bitstring) :
    List.take 3 (formulaTag f ++ mid ++ rest) = formulaTag f :=
  take_prefix3 (formulaTag f) mid rest (len_formulaTag f)

private theorem take_serializeTerm_prefix3 (t : Term) (rest : Bitstring) :
    List.take 3 (serializeTerm t ++ rest) = termTag t := by
  cases t with
  | var n => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | empty => simp [serializeTerm, termTag, take_prefix3, len_termTag]
  | union t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | inter t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | diff t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]

private theorem take_serializeRelation_prefix2 (r : Relation) (rest : Bitstring) :
    List.take 2 (serializeRelation r ++ rest) = relationTag r := by
  cases r with
  | mem t1 t2 | not_mem t1 t2 | eq t1 t2 | neq t1 t2 =>
    simp [serializeRelation, relationTag, take_prefix2, len_relationTag, List.append_assoc]

private theorem take_serializeFormula_prefix3 (f : Formula) (rest : Bitstring) :
    List.take 3 (serializeFormula f ++ rest) = formulaTag f := by
  cases f with
  | rel r => simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]
  | not f => simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]
  | and f1 f2 | or f1 f2 | imp f1 f2 | iff f1 f2 =>
    simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]

private theorem drop3_termTag_append (tag mid rest : Bitstring) (h : len tag = 3) :
    (tag ++ mid ++ rest).drop 3 = mid ++ rest := by
  rw [len_eq] at h
  simp [List.drop_append, h, List.append_assoc]

private theorem drop3_serializeTerm (t : Term) (rest : Bitstring) :
    (serializeTerm t ++ rest).drop 3 =
      match t with
      | .var n => encodeNat n ++ rest
      | .empty => rest
      | .union t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest
      | .inter t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest
      | .diff t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest := by
  cases t <;> simp [serializeTerm, termTag, drop3_termTag_append, len_termTag, List.append_assoc]

private theorem drop2_relationTag_append (tag mid rest : Bitstring) (h : len tag = 2) :
    (tag ++ mid ++ rest).drop 2 = mid ++ rest := by
  rw [len_eq] at h
  simp [List.drop_append, h, List.append_assoc]

private theorem drop2_serializeRelation (r : Relation) (rest : Bitstring) :
    (serializeRelation r ++ rest).drop 2 =
      match r with
      | .mem t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest
      | .not_mem t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest
      | .eq t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest
      | .neq t1 t2 => serializeTerm t1 ++ serializeTerm t2 ++ rest := by
  cases r <;> simp [serializeRelation, relationTag, drop2_relationTag_append, len_relationTag,
    List.append_assoc]

private theorem drop3_formulaTag_append (tag mid rest : Bitstring) (h : len tag = 3) :
    (tag ++ mid ++ rest).drop 3 = mid ++ rest := by
  rw [len_eq] at h
  simp [List.drop_append, h, List.append_assoc]

private theorem drop3_serializeFormula (f : Formula) (rest : Bitstring) :
    (serializeFormula f ++ rest).drop 3 =
      match f with
      | .rel r => serializeRelation r ++ rest
      | .not f => serializeFormula f ++ rest
      | .and f1 f2 => serializeFormula f1 ++ serializeFormula f2 ++ rest
      | .or f1 f2 => serializeFormula f1 ++ serializeFormula f2 ++ rest
      | .imp f1 f2 => serializeFormula f1 ++ serializeFormula f2 ++ rest
      | .iff f1 f2 => serializeFormula f1 ++ serializeFormula f2 ++ rest := by
  cases f <;> simp [serializeFormula, formulaTag, drop3_formulaTag_append, len_formulaTag,
    List.append_assoc]

theorem decodeTermFuel_suffix (fuel : Nat) (t : Term) (rest : Bitstring)
    (h : wireSizeTerm t + rest.length <= fuel) :
    decodeTermFuel fuel (serializeTerm t ++ rest) = some (t, rest) := by
  induction t generalizing rest fuel with
  | var n =>
    have hlen : 3 <= (serializeTerm (.var n) ++ rest).length := by
      simp [wireSizeTerm, length_serializeTerm, wireSizeNat, length_encodeNat]
      omega
    cases fuel with
    | zero => simp [wireSizeTerm] at h
    | succ fuel =>
      simp [decodeTermFuel, serializeTerm, termTag, drop3_serializeTerm, hlen]
      rw [decodeNat?_suffix n rest]
  | empty =>
    have hlen : 3 <= (serializeTerm .empty ++ rest).length := by
      simp [wireSizeTerm, length_serializeTerm]
    cases fuel with
    | zero => simp [wireSizeTerm] at h
    | succ fuel =>
      simp [decodeTermFuel, serializeTerm, termTag, drop3_serializeTerm, hlen]
  | union t1 t2 ih1 ih2 =>
    have hlen : 3 <= (serializeTerm (.union t1 t2) ++ rest).length := by
      simp [wireSizeTerm, length_serializeTerm]
      have := wireSizeTerm_pos t1
      omega
    cases fuel with
    | zero => simp [wireSizeTerm] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeTermFuel, serializeTerm, termTag, drop3_serializeTerm, hlen]
      rw [ih1 fuel (serializeTerm t2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]
  | inter t1 t2 ih1 ih2 =>
    have hlen : 3 <= (serializeTerm (.inter t1 t2) ++ rest).length := by
      simp [wireSizeTerm, length_serializeTerm]
      have := wireSizeTerm_pos t1
      omega
    cases fuel with
    | zero => simp [wireSizeTerm] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeTermFuel, serializeTerm, termTag, drop3_serializeTerm, hlen]
      rw [ih1 fuel (serializeTerm t2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]
  | diff t1 t2 ih1 ih2 =>
    have hlen : 3 <= (serializeTerm (.diff t1 t2) ++ rest).length := by
      simp [wireSizeTerm, length_serializeTerm]
      have := wireSizeTerm_pos t1
      omega
    cases fuel with
    | zero => simp [wireSizeTerm] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeTerm, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeTermFuel, serializeTerm, termTag, drop3_serializeTerm, hlen]
      rw [ih1 fuel (serializeTerm t2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]

theorem decodeTerm?_suffix (t : Term) (rest : Bitstring) :
    decodeTerm? (serializeTerm t ++ rest) = some (t, rest) := by
  simp [decodeTerm?, length_serializeTerm]
  exact decodeTermFuel_suffix (wireSizeTerm t + rest.length) t rest le_rfl

theorem decodeTerm?_serializeTerm (t : Term) :
    decodeTerm? (serializeTerm t) = some (t, []) := by
  simpa [List.append_nil] using decodeTerm?_suffix t []

theorem decodeRelationFuel_suffix (fuel : Nat) (r : Relation) (rest : Bitstring)
    (h : wireSizeRelation r + rest.length <= fuel) :
    decodeRelationFuel fuel (serializeRelation r ++ rest) = some (r, rest) := by
  cases r with
  | mem t1 t2 =>
    have hlen : 2 <= (serializeRelation (.mem t1 t2) ++ rest).length := by
      simp [wireSizeRelation, length_serializeRelation, wireSizeTerm, wireSizeNat]
      have := wireSizeTerm_pos t1; omega
    cases fuel with
    | zero => simp [wireSizeRelation] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeRelationFuel, serializeRelation, relationTag, drop2_serializeRelation, hlen]
      rw [decodeTermFuel_suffix fuel t1 (serializeTerm t2 ++ rest) hf1]
      simp
      rw [decodeTermFuel_suffix fuel t2 rest hf2]
  | not_mem t1 t2 =>
    have hlen : 2 <= (serializeRelation (.not_mem t1 t2) ++ rest).length := by
      simp [wireSizeRelation, length_serializeRelation, wireSizeTerm, wireSizeNat]
      have := wireSizeTerm_pos t1; omega
    cases fuel with
    | zero => simp [wireSizeRelation] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeRelationFuel, serializeRelation, relationTag, drop2_serializeRelation, hlen]
      rw [decodeTermFuel_suffix fuel t1 (serializeTerm t2 ++ rest) hf1]
      simp
      rw [decodeTermFuel_suffix fuel t2 rest hf2]
  | eq t1 t2 =>
    have hlen : 2 <= (serializeRelation (.eq t1 t2) ++ rest).length := by
      simp [wireSizeRelation, length_serializeRelation, wireSizeTerm, wireSizeNat]
      have := wireSizeTerm_pos t1; omega
    cases fuel with
    | zero => simp [wireSizeRelation] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeRelationFuel, serializeRelation, relationTag, drop2_serializeRelation, hlen]
      rw [decodeTermFuel_suffix fuel t1 (serializeTerm t2 ++ rest) hf1]
      simp
      rw [decodeTermFuel_suffix fuel t2 rest hf2]
  | neq t1 t2 =>
    have hlen : 2 <= (serializeRelation (.neq t1 t2) ++ rest).length := by
      simp [wireSizeRelation, length_serializeRelation, wireSizeTerm, wireSizeNat]
      have := wireSizeTerm_pos t1; omega
    cases fuel with
    | zero => simp [wireSizeRelation] at h
    | succ fuel =>
      have hf1 : wireSizeTerm t1 + (serializeTerm t2 ++ rest).length <= fuel := by
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      have hf2 : wireSizeTerm t2 + rest.length <= fuel := by
        have h1 := wireSizeTerm_pos t1
        simp [wireSizeRelation, length_serializeTerm, List.length_append] at h |-; omega
      simp [decodeRelationFuel, serializeRelation, relationTag, drop2_serializeRelation, hlen]
      rw [decodeTermFuel_suffix fuel t1 (serializeTerm t2 ++ rest) hf1]
      simp
      rw [decodeTermFuel_suffix fuel t2 rest hf2]

theorem decodeRelation?_suffix (r : Relation) (rest : Bitstring) :
    decodeRelation? (serializeRelation r ++ rest) = some (r, rest) := by
  simp [decodeRelation?, length_serializeRelation]
  exact decodeRelationFuel_suffix (wireSizeRelation r + rest.length) r rest le_rfl

theorem decodeRelation?_serializeRelation (r : Relation) :
    decodeRelation? (serializeRelation r) = some (r, []) := by
  simpa [List.append_nil] using decodeRelation?_suffix r []

theorem decodeFormulaFuel_suffix (fuel : Nat) (f : Formula) (rest : Bitstring)
    (h : wireSizeFormula f + rest.length <= fuel) :
    decodeFormulaFuel fuel (serializeFormula f ++ rest) = some (f, rest) := by
  induction f generalizing rest fuel with
  | rel r =>
    have hlen : 3 <= (serializeFormula (.rel r) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula, wireSizeRelation]
      cases r with
      | mem t1 _ | not_mem t1 _ | eq t1 _ | neq t1 _ =>
        have := wireSizeTerm_pos t1; omega
    cases fuel with
    | zero => simp [wireSizeFormula, wireSizeRelation] at h
    | succ fuel =>
      have hrel : wireSizeRelation r + rest.length <= fuel := by
        simp [wireSizeFormula, wireSizeRelation] at h |-; omega
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [decodeRelationFuel_suffix fuel r rest hrel]
  | not f ih =>
    have hlen : 3 <= (serializeFormula (.not f) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula]
      have := formulaSize_pos f; omega
    cases fuel with
    | zero => simp [wireSizeFormula] at h
    | succ fuel =>
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [ih fuel rest (by simp [wireSizeFormula] at h |-; omega)]
  | and f1 f2 ih1 ih2 =>
    have hlen : 3 <= (serializeFormula (f1.and f2) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula]
      have := formulaSize_pos f1; omega
    cases fuel with
    | zero => simp [wireSizeFormula] at h
    | succ fuel =>
      have hf1 : wireSizeFormula f1 + (serializeFormula f2 ++ rest).length <= fuel := by
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      have hf2 : wireSizeFormula f2 + rest.length <= fuel := by
        have h1 := formulaSize_pos f1
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [ih1 fuel (serializeFormula f2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]
  | or f1 f2 ih1 ih2 =>
    have hlen : 3 <= (serializeFormula (f1.or f2) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula]
      have := formulaSize_pos f1; omega
    cases fuel with
    | zero => simp [wireSizeFormula] at h
    | succ fuel =>
      have hf1 : wireSizeFormula f1 + (serializeFormula f2 ++ rest).length <= fuel := by
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      have hf2 : wireSizeFormula f2 + rest.length <= fuel := by
        have h1 := formulaSize_pos f1
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [ih1 fuel (serializeFormula f2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]
  | imp f1 f2 ih1 ih2 =>
    have hlen : 3 <= (serializeFormula (f1.imp f2) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula]
      have := formulaSize_pos f1; omega
    cases fuel with
    | zero => simp [wireSizeFormula] at h
    | succ fuel =>
      have hf1 : wireSizeFormula f1 + (serializeFormula f2 ++ rest).length <= fuel := by
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      have hf2 : wireSizeFormula f2 + rest.length <= fuel := by
        have h1 := formulaSize_pos f1
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [ih1 fuel (serializeFormula f2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]
  | iff f1 f2 ih1 ih2 =>
    have hlen : 3 <= (serializeFormula (f1.iff f2) ++ rest).length := by
      simp [wireSizeFormula, length_serializeFormula]
      have := formulaSize_pos f1; omega
    cases fuel with
    | zero => simp [wireSizeFormula] at h
    | succ fuel =>
      have hf1 : wireSizeFormula f1 + (serializeFormula f2 ++ rest).length <= fuel := by
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      have hf2 : wireSizeFormula f2 + rest.length <= fuel := by
        have h1 := formulaSize_pos f1
        simp [wireSizeFormula, length_serializeFormula, List.length_append] at h |-; omega
      simp [decodeFormulaFuel, serializeFormula, formulaTag, drop3_serializeFormula, hlen]
      rw [ih1 fuel (serializeFormula f2 ++ rest) hf1]
      simp
      rw [ih2 fuel rest hf2]

theorem decodeFormula?_suffix (f : Formula) (rest : Bitstring) :
    decodeFormula? (serializeFormula f ++ rest) = some (f, rest) := by
  simp [decodeFormula?, length_serializeFormula]
  exact decodeFormulaFuel_suffix (wireSizeFormula f + rest.length) f rest le_rfl

theorem decodeFormula?_serializeFormula (f : Formula) :
    decodeFormula? (serializeFormula f) = some (f, []) := by
  simpa [List.append_nil] using decodeFormula?_suffix f []

end MLS
