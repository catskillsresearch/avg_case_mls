import AvgCaseMls.MLS
import AvgCaseMls.Foundation.Codec

/-!
# A binary, self-delimiting codec for full MLS

Unlike the historical serializer in `Serialization.lean`, variable names are
encoded with the shared binary natural-number codec.  Constructor tags are
prefix-free at each syntactic category.
-/

namespace AvgCaseMls.MLSCodec

open AvgCaseMls.Foundation
open MLS

def encodeTerm : Term → Bitstring
  | .var n => [false, false, false] ++ encodeNat n
  | .empty => [false, false, true]
  | .union x y => [false, true, false] ++ encodeTerm x ++ encodeTerm y
  | .inter x y => [false, true, true] ++ encodeTerm x ++ encodeTerm y
  | .diff x y => [true, false, false] ++ encodeTerm x ++ encodeTerm y

def encodeRelation : Relation → Bitstring
  | .mem x y => [false, false] ++ encodeTerm x ++ encodeTerm y
  | .not_mem x y => [false, true] ++ encodeTerm x ++ encodeTerm y
  | .eq x y => [true, false] ++ encodeTerm x ++ encodeTerm y
  | .neq x y => [true, true] ++ encodeTerm x ++ encodeTerm y

def encodeFormula : Formula → Bitstring
  | .rel r => [false, false, false] ++ encodeRelation r
  | .not f => [false, false, true] ++ encodeFormula f
  | .and f g => [false, true, false] ++ encodeFormula f ++ encodeFormula g
  | .or f g => [false, true, true] ++ encodeFormula f ++ encodeFormula g
  | .imp f g => [true, false, false] ++ encodeFormula f ++ encodeFormula g
  | .iff f g => [true, false, true] ++ encodeFormula f ++ encodeFormula g

def termFuel : Term → Nat
  | .var _ | .empty => 1
  | .union x y | .inter x y | .diff x y =>
      1 + max (termFuel x) (termFuel y)

def relationFuel : Relation → Nat
  | .mem x y | .not_mem x y | .eq x y | .neq x y =>
      1 + max (termFuel x) (termFuel y)

def formulaFuel : Formula → Nat
  | .rel r => 1 + relationFuel r
  | .not f => 1 + formulaFuel f
  | .and f g | .or f g | .imp f g | .iff f g =>
      1 + max (formulaFuel f) (formulaFuel g)

mutual
  def decodeTermFuel : Nat → Bitstring → Option (Term × Bitstring)
    | 0, _ => none
    | _ + 1, false :: false :: false :: bits => do
        let (n, rest) ← decodeNat? bits
        some (.var n, rest)
    | _ + 1, false :: false :: true :: rest => some (.empty, rest)
    | fuel + 1, false :: true :: false :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.union x y, rest)
    | fuel + 1, false :: true :: true :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.inter x y, rest)
    | fuel + 1, true :: false :: false :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.diff x y, rest)
    | _ + 1, _ => none

  def decodeRelationFuel : Nat → Bitstring → Option (Relation × Bitstring)
    | 0, _ => none
    | fuel + 1, false :: false :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.mem x y, rest)
    | fuel + 1, false :: true :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.not_mem x y, rest)
    | fuel + 1, true :: false :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.eq x y, rest)
    | fuel + 1, true :: true :: bits => do
        let (x, bits) ← decodeTermFuel fuel bits
        let (y, rest) ← decodeTermFuel fuel bits
        some (.neq x y, rest)
    | _ + 1, _ => none

  def decodeFormulaFuel : Nat → Bitstring → Option (Formula × Bitstring)
    | 0, _ => none
    | fuel + 1, false :: false :: false :: bits => do
        let (r, rest) ← decodeRelationFuel fuel bits
        some (.rel r, rest)
    | fuel + 1, false :: false :: true :: bits => do
        let (f, rest) ← decodeFormulaFuel fuel bits
        some (.not f, rest)
    | fuel + 1, false :: true :: false :: bits => do
        let (f, bits) ← decodeFormulaFuel fuel bits
        let (g, rest) ← decodeFormulaFuel fuel bits
        some (.and f g, rest)
    | fuel + 1, false :: true :: true :: bits => do
        let (f, bits) ← decodeFormulaFuel fuel bits
        let (g, rest) ← decodeFormulaFuel fuel bits
        some (.or f g, rest)
    | fuel + 1, true :: false :: false :: bits => do
        let (f, bits) ← decodeFormulaFuel fuel bits
        let (g, rest) ← decodeFormulaFuel fuel bits
        some (.imp f g, rest)
    | fuel + 1, true :: false :: true :: bits => do
        let (f, bits) ← decodeFormulaFuel fuel bits
        let (g, rest) ← decodeFormulaFuel fuel bits
        some (.iff f g, rest)
    | _ + 1, _ => none
end

theorem decodeTermFuel_suffix (t : Term) (rest : Bitstring) (fuel : Nat)
    (h : termFuel t ≤ fuel) :
    decodeTermFuel fuel (encodeTerm t ++ rest) = some (t, rest) := by
  induction t generalizing fuel rest with
  | var n =>
      cases fuel with
      | zero => simp [termFuel] at h
      | succ fuel => simp [encodeTerm, decodeTermFuel, decodeNat?_suffix]
  | empty =>
      cases fuel with
      | zero => simp [termFuel] at h
      | succ fuel => rfl
  | union x y ihx ihy | inter x y ihx ihy | diff x y ihx ihy =>
      cases fuel with
      | zero => simp [termFuel] at h
      | succ fuel =>
          have hx : termFuel x ≤ fuel := by
            simp [termFuel] at h
            omega
          have hy : termFuel y ≤ fuel := by
            simp [termFuel] at h
            omega
          simp [encodeTerm, decodeTermFuel,
            ihx (encodeTerm y ++ rest) fuel hx, ihy rest fuel hy,
            List.append_assoc]

theorem decodeRelationFuel_suffix (r : Relation) (rest : Bitstring) (fuel : Nat)
    (h : relationFuel r ≤ fuel) :
    decodeRelationFuel fuel (encodeRelation r ++ rest) = some (r, rest) := by
  cases r with
  | mem x y | not_mem x y | eq x y | neq x y =>
      cases fuel with
      | zero => simp [relationFuel] at h
      | succ fuel =>
          have hx : termFuel x ≤ fuel := by
            simp [relationFuel] at h
            omega
          have hy : termFuel y ≤ fuel := by
            simp [relationFuel] at h
            omega
          simp [encodeRelation, decodeRelationFuel,
            decodeTermFuel_suffix x (encodeTerm y ++ rest) fuel hx,
            decodeTermFuel_suffix y rest fuel hy, List.append_assoc]

theorem decodeFormulaFuel_suffix (f : Formula) (rest : Bitstring) (fuel : Nat)
    (h : formulaFuel f ≤ fuel) :
    decodeFormulaFuel fuel (encodeFormula f ++ rest) = some (f, rest) := by
  induction f generalizing fuel rest with
  | rel r =>
      cases fuel with
      | zero => simp [formulaFuel] at h
      | succ fuel =>
          have hr : relationFuel r ≤ fuel := by
            simp [formulaFuel] at h
            omega
          simp [encodeFormula, decodeFormulaFuel,
            decodeRelationFuel_suffix r rest fuel hr, List.append_assoc]
  | not f ih =>
      cases fuel with
      | zero => simp [formulaFuel] at h
      | succ fuel =>
          have hf : formulaFuel f ≤ fuel := by
            simp [formulaFuel] at h
            omega
          simp [encodeFormula, decodeFormulaFuel, ih rest fuel hf,
            List.append_assoc]
  | and f g ihf ihg | or f g ihf ihg | imp f g ihf ihg | iff f g ihf ihg =>
      cases fuel with
      | zero => simp [formulaFuel] at h
      | succ fuel =>
          have hf : formulaFuel f ≤ fuel := by
            simp [formulaFuel] at h
            omega
          have hg : formulaFuel g ≤ fuel := by
            simp [formulaFuel] at h
            omega
          simp [encodeFormula, decodeFormulaFuel,
            ihf (encodeFormula g ++ rest) fuel hf, ihg rest fuel hg,
            List.append_assoc]

theorem termFuel_le_encode_length (t : Term) :
    termFuel t ≤ (encodeTerm t).length := by
  induction t with
  | var n => simp [termFuel, encodeTerm]
  | empty => simp [termFuel, encodeTerm]
  | union x y ihx ihy | inter x y ihx ihy | diff x y ihx ihy =>
      simp [termFuel, encodeTerm] at ihx ihy ⊢
      omega

theorem relationFuel_le_encode_length (r : Relation) :
    relationFuel r ≤ (encodeRelation r).length := by
  cases r with
  | mem x y | not_mem x y | eq x y | neq x y =>
      have hx := termFuel_le_encode_length x
      have hy := termFuel_le_encode_length y
      simp [relationFuel, encodeRelation] at hx hy ⊢
      omega

theorem formulaFuel_le_encode_length (f : Formula) :
    formulaFuel f ≤ (encodeFormula f).length := by
  induction f with
  | rel r =>
      have hr := relationFuel_le_encode_length r
      simp [formulaFuel, encodeFormula] at hr ⊢
      omega
  | not f ih => simp [formulaFuel, encodeFormula] at ih ⊢; omega
  | and f g ihf ihg | or f g ihf ihg | imp f g ihf ihg | iff f g ihf ihg =>
      simp [formulaFuel, encodeFormula] at ihf ihg ⊢
      omega

def decodeFormula? (bits : Bitstring) : Option Formula := do
  let (formula, rest) ← decodeFormulaFuel bits.length bits
  if rest = [] then some formula else none

@[simp] theorem decodeFormula?_encode (f : Formula) :
    decodeFormula? (encodeFormula f) = some f := by
  unfold decodeFormula?
  have hdecode := decodeFormulaFuel_suffix f []
    (encodeFormula f).length (formulaFuel_le_encode_length f)
  simp only [List.append_nil] at hdecode
  rw [hdecode]
  rfl

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro f g h
  have := congrArg decodeFormula? h
  simpa using this

def EncodedMLSSAT : Set Bitstring :=
  {bits | ∃ formula, decodeFormula? bits = some formula ∧
    ∃ env : Env, evalFormula env formula}

@[simp] theorem encode_mem_encodedMLSSAT (formula : Formula) :
    encodeFormula formula ∈ EncodedMLSSAT ↔
      ∃ env : Env, evalFormula env formula := by
  constructor
  · rintro ⟨decoded, hdecode, hsatisfiable⟩
    rw [decodeFormula?_encode] at hdecode
    cases hdecode
    exact hsatisfiable
  · exact fun h => ⟨formula, decodeFormula?_encode formula, h⟩

end AvgCaseMls.MLSCodec
