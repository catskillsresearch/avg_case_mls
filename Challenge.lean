import Mathlib

/-!
# TR1995-711: explicit statement of record

This Mathlib-only file records the six paper-numbered/core results selected for
Palomar: Theorems 4.1 and 4.4, Example 4.1, and the constructive cores of
Theorems 5.1--5.3. Every notion occurring in those statements is defined
concretely below. The only `sorry`s are the six theorem proof holes required by
the Challenge/Solution protocol.
-/

namespace AvCom

abbrev Bitstring := List Bool

def len (s : Bitstring) : Nat := s.length

def lenBot (s : Bitstring) : Nat := max 1 s.length

structure Distribution where
  support : Finset Bitstring
  prob : Bitstring → Real
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_zero_outside : ∀ s, s ∉ support → prob s = 0
  prob_sum_le_one : support.sum prob ≤ 1

structure DistributionalProblem where
  L : Set Bitstring
  μ : Distribution

def IsPolynomial (T : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n, T n ≤ c * n ^ k + c

noncomputable def rank (μ : Distribution) (x : Bitstring) : Nat :=
  if μ.prob x = 0 then 0
  else
    open Classical in
    (μ.support.filter (fun z => μ.prob x ≤ μ.prob z)).card

def IsTRankable (V : Nat → Nat) (μ : Distribution) : Prop :=
  ∀ x, rank μ x ≤ V (len x)

def IsPolRankable (μ : Distribution) : Prop :=
  ∃ V : Nat → Nat, IsPolynomial V ∧ IsTRankable V μ

def InNP (L : Set Bitstring) : Prop :=
  ∃ (verify : Bitstring → Bitstring → Bool) (bound : Nat → Nat),
    IsPolynomial bound ∧
    ∀ x, x ∈ L ↔ ∃ cert, len cert ≤ bound (len x) ∧ verify x cert = true

def InDistNP (prob : DistributionalProblem) : Prop :=
  InNP prob.L ∧ IsPolRankable prob.μ

def DistributionalReduction (source target : DistributionalProblem) : Prop :=
  ∃ f : Bitstring → Bitstring,
    (∀ x, x ∈ source.L ↔ f x ∈ target.L) ∧
    (∃ k0 k1 : Nat, ∀ x, lenBot (f x) ≤ k0 * lenBot x ^ k1) ∧
    ∃ c0 c1 : Nat, 0 < c0 ∧ 0 < c1 ∧
      ∀ x, rank target.μ (f x) ≤ c0 * lenBot x ^ c1 * rank source.μ x

def IsNPAverageComplete (target : DistributionalProblem) : Prop :=
  InDistNP target ∧
    ∀ source, InDistNP source → DistributionalReduction source target

end AvCom

namespace TR1995

open AvCom

def IsNPAverageCompleteLanguage (L : Set Bitstring) : Prop :=
  InNP L ∧
    ∀ source : DistributionalProblem, InDistNP source →
      ∃ μ : Distribution,
        IsPolRankable μ ∧ DistributionalReduction source ⟨L, μ⟩

noncomputable def example41Exponent (ε : ℝ) : ℝ :=
  -3 + 2 / (1 + ε)

noncomputable def example41Contribution (ε : ℝ) (n : Nat) : ℝ :=
  (6 / Real.pi ^ 2) * (n : ℝ) ^ example41Exponent ε

end TR1995

namespace HonestReduction

open AvCom

structure FaithfulReduction (L₁ L₂ : Set Bitstring) where
  map : Bitstring → Bitstring
  inverse : Bitstring → Bitstring
  inRange : Bitstring → Bool
  reduces : ∀ x, x ∈ L₁ ↔ map x ∈ L₂
  injective : Function.Injective map
  leftInverse : Function.LeftInverse inverse map
  recognizesRange : ∀ y, inRange y = true ↔ ∃ x, map x = y
  forwardLength :
    ∃ c k : Nat, ∀ x, lenBot (map x) ≤ c * lenBot x ^ k
  honest :
    ∃ c k : Nat, ∀ x, lenBot x ≤ c * lenBot (map x) ^ k

end HonestReduction

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
  | .neg i => ¬a i

def evalClause (a : Assignment) (c : Clause) : Prop :=
  ∃ l ∈ c, evalLiteral a l

def evalCNF (a : Assignment) (φ : CNF) : Prop :=
  ∀ c ∈ φ, evalClause a c

def Satisfiable (φ : CNF) : Prop :=
  ∃ a, evalCNF a φ

def size (φ : CNF) : Nat :=
  1 + φ.length + (φ.map List.length).sum

end SAT

namespace MLS

inductive Term : Type
  | var : Nat → Term
  | empty : Term
  | union : Term → Term → Term
  | inter : Term → Term → Term
  | diff : Term → Term → Term
  deriving DecidableEq, Repr

inductive Relation : Type
  | mem : Term → Term → Relation
  | not_mem : Term → Term → Relation
  | eq : Term → Term → Relation
  | neq : Term → Term → Relation
  deriving DecidableEq, Repr

inductive Formula : Type
  | rel : Relation → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | iff : Formula → Formula → Formula
  deriving DecidableEq, Repr

abbrev ZFSet := _root_.ZFSet.{0}

namespace ZFSet

def empty : ZFSet := ∅
def union (x y : ZFSet) : ZFSet := x ∪ y
def inter (x y : ZFSet) : ZFSet := x ∩ y
def diff (x y : ZFSet) : ZFSet := x \ y
def mem (x y : ZFSet) : Prop := x ∈ y

end ZFSet

def Env : Type 1 := Nat → ZFSet

noncomputable def evalTerm (env : Env) : Term → ZFSet
  | .var n => env n
  | .empty => ZFSet.empty
  | .union t₁ t₂ => ZFSet.union (evalTerm env t₁) (evalTerm env t₂)
  | .inter t₁ t₂ => ZFSet.inter (evalTerm env t₁) (evalTerm env t₂)
  | .diff t₁ t₂ => ZFSet.diff (evalTerm env t₁) (evalTerm env t₂)

noncomputable def evalFormula (env : Env) : Formula → Prop
  | .rel (.mem t₁ t₂) => ZFSet.mem (evalTerm env t₁) (evalTerm env t₂)
  | .rel (.not_mem t₁ t₂) => ¬ZFSet.mem (evalTerm env t₁) (evalTerm env t₂)
  | .rel (.eq t₁ t₂) => evalTerm env t₁ = evalTerm env t₂
  | .rel (.neq t₁ t₂) => evalTerm env t₁ ≠ evalTerm env t₂
  | .not f => ¬evalFormula env f
  | .and f₁ f₂ => evalFormula env f₁ ∧ evalFormula env f₂
  | .or f₁ f₂ => evalFormula env f₁ ∨ evalFormula env f₂
  | .imp f₁ f₂ => evalFormula env f₁ → evalFormula env f₂
  | .iff f₁ f₂ => evalFormula env f₁ ↔ evalFormula env f₂

def termNodes : Term → Nat
  | .var _ => 1
  | .empty => 1
  | .union t₁ t₂ => 1 + termNodes t₁ + termNodes t₂
  | .inter t₁ t₂ => 1 + termNodes t₁ + termNodes t₂
  | .diff t₁ t₂ => 1 + termNodes t₁ + termNodes t₂

def relationNodes : Relation → Nat
  | .mem t₁ t₂ => 1 + termNodes t₁ + termNodes t₂
  | .not_mem t₁ t₂ => 1 + termNodes t₁ + termNodes t₂
  | .eq t₁ t₂ => 1 + termNodes t₁ + termNodes t₂
  | .neq t₁ t₂ => 1 + termNodes t₁ + termNodes t₂

def formulaNodes : Formula → Nat
  | .rel r => 1 + relationNodes r
  | .not f => 1 + formulaNodes f
  | .and f₁ f₂ => 1 + formulaNodes f₁ + formulaNodes f₂
  | .or f₁ f₂ => 1 + formulaNodes f₁ + formulaNodes f₂
  | .imp f₁ f₂ => 1 + formulaNodes f₁ + formulaNodes f₂
  | .iff f₁ f₂ => 1 + formulaNodes f₁ + formulaNodes f₂

namespace EMLS

inductive BinOp
  | union
  | inter
  | diff
  deriving DecidableEq, Repr

inductive Literal
  | eqOp : Nat → Nat → Nat → BinOp → Literal
  | eqEmpty : Nat → Literal
  | mem : Nat → Nat → Literal
  | notMem : Nat → Nat → Literal
  | neq : Nat → Nat → Literal
  deriving DecidableEq, Repr

abbrev Conjunct := List Literal

def binOpToTerm (op : BinOp) (y z : Nat) : Term :=
  match op with
  | .union => .union (.var y) (.var z)
  | .inter => .inter (.var y) (.var z)
  | .diff => .diff (.var y) (.var z)

noncomputable def Literal.holds (env : Env) : Literal → Prop
  | .eqOp x y z op => evalTerm env (.var x) = evalTerm env (binOpToTerm op y z)
  | .eqEmpty x => evalTerm env (.var x) = evalTerm env .empty
  | .mem x y => ZFSet.mem (evalTerm env (.var x)) (evalTerm env (.var y))
  | .notMem x y => ¬ZFSet.mem (evalTerm env (.var x)) (evalTerm env (.var y))
  | .neq x y => evalTerm env (.var x) ≠ evalTerm env (.var y)

end EMLS

end MLS

namespace Example41

open AvCom

noncomputable def standardMass (x : List Bool) : ℝ :=
  if x.isEmpty then 0
  else (6 / Real.pi ^ 2) * (x.length : ℝ) ^ (-2 : ℝ) / (2 : ℝ) ^ x.length

abbrev Shell (n : ℕ) := Fin n → Bool

def Shell.toList {n : ℕ} (x : Shell n) : List Bool :=
  List.ofFn x

noncomputable def shellMass (n : ℕ) : ℝ :=
  ∑ x : Shell n, standardMass x.toList

def quadraticTime (x : List Bool) : ℕ :=
  x.length ^ 2

noncomputable def inversePower (ε : ℝ) (t : ℕ) : ℝ :=
  (t : ℝ) ^ (1 / (1 + ε) : ℝ)

noncomputable def levinTerm (ε : ℝ) (x : List Bool) : ℝ :=
  standardMass x * inversePower ε (quadraticTime x) / (lenBot x : ℝ)

noncomputable def shellLevin (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Shell n, levinTerm ε x.toList

noncomputable def levinShellSeries (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else shellLevin ε n

end Example41

namespace MLSInReduction

open MLS

def distinguishedTerm : Term := .var 0
def setTerm (i : Nat) : Term := .var (Nat.succ i)

def literalToMLS : SAT.Literal → Formula
  | .pos i => .rel (.mem distinguishedTerm (setTerm i))
  | .neg i => .rel (.not_mem distinguishedTerm (setTerm i))

def falseFormula : Formula := .rel (.mem distinguishedTerm distinguishedTerm)
def trueFormula : Formula := .rel (.eq distinguishedTerm distinguishedTerm)

def clauseToMLS : SAT.Clause → Formula
  | [] => falseFormula
  | l :: c => .or (literalToMLS l) (clauseToMLS c)

def toMLS : SAT.CNF → Formula
  | [] => trueFormula
  | c :: φ => .and (clauseToMLS c) (toMLS φ)

def MLSSatisfiable (f : Formula) : Prop :=
  ∃ env, evalFormula env f

end MLSInReduction

namespace EMLSReduction

open MLS MLS.EMLS

abbrev Satisfies (env : Env) (c : Conjunct) : Prop :=
  ∀ lit ∈ c, Literal.holds env lit

def EMLSSatisfiable (c : Conjunct) : Prop :=
  ∃ env, Satisfies env c

def distinguishedVar : Nat := 0
def emptyVar : Nat := 3
def positiveVar (i : Nat) : Nat := 4 * i + 1
def negativeVar (i : Nat) : Nat := 4 * i + 2
def intersectionVar (i : Nat) : Nat := 4 * i + 7

private def literalEquiv : SAT.Literal ≃ Sum Nat Nat where
  toFun
    | .pos i => .inl i
    | .neg i => .inr i
  invFun
    | .inl i => .pos i
    | .inr i => .neg i
  left_inv l := by cases l <;> rfl
  right_inv l := by cases l <;> rfl

private local instance : Encodable SAT.Literal :=
  Encodable.ofEquiv (Sum Nat Nat) literalEquiv

def gadgetVar (k : Nat) (c : SAT.Clause) : Nat :=
  4 * (Nat.pair k (Encodable.encode c) + 1)

def literalVar : SAT.Literal → Nat
  | .pos i => positiveVar i
  | .neg i => negativeVar i

def complementGadget (i : Nat) : Conjunct :=
  [.eqOp (intersectionVar i) (positiveVar i) (negativeVar i) .inter,
   .eqEmpty (intersectionVar i)]

def literalComplementGadget : SAT.Literal → Conjunct
  | .pos i => complementGadget i
  | .neg i => complementGadget i

def clauseGadgets (k : Nat) : SAT.Clause → Conjunct
  | [] => []
  | l :: [] => [.eqOp (gadgetVar k [l]) (literalVar l) emptyVar .union]
  | l :: rest@(_ :: _) =>
      .eqOp (gadgetVar k (l :: rest)) (literalVar l) (gadgetVar k rest) .union ::
        clauseGadgets k rest

def clauseCore (k : Nat) : SAT.Clause → Conjunct
  | [] => [.mem distinguishedVar distinguishedVar]
  | c@(_ :: _) => clauseGadgets k c ++ [.mem distinguishedVar (gadgetVar k c)]

def clausesCoreFrom : Nat → SAT.CNF → Conjunct
  | _, [] => []
  | k, c :: φ => clauseCore k c ++ clausesCoreFrom (k + 1) φ

def complementCore (φ : SAT.CNF) : Conjunct :=
  φ.flatMap fun c => c.flatMap literalComplementGadget

def semanticCore (φ : SAT.CNF) : Conjunct :=
  .eqEmpty emptyVar :: (complementCore φ ++ clausesCoreFrom 0 φ)

def provenanceTag (φ : SAT.CNF) : Literal :=
  let n := Encodable.encode φ
  .eqOp n n n .union

def toEMLS (φ : SAT.CNF) : Conjunct :=
  provenanceTag φ :: semanticCore φ

end EMLSReduction

namespace TR1995.FPILPSource

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

inductive Term (n : Nat) where
  | var : Fin n → Term n
  | oneMinus : Fin n → Term n
  deriving DecidableEq, Repr

def Term.eval {n : Nat} (x : Fin n → Int) : Term n → Int
  | .var i => x i
  | .oneMinus i => 1 - x i

structure Inequality (n : Nat) where
  lhs : List (Term n)
  rhs : Int
  deriving DecidableEq, Repr

def Inequality.Holds {n : Nat} (x : Fin n → Int) (q : Inequality n) : Prop :=
  q.rhs ≤ (q.lhs.map (Term.eval x)).sum

structure FPILP (n : Nat) where
  constraints : List (Inequality n)
  deriving DecidableEq, Repr

def FPILP.Feasible {n : Nat} (p : FPILP n) : Prop :=
  ∃ x : Fin n → Int, ∀ q ∈ p.constraints, q.Holds x

def lowerBound {n : Nat} (i : Fin n) : Inequality n := ⟨[.var i], 0⟩
def upperBound {n : Nat} (i : Fin n) : Inequality n := ⟨[.oneMinus i], 0⟩

def bounds (n : Nat) : List (Inequality n) :=
  (List.finRange n).flatMap fun i => [lowerBound i, upperBound i]

def Literal.toTerm {n : Nat} : Literal n → Term n
  | .pos i => .var i
  | .neg i => .oneMinus i

def clauseInequality {n : Nat} (c : Clause n) : Inequality n :=
  ⟨c.map Literal.toTerm, 1⟩

def satToFPILP {n : Nat} (φ : CNF n) : FPILP n :=
  ⟨bounds n ++ φ.map clauseInequality⟩

end TR1995.FPILPSource

namespace AvgCasePalomar

open AvCom MLS EMLS

theorem paper_theorem_4_1 :
    ∀ {L : Set Bitstring} {ρ : Distribution},
      IsNPAverageComplete ⟨L, ρ⟩ → TR1995.IsNPAverageCompleteLanguage L := by
  sorry

theorem paper_theorem_4_4 :
    ∀ {L₁ L₂ : Set Bitstring},
      HonestReduction.FaithfulReduction L₁ L₂ →
      TR1995.IsNPAverageCompleteLanguage L₁ →
      InNP L₂ →
      TR1995.IsNPAverageCompleteLanguage L₂ := by
  sorry

theorem paper_example_4_1 :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        Summable (Example41.levinShellSeries ε) ∧
        (∑' n : Nat, Example41.levinShellSeries ε n / C) ≤ 1 := by
  sorry

theorem paper_theorem_5_1_reduction_core :
    (∀ φ : SAT.CNF,
        SAT.Satisfiable φ ↔ MLSInReduction.MLSSatisfiable (MLSInReduction.toMLS φ)) ∧
    Function.Injective MLSInReduction.toMLS ∧
    ∀ φ : SAT.CNF,
      formulaNodes (MLSInReduction.toMLS φ) + 1 = 5 * SAT.size φ := by
  sorry

theorem paper_theorem_5_2_reduction_core :
    (∀ φ : SAT.CNF,
        SAT.Satisfiable φ ↔
          EMLSReduction.EMLSSatisfiable (EMLSReduction.toEMLS φ)) ∧
    Function.Injective EMLSReduction.toEMLS ∧
    ∀ φ : SAT.CNF,
      (EMLSReduction.toEMLS φ).length ≤ 3 * SAT.size φ := by
  sorry

theorem paper_theorem_5_3_reduction_core :
    (∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
        φ.Satisfiable ↔ (TR1995.FPILPSource.satToFPILP φ).Feasible) ∧
    (∀ {n : Nat},
        Function.Injective (@TR1995.FPILPSource.satToFPILP n)) ∧
    ∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
      (TR1995.FPILPSource.satToFPILP φ).constraints.length =
        2 * n + φ.length := by
  sorry

end AvgCasePalomar
