/-
Runnable snippet for arxiv.md, displayed with the three SAT reductions.

All three are stated in the same four-part form -- correctness, injectivity, an
explicit left inverse, and an exact size identity -- which is precisely the
hypothesis package that the repaired Theorem 4.4 consumes.  Stating them
uniformly is what makes them composable with the transfer theorem.

Note on the second one: the bare semantic core is *not* injective, because the
complement gadget for a literal ignores its polarity.  Tagging the output with
a provenance prefix that encodes the source bits repairs this, which is why
`toEMLS` rather than `semanticCore` is the reduction of record.

Checked against AvgCaseMls.MLSInReduction, AvgCaseMls.EMLSReduction, and
AvgCaseMls.FPILP.
-/
import AvgCaseMls.MLSInReduction
import AvgCaseMls.EMLSReduction
import AvgCaseMls.FPILP

namespace Exposition.Reductions

open MLS

/-! ## SAT to the membership fragment of MLS

A distinguished variable `x` plays the role of an element; propositional
variable `i` becomes the set variable `i+1`.  A positive literal becomes
`x ∈ s(i)`, a negative one `x ∉ s(i)`.  The empty clause becomes `x ∈ x` and
the empty formula `x ∉ x`, both decided by foundation, since the fragment has
no equality atoms available. -/

theorem reduction_5_1 :
    (∀ φ : SAT.CNF,
        SAT.Satisfiable φ ↔ MLSInReduction.MLSSatisfiable (MLSInReduction.toMLS φ)) ∧
    Function.Injective MLSInReduction.toMLS ∧
    (∀ φ : SAT.CNF, MLSInReduction.fromMLS (MLSInReduction.toMLS φ) = some φ) ∧
    (∀ φ : SAT.CNF, MLSInReduction.IsMLSIn (MLSInReduction.toMLS φ)) ∧
    ∀ φ : SAT.CNF,
      formulaNodes (MLSInReduction.toMLS φ) + 1 = 5 * SAT.size φ :=
  ⟨MLSInReduction.satisfiable_iff,
   MLSInReduction.toMLS_injective,
   MLSInReduction.fromMLS_toMLS,
   MLSInReduction.toMLS_isMLSIn,
   MLSInReduction.formulaNodes_toMLS⟩

/-! ## SAT to EMLS

Each propositional variable `i` gets a positive set, a negative set, and a
gadget forcing their intersection empty, so no variable is both true and false.
Each clause is turned into a chain of union gadgets accumulating the sets of
its literals, and the distinguished element is forced into that union, so the
clause holds exactly when one of its literals is true. -/

theorem reduction_5_2 :
    (∀ φ : SAT.CNF,
        SAT.Satisfiable φ ↔
          EMLSReduction.EMLSSatisfiable (EMLSReduction.toEMLS φ)) ∧
    Function.Injective EMLSReduction.toEMLS ∧
    (∀ φ : SAT.CNF, EMLSReduction.fromEMLS (EMLSReduction.toEMLS φ) = some φ) ∧
    ∀ φ : SAT.CNF,
      (EMLSReduction.toEMLS φ).length =
        (EMLSReduction.sourceBits φ).length + 2 +
          3 * EMLSReduction.literalCount φ + φ.length :=
  ⟨EMLSReduction.toEMLS_satisfiable_iff,
   EMLSReduction.toEMLS_injective,
   EMLSReduction.fromEMLS_toEMLS,
   EMLSReduction.toEMLS_length⟩

/-! ## SAT to feasibility of integer linear programs

Variables are pinned to `{0,1}` by the pair of inequalities `xᵢ ≥ 0` and
`1 - xᵢ ≥ 0`.  A clause becomes `∑ terms ≥ 1`, where a positive literal
contributes `xᵢ` and a negative one `1 - xᵢ`, so the clause is satisfied
exactly when some term equals `1`. -/

theorem reduction_5_3 :
    (∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
        φ.Satisfiable ↔ (TR1995.FPILPSource.satToFPILP φ).Feasible) ∧
    (∀ {n : Nat}, Function.Injective (@TR1995.FPILPSource.satToFPILP n)) ∧
    ∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
      (TR1995.FPILPSource.satToFPILP φ).constraints.length = 2 * n + φ.length :=
  ⟨fun φ => (TR1995.FPILPSource.satToFPILP_feasible_iff φ).symm,
   @TR1995.FPILPSource.satToFPILP_injective,
   TR1995.FPILPSource.satToFPILP_constraint_count⟩

end Exposition.Reductions
