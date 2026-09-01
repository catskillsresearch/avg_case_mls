# TR1995-711 to Lean claim audit

Source: Cox, Ericson, and Mishra, *The average case complexity of multilevel
syllogistic*, Courant Institute Technical Report CS-TR 711 (1995),
`TR1995-711.pdf`.

## Palomar outcome

The mechanical preflight passes for all six selected statements: Challenge and
Solution types match, the selected proof source has no `sorry`, and target
axiom audits use only `propext`, `Quot.sound`, and `Classical.choice`.

The full editorial audit returns **rejected**, specifically because these six
statements are routine infrastructure or weaker adapted closure results rather
than a substantive numbered theorem of TR1995-711. A registrable submission
requires an axiom-free proof of a result such as global decision completeness,
a faithful distributional reduction, or NP-average completeness. This cannot
be fixed by stronger prose or by selecting the existing axiomatized wrappers.

## Palomar-validated statements

| Report location | Lean statement | Validation boundary |
|---|---|---|
| §2.1, p. 5, model-graph contradiction checks | `AvgCasePalomar.step2_rejection` | Fully proved for the implemented `hasStep2Contradiction` test |
| §2.1, p. 5, MLS decision procedure | `AvgCasePalomar.sound_fragment_completeness` | A weaker adapted theorem, proved only on `InDecideSoundFormula`; it is not the report's global completeness claim |
| §5, pp. 15–18, encoded reductions | `AvgCasePalomar.formula_serialization_roundtrip` | Fully proved for the repository's own tagged-prefix formula codec, not a report-defined codec |
| §5, pp. 15–18, polynomial reduction sizes | `AvgCasePalomar.formula_encoding_polynomially_bounded` | Fully proved against `formulaAstMass`; it does not prove the report's SAT-to-MLS/EMLS/FPILP reduction bounds |
| §4.2, pp. 11–12, distributional reductions | `AvgCasePalomar.distributional_reduction_transitive` | Fully proved for a weaker Lean definition lacking injectivity and polynomial-time computability |
| Theorem 4.4, p. 14 | `AvgCasePalomar.average_completeness_transfers_along_reduction` | An analogous abstract closure lemma; it assumes the packaged weaker reduction and does not establish honesty, invertibility, or runtime |

These are checked Lean statements related to the cited report passages. They
are not presented as literal formalizations of any numbered report theorem.

## Material definition differences

- Report distributions range over all bitstrings; Lean distributions have
  finite support.
- Report rank counts strings with strictly greater probability; Lean uses
  greater-than-or-equal probability and assigns rank zero off support.
- `DistTime` is not linked to a decider or to the language component, and
  `InNP` does not constrain verifier runtime.
- Lean distributional reductions omit report requirements for injectivity and
  polynomial-time computation, replacing them with an output-length bound.
- The NBH scaffold has one canonical trivial machine and a singleton
  distribution rather than the report's family over bounded-halting inputs.

## Formalized but not independently validated as report theorems

- `Completeness.satMLSProb_NPAverageComplete` follows compositionally, but
  depends on `Completeness.distNP_reduces_to_nbh` and the axiomatized general
  NBH-to-MLS map and bounds.
- `NonAvP.SatMLS_average_hard` and its semantic/existential variants also
  depend on the named complexity-collapse and pullback axioms.
- `Reduction.nbhToSatMLS_red` packages the desired reduction interface, but
  the general compiler, correctness, length, and domination properties are
  axioms.
- `DistTime` is not connected to a language decider. Consequently `AvP.zero`
  makes every polynomially rankable distribution tractable, which conflicts
  with the separately axiomatized hardness chain. No theorem from that chain
  is selected by Palomar.

## Open or absent report claims

- Global `MLS.decideMLSSat_complete` retains one `sorry`; Steps 1 and complete
  Step 4 model search remain open.
- Theorems 3.1 and 3.2 (pp. 6–7), Example 4.1 (pp. 8–9), Theorem 4.1
  (p. 12), Theorem 4.2 (pp. 12–13), Theorem 4.3 (p. 14), and the report's
  padding construction are not faithfully proved.
- Theorem 5.1 (p. 15), Corollary 5.1 (p. 16), Corollary 5.2 (p. 16),
  Theorem 5.2 and Corollary 5.3 (pp. 16–17), Corollary 5.4 (p. 18),
  Theorem 5.3 and Corollary 5.5 (p. 18) are absent or theorem-shaped only
  through project axioms.
- None of the report's worked constructions or examples is formalized.
  `AvgCaseMls/Tests.lean` contains repository smoke tests, not report examples.
- No theorem formalizes the report's “nose” diagram; the repository contains a
  generated visualization and prose interpretation.

See `DEFINITION_FORKS.md` for exact differences between the report's
definitions and the executable Lean model.
