# Principal checked results

The Palomar statement of record is `Challenge.lean`; checked implementations
are collected in `AvgCaseMls/Palomar.lean`.

## Selected report-related claims

- `AvgCasePalomar.step2_rejection` — Step 2 contradictions are rejected.
- `AvgCasePalomar.sound_fragment_completeness` — the implemented decision
  procedure accepts every formula in its explicit restricted sound fragment.
- `AvgCasePalomar.formula_serialization_roundtrip` — serialized formulas decode
  back to the original formula.
- `AvgCasePalomar.formula_encoding_polynomially_bounded` — the chosen encoding
  has the proved quadratic upper bound.
- `AvgCasePalomar.distributional_reduction_transitive` — the formalized
  distributional reductions compose.
- `AvgCasePalomar.average_completeness_transfers_along_reduction` — abstract
  NP-average completeness transfers to a target along a reduction.

## Not selected as completed results

`Completeness.satMLSProb_NPAverageComplete`,
`NonAvP.SatMLS_average_hard`, and related headline results depend on named
project axioms. `MLS.decideMLSSat_complete` retains one `sorry`. Palomar does
not present these declarations as completed proofs.

The examples in `AvgCaseMls/Tests.lean` are repository smoke tests. None is
identified as a worked example from TR1995-711, so they are not selected.
