# Principal checked results

The Palomar statement of record is `Challenge.lean`; checked implementations
are collected in `AvgCaseMls/Palomar.lean`.

## Selected report-related claims

Five encoding-collapse diagnostics of the untimed AvCom layer:

- `AvgCasePalomar.paper_collapse_inNP_trivial`
- `AvgCasePalomar.paper_collapse_completeness_characterization`
- `AvgCasePalomar.paper_collapse_theorem44_vacuous`
- `AvgCasePalomar.paper_collapse_avP_characterization`
- `AvgCasePalomar.paper_collapse_no_theory_separates`

Plus Example 4.1 and the three SAT reduction cores:

- `AvgCasePalomar.paper_example_4_1` — the Example 4.1 p-series converges and
  admits the normalized constant hidden by its big-O assertion.
- `AvgCasePalomar.paper_theorem_5_1_reduction_core` — SAT-to-MLS substitution:
  correctness, injectivity, left inverse, exact linear AST growth.
- `AvgCasePalomar.paper_theorem_5_2_reduction_core` — tagged SAT-to-EMLS
  `toEMLS`: correctness, injectivity, left inverse, exact linear conjunct count.
- `AvgCasePalomar.paper_theorem_5_3_reduction_core` — SAT-to-0/1-ILP:
  correctness, injectivity, exact linear constraint growth; no decoder.

Definition holes on this surface: `MLSInReduction.fromMLS`,
`EMLSReduction.sourceBits`, `EMLSReduction.toEMLS`, `EMLSReduction.fromEMLS`.

Routine support theorems for Step 2 rejection, restricted-fragment
completeness, serialization, encoding bounds, reduction transitivity, and
abstract completeness transfer remain proved in the library but are not part
of the focused nine-theorem Palomar configuration. Untimed TR1995 Theorems
4.1 and 4.4 are likewise library-only.

## Not selected as completed results

`Completeness.satMLSProb_NPDistributionallyComplete`,
`NonAvP.SatMLS_average_hard`, and related legacy NBH results are conditional
on explicit compiler, universal-reduction, and collapse-theory arguments.
They no longer depend on project axioms. The old
`MLS.decideMLSSat_complete` placeholder has also been removed:
`MLS.not_decideMLSSat_complete` proves that the current partial implementation
is not globally complete.

The examples in `AvgCaseMls/Tests.lean` are repository smoke tests. None is
identified as a worked example from TR1995-711, so they are not selected.

## Paper-aligned work

- `TR1995.theorem_4_1` proves the report's fixed-distributional-complete to
  language-average-complete implication for the current formalized notions.
- `TR1995.example_4_1` proves the p-series convergence calculation underlying
  the report's worked Example 4.1.
- `PAPER_THEOREM_MAP.md` records the exact remaining definition and proof
  obligations for every numbered result.
