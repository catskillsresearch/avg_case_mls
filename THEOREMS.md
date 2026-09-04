# Principal checked results

The Palomar statement of record is `Challenge.lean`; checked implementations
are collected in `AvgCaseMls/Palomar.lean`.

## Selected report-related claims

- `AvgCasePalomar.paper_theorem_4_1` — fixed-distributional completeness
  implies language-level NP-average completeness.
- `AvgCasePalomar.paper_theorem_4_4` — explicit injective, invertible, honest
  reductions transport NP-average completeness in the finite-support model,
  provided the target language is separately shown to belong to `InNP`.
- `AvgCasePalomar.paper_example_4_1` — the Example 4.1 p-series converges and
  admits the normalized constant hidden by its big-O assertion.
- `AvgCasePalomar.paper_theorem_5_1_reduction_core` — the paper's SAT-to-MLS
  substitution preserves satisfiability, is injective, and has exact linear
  AST growth.
- `AvgCasePalomar.paper_theorem_5_2_reduction_core` — the constructive
  SAT-to-EMLS semantic gadget reduction preserves satisfiability and has an
  exact linear conjunct count. The selected statement does not claim
  injectivity from an uncharged provenance tag.
- `AvgCasePalomar.paper_theorem_5_3_reduction_core` — the SAT-to-0/1-ILP
  construction preserves satisfiability, is injective, and has exact linear
  constraint growth.

Routine support theorems for Step 2 rejection, restricted-fragment
completeness, serialization, encoding bounds, reduction transitivity, and
abstract completeness transfer remain proved in the library but are not part
of the focused six-theorem Palomar configuration.

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
