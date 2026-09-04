# TR1995-711 to Lean claim audit

Source: Cox, Ericson, and Mishra, *The average case complexity of multilevel
syllogistic*, Courant Institute Technical Report CS-TR 711 (1995),
[`sources/TR1995-711.pdf`](sources/TR1995-711.pdf), with draft transcription
[`sources/TR1995-711_vision.md`](sources/TR1995-711_vision.md).

## Palomar outcome

The mechanical preflight passes for the six selected paper-numbered/core
statements: Challenge and Solution types match, the selected proof source has
no `sorry`, and target axiom audits use only `propext`, `Quot.sound`, and
`Classical.choice`. `Challenge.lean` now gives every proposition and material
underlying notion a concrete Mathlib-only body; its only holes are the six
protocol-required theorem proofs.

The prior twelve-target editorial surface mixed these results with six routine
support declarations. The current configuration removes those support targets
and centers the audit on Theorems 4.1, 4.4, Example 4.1, and the reduction
cores of Theorems 5.1--5.3.

## Palomar-validated statements

| Report location | Lean statement | Validation boundary |
|---|---|---|
| Theorem 4.1, p. 12 | `AvgCasePalomar.paper_theorem_4_1` | Proved for the current finite-support distribution and reduction notions |
| Theorem 4.4, p. 14 | `AvgCasePalomar.paper_theorem_4_4` | Explicit injective/invertible/honest finite-support transport with exact rank preservation, plus a separate `InNP L₂` hypothesis because no machine-time model derives target NP membership |
| Example 4.1, pp. 8–9 | `AvgCasePalomar.paper_example_4_1` | Full shell p-series calculation and normalized big-O constant |
| Theorem 5.1, p. 15 | `AvgCasePalomar.paper_theorem_5_1_reduction_core` | Constructive SAT-to-MLS substitution: correctness, injectivity, exact linear AST size |
| Theorem 5.2, pp. 16–17 | `AvgCasePalomar.paper_theorem_5_2_reduction_core` | Constructive SAT-to-EMLS semantic gadgets: correctness and exact linear conjunct count; no uncharged provenance encoding |
| Theorem 5.3, p. 18 | `AvgCasePalomar.paper_theorem_5_3_reduction_core` | Constructive SAT-to-0/1-ILP reduction: correctness, injectivity, exact linear constraint size |

The reduction-core selections prove the constructive content used by the
numbered theorems, but not their still-missing average-completeness premises.

## Material definition differences

- Report distributions range over all bitstrings; Lean distributions have
  finite support.
- Both the report and Lean use the non-strict comparison `μ(z) ≥ μ(x)` for
  rank; Lean additionally assigns rank zero off its finite support.
- `DistTime` is not linked to a decider or to the language component, and
  `InNP` does not constrain verifier runtime.
- Lean distributional reductions omit report requirements for injectivity and
  polynomial-time computation, replacing them with an output-length bound.
- The NBH scaffold has one canonical trivial machine and a singleton
  distribution rather than the report's family over bounded-halting inputs.

## Formalized but not independently validated as report theorems

- `Completeness.satMLSProb_NPDistributionallyComplete` follows compositionally from
  explicit `LevinNBHData` and `NBHToMLSData` arguments.
- `NonAvP.SatMLS_average_hard` and its semantic/existential variants take an
  explicit `AverageCaseCollapseTheory` argument.
- `Reduction.nbhToSatMLS_red` packages the desired reduction interface once a
  caller supplies compiler correctness, length, and domination proofs.
- `DistTime` is not connected to a language decider. Consequently `AvP.zero`
  makes every polynomially rankable distribution tractable. The legacy
  hardness chain is therefore retained only as a conditional interface.

## Open or absent report claims

- Global completeness is now refuted for the current partial implementation by
  `MLS.not_decideMLSSat_complete`; propositional normalization, Step 1, and
  complete Step 4 model search remain open. There is no longer a `sorry`.
- `TR1995.theorem_4_1` proves the report's fixed-distributional-complete to
  language-average-complete implication for the current formalized notions.
- `TR1995.example_4_1` proves the p-series convergence calculation underlying
  Example 4.1; representing the report's infinite distribution and complete
  Levin-average-time assertion remains open.
- Theorems 3.1 and 3.2 (pp. 6–7), Theorem 4.2 (pp. 12–13), Theorem 4.3
  (p. 14), and the report's padding construction are not faithfully proved.
- Theorem 5.1 (p. 15), Corollary 5.1 (p. 16), Corollary 5.2 (p. 16),
  Theorem 5.2 and Corollary 5.3 (pp. 16–17), Corollary 5.4 (p. 18),
  Theorem 5.3 and Corollary 5.5 (p. 18) are not yet proved as full
  average-completeness results, although the concrete 5.1–5.3 reductions
  are checked.
- The full probability-shell calculation of Example 4.1 is formalized.
  `AvgCaseMls/Tests.lean`
  otherwise contains repository smoke tests, not report examples.
- No theorem formalizes the report's “nose” diagram; the repository contains a
  generated visualization and prose interpretation.

See `DEFINITION_FORKS.md` for exact differences between the report's
definitions and the executable Lean model.

## Related formal decision procedure

Stevens's 2023 Isabelle/HOL
[AFP development](https://isa-afp.org/entries/MLSS_Decision_Proc.html) and
[CADE 29 paper](https://doi.org/10.1007/978-3-031-38499-8_28) verify an
executable, terminating, sound, and complete tableau procedure for MLSS over
hereditarily finite sets. MLSS includes singleton terms and is richer than the
MLS syntax here. Its Cantone–Zarba tableau is distinct from this repository's
partial FOS80 model-graph procedure; it is the relevant proof-assistant
baseline for the restricted decision results.
