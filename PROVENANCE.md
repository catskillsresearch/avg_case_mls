# Provenance and claim boundary

This repository revisits *The average case complexity of multilevel
syllogistic*, Courant Institute Technical Report CS-TR 711 (1995), by Jim Cox,
Lars Ericson, and Bud Mishra. The report is preserved locally as
`TR1995-711.pdf`. Lars Warren Ericson directs and maintains this Lean 4
development.

The Lean code is a new formalization rather than a port of a pre-existing proof
assistant artifact. It defines average-case complexity vocabulary, MLS/EMLS
syntax, executable decision fragments, encodings, bounded-halting scaffolding,
and reduction interfaces.

Palomar validates only the report-related statements exposed by
`AvgCaseMls/Palomar.lean`. Their axiom audit contains only `propext`,
`Quot.sound`, and `Classical.choice`.

It does **not** certify the report's full Corollary 5.1. The current
NP-average-completeness and non-AvP chain depends on named project axioms for
the universal bounded-halting reduction, the general NBH-to-MLS compiler,
domination, and complexity-class transfer. Global FOS80 decision completeness
also retains one `sorry`. These boundaries are recorded in
`DEFINITION_FORKS.md`, `REPORT_CLAIM_AUDIT.md`, and `formalization.yaml`.
