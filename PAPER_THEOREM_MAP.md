# TR1995-711 theorem map

Statement ground truth is
[`sources/TR1995-711_vision.md`](sources/TR1995-711_vision.md). When the report
quotes or sketches an external result, the proof source listed below must be
read before implementing its Lean declaration.

The status column distinguishes a result that is genuinely proved from a
theorem-shaped declaration whose proof still imports a project axiom.

| Paper item | Statement | Proof source | Closest current Lean declaration | Current status |
|---|---|---|---|---|
| Theorem 3.1 | For fixed positive `c,k`, with `k ≥ 3` and `c·2⁻ᵏ ≥ 0.7`, random `k`-CNF with `cn` clauses is almost surely unsatisfiable and has resolution complexity at least `(1+ε)ⁿ` for some `ε>0`. | `sources/CS87_vision.md` | None | Missing: random `k`-CNF, resolution proofs, asymptotics |
| Theorem 3.2 | Under the same density hypotheses, average resolution complexity on `K(cr,r,k)` is `Ω((1+ε)ʳ)`. | `sources/CS87_vision.md`, derived from Theorem 3.1 | None | Missing |
| Example 4.1 | Under `μ(x)=6/π²·|x|⁻²·2⁻|x|`, an `n²`-time machine is Levin-`μ` average `O(n^(1+ε))` for every `ε>0`. | `sources/RS93_vision.md` | `Example41.shellMass_eq`, `shellLevin_eq_contribution`, `normalized_levin_bound` | Full all-bitstring shell calculation and normalized Levin bound proved; empty string is transparently assigned mass zero because the displayed paper formula is singular there |
| Theorem 4.1 | If `(L,ρ)` is NP-distributional complete, then `L` is NP-average complete. | `sources/RS93_vision.md` | `TR1995.theorem_4_1` | Proved for the current formalized distribution/rank/reduction notions |
| Theorem 4.2 | A linear-time ranking corresponds to infinitely many `μ` for which `(SAT,μ)` is NP-distributional complete; hence SAT is NP-average complete. | `sources/RS93_vision.md`, `sources/Lev86_vision.md` | `Completeness.nbhProb_NPAverageComplete` | Axiom-backed and not SAT; current NBH has a singleton distribution |
| Theorem 4.3 | If SAT has an average-polynomial algorithm for every linear-time rankable distribution, then `NP ⊆ AvP`, every NP problem is efficient on average for every polynomial-time rankable distribution, and `NEXP=EXP`. | `sources/TR1995-711_vision.md`, `sources/Gur91_vision.md` | `NonAvP.NEXP_eq_EXP_of_AvP_complete` | Axiom-backed; current `DistTime` is not linked to a decider |
| Theorem 4.4 | An injective, polynomial-time invertible, honest polynomial-time reduction transfers NP-average completeness from `L₁` to `L₂`. | `sources/RS93_vision.md` | `HonestReduction.npAverageCompleteLanguage_of_faithfulReduction` | Finite-support specialization proved with explicit injectivity, inverse, range recognition, honesty, exact rank transport, and length bounds; it separately assumes `InNP L₂` because machine-level runtime is absent |
| Theorem 5.1 | Satisfiability for `MLS_∈` is NP-average complete via the injective SAT substitution reduction. | `sources/TR1995-711_vision.md`, `sources/COP90_vision.md` | `MLSInReduction.satisfiable_iff`, `toMLS_injective`, `formulaNodes_toMLS` | Concrete SAT substitution, semantic equivalence, injectivity, and exact linear AST size proved; SAT average completeness and timed rank transport remain |
| Corollary 5.1 | MLS satisfiability is NP-average complete. | `sources/TR1995-711_vision.md` | `Completeness.satMLSProb_NPAverageComplete` | Axiom-backed and stated for checker/singleton distribution rather than paper language |
| Corollary 5.2 | Satisfiability for `(∀)₀ˡ`-simple prenex formulae is NP-average complete. | `sources/TR1995-711_vision.md`, `sources/COP90_vision.md` | None | Missing syntax, semantics, NP membership, and embedding |
| Theorem 5.2 | EMLS satisfiability is NP-complete and NP-average complete via an injective, honest, polynomial-time invertible SAT reduction. | `sources/TR1995-711_vision.md` | `EMLSReduction.toEMLS_satisfiable_iff`, `toEMLS_injective`, `toEMLS_length_le` | Concrete elementary-literal reduction correctness, syntactic inversion, and linear size proved; NP and average-completeness transfer remain |
| Corollary 5.3 | Infinitely many linear-time rankable `μ'` make `(EMLS,μ')` NP-distributional complete. | `sources/TR1995-711_vision.md`, `sources/RS93_vision.md` | None | Missing infinite distributions and transported ranking |
| Corollary 5.4 | Assuming `EXP ≠ NEXP`, infinitely many linear-time rankable distributions force every EMLS algorithm to super-polynomial average time. | `sources/TR1995-711_vision.md`, `sources/Gur91_vision.md` | `NonAvP.SatMLS_average_hard` | Axiom-backed and for MLS checker, not EMLS |
| Theorem 5.3 | FPILP is NP-average complete via the standard injective, invertible, honest SAT-to-0/1-ILP reduction. | `sources/TR1995-711_vision.md` | `TR1995.FPILPSource.satToFPILP_feasible_iff`, `satToFPILP_injective`, size theorems | Concrete 0/1-ILP reduction correctness, injectivity, and exact size counts proved; average-completeness transfer remains |
| Corollary 5.5 | Infinitely many linear-time rankable `μ` make `(FPILP,μ)` NP-distributional complete. | `sources/TR1995-711_vision.md`, `sources/RS93_vision.md` | None | Missing |

## Non-numbered supporting obligation

The report relies on the FOS80 decision procedure, but does not number global
MLS decision completeness as one of its own theorems. The current
`MLS.decideMLSSat_complete` is a `sorry` and its current statement is not
provable for the implemented partial parser: satisfiable formulae containing
disjunction, implication, equivalence, or unsupported terms can be rejected
before the model-graph checks. Closing it requires implementing normalization
and the complete model search, not a proof-only edit.

## Definition repairs required for faithful statements

1. Infinite distributions on all bitstrings, with a finite-rank condition for
   positive mass; the current `Finset` support cannot express Example 4.1 or
   the infinitely-many-distributions corollaries.
2. Complexity bounds equipped with monotonicity/time-constructibility.
3. `DistDTime` linked to an actual language decider and its running time.
4. Rankability linked to an algorithm computing the rank within the bound.
5. Paper-level NP and exponential-time classes, rather than only a certificate
   relation with no verifier runtime model.
6. Distributional reductions with injectivity, polynomial-time computation,
   correctness, and rank domination.
7. Honest, polynomial-time invertible language reductions for Theorem 4.4.
8. Concrete SAT, resolution, `MLS_∈`, prenex, EMLS, and FPILP languages.

No numbered result should enter `Challenge.lean` as “paper-faithful” until its
statement uses these repaired definitions or an explicitly documented,
mathematically equivalent specialization.
