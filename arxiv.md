# Revisiting average case complexity of multilevel syllogistic: From the 1995 NYU Courant Technical Report to Lean 4 Formalization

## 1. Introduction: The Vision of AvCom in Program Verification

In the late 1970s and throughout the 1980s, the "Correct Program Technology" (CPT) movement, spearheaded by figures such as Martin Davis and Jacob T. Schwartz, envisioned a software development pipeline where programmers wrote code alongside mathematical specifications [DS77]. A compiler, integrated with an automated theorem prover, would then verify that the program met its specification. 

To make this feasible, researchers sought to enrich Floyd-Hoare verification tools with decision procedures for decidable sublanguages of set theory and arithmetic. These logic fragments—such as Multilevel Syllogistic (MLS) and Elementary Multilevel Syllogistic (EMLS)—modeled the set-theoretic operations typical of high-level programming languages like SETL [Sny90a].

However, worst-case complexity analysis posed a major roadblock: the decision problems for MLS and EMLS are NP-complete, and extensions involving Presburger arithmetic exhibit exponential or double-exponential worst-case bounds. To bypass this, researchers pointed to early optimistic results by Goldberg [Gol79], which suggested that the Davis-Putnam procedure and resolution-based SAT solvers could perform exceptionally well on "average" inputs.

In their 1995 New York University Courant Institute Technical Report, *"The average case complexity of multilevel syllogistic"* (TR1995-711), Jim Cox, Lars Ericson, and Bud Mishra set out to evaluate this optimism rigorously. They sought to marry the mathematical foundations of **average-case complexity (AvCom)** with set-theoretic decision procedures to determine whether a typical instance of these verification problems is truly tractable.

---

## 2. Recap of Multilevel Syllogistic (MLS) and Its Decision Procedures

### Syntax of MLS and EMLS
Multilevel Syllogistic (MLS) is a decidable fragment of Zermelo-Fraenkel set theory. Its syntax allows set variables, the empty set ($\emptyset$), binary set operators (union $\cup$, intersection $\cap$, set difference $\setminus$), binary set relations (membership $\in$, non-membership $\notin$, equality $=$, inequality $\neq$), and standard propositional connectives.

The grammar is formally defined as:
*   **Terms:** $T \to v_i \mid \emptyset \mid T \cup T \mid T \cap T \mid T \setminus T$
*   **Literals:** $L \to T \in T \mid T \notin T \mid T = T \mid T \neq T$
*   **Formulas:** $\Phi \to L \mid \neg \Phi \mid \Phi \land \Phi \mid \Phi \lor \Phi \mid \Phi \Rightarrow \Phi \mid \Phi \equiv \Phi$

**Elementary Multilevel Syllogistic (EMLS)** simplifies the terms by restricting conjuncts to "flat" elementary literals:
$$v_i = \emptyset, \quad v_i = v_j \cup v_k, \quad v_i = v_j \setminus v_k, \quad v_i = v_j \cap v_k, \quad v_i \in v_j, \quad v_i \notin v_j, \quad v_i \neq v_j$$

### Decision Procedures
The primary algorithm proposed to decide the satisfiability of MLS and EMLS formulas is the **model-graph algorithm** (originally analyzed by Ferro, Omodeo, and Schwartz [FOS80]). 

To determine whether an EMLS formula $\Phi$ is satisfiable:
1.  **Normalization:** Translate the formula into a conjunct of elementary literals.
2.  **Graph Construction:** Build a directed model graph representing the membership and equality relations between set variables.
3.  **Refinement:** Propagate set-theoretic axioms (such as extensionality: if two sets have the same elements, they are equal) through the graph to detect contradictions.
4.  **Worst-Case Performance:** In the worst case, the number of distinct models that must be checked is $2^{4n^3}$ where $n$ is the number of variables, leading to an exponential worst-case runtime.

---

## 3. Average-Case Complexity (AvCom) in 1995: Theory, Visualizations, and Classes

In the mid-1990s, structural average-case complexity was a young, highly mathematical field. 

### Why Naive Averaging Fails
Prior to Leonid Levin’s 1986 breakthrough [Lev86], researchers measured average running time naively:
$$\text{Time}_M^{\mu}(n) = \sum_{|x|=n} \mu_n(x) \text{time}_M(x)$$
As noted by Ben-David et al. [BDCGL89], this formulation is deeply flawed:
*   **Not closed under functional composition:** An algorithm that runs in average $O(n)$ time can yield an average-case exponential runtime when composed with a polynomial-time pre-processing step.
*   **Encoding-dependent:** Slight changes in the binary representation of inputs radically alter the average complexity.

### Levin's and Reischuk-Schindelhauer's Robust Classes
Levin solved this by defining average-case polynomial time using a power-weighted expectation. In 1993, Reischuk and Schindelhauer [RS93] streamlined this theory by introducing **ranking functions** to capture the distribution profile.

Let $\mu$ be a probability distribution on $\Sigma^*$. The **rank** of an instance $x$ under $\mu$ is:
$$\text{rank}_{\mu}(x) = |\{ z \in \Sigma^* : \mu(z) \geq \mu(x) \}|$$

Under this framework, Cox, Ericson, and Mishra utilize several precise complexity classes:

*   **$\text{POL-rankable}$ Distributions:** A distribution $\mu$ is polynomial-time rankable if its rank function $\text{rank}_{\mu}(x)$ can be computed in binary in deterministic polynomial time.
*   **$\text{Av}(T)$ (Average Time $T$):** A running time function $f : \Sigma^* \to \mathbb{N}$ is in $\text{Av}(T)$ under distribution $\mu$ if, for all integers $\ell \geq 1$:
    $$\sum_{\text{rank}_{\mu}(x) \leq \ell} \frac{T^{-1}(f(x))}{|x|} \leq \ell$$
*   **$\text{AvP}$ (Average Polynomial Time):** The set of distributional problems $(L, \mu)$ solvable on average in polynomial time over $\text{POL-rankable}$ distributions.
*   **$\text{distNP}$:** The class of distributional problems $(L, \mu)$ where $L \in \text{NP}$ and $\mu \in \text{POL-rankable}$.

### The Concept of "The Nose"
The paper features a key visualization of the average-case landscape of NP-complete languages (Figure 1, page 13).

```
  Worst-Case 
  Complexity (V)
       ▲
       │             L4       L3
       │            /        /    L2
   Pol ┼───────────┼────────┼────/──────
       │           │       /    /  L1
       │           │      /    /  /
  h(T) ┼───────────┼─────┼────┼──/──────
       │          /     /    /  /
     N ┼─────────┼─────┼────┼──/────────
       │        /     /    /  / 
       │       /     /____/  /
       │      /     /     \ /
       │     /     / Nose  *
       │    /     /________/
       └────┴─────┴────────┼──────────► Average-Case Complexity (T)
            N    Pol      Pol
```

In this diagram, languages $L_i$ are mapped based on their worst-case complexity $V$ (vertical axis) and their average-case complexity $T$ (horizontal axis). 
*   **The Nose** represents the sweet spot of tractability: the shaded region where the worst-case complexity of the ranking function $V$ is bounded by $h(T)$, such that the language still possesses an efficient average-case algorithm.
*   Formally, the authors define this boundary as:
    $$\text{nose}(L) = \{ (T, V) \in (\text{POL}, \text{POL}) : L \in \text{AvDTime}(T, V\text{-rankable}) \}$$
*   For an NP-average complete problem, the "nose" is trivial or empty under simple distributions, meaning no non-trivial efficient average-case behavior can be guaranteed unless $\text{Nondeterministic Exp} = \text{Deterministic Exp}$.

---

## 4. Legacy and Citations of TR1995-711

The technical report TR1995-711 remains a highly specialized document:
*   **Citations:** The report has very low academic citation rates. It exists primarily as a archival Courant Institute technical report. Its memory is preserved largely through references on the Wikipedia page for "Average-case complexity," where it is cited as an example of an applied average-case completeness proof.
*   **Practical Impact:** Martin Davis famously requested that the authors provide a more pragmatic, empirical demonstration of their results before publishing in *Communications on Pure and Applied Mathematics* (CPAM). The authors could not deliver this; their concrete heuristics were weak, and the empirical machinery to test these algorithms on large datasets did not yet exist. As a result, the paper was never published in CPAM.
*   **Pursuit of MLS + AvCom:** The specific application of AvCom to MLS was largely abandoned. The theorem-proving community realized that proving average-case hardness under mathematically simple, rankable distributions (such as those analyzed in the paper) did not reflect the highly structured formulas generated by real-world compilers.

---

## 5. Development of Average-Case Complexity to Date (2026)

In the three decades since 1995, average-case complexity has evolved into a cornerstone of computer science, though its focus has shifted:

1.  **Lattice Cryptography and Worst-to-Average Reductions:** 
    Following Miklós Ajtai's seminal work in 1996 [Ajt96] and Oded Regev's introduction of Learning With Errors (LWE) in 2005 [Reg05], researchers found ways to prove average-case hardness by reducing *worst-case* lattice problems to them. This forms the mathematical basis for post-quantum cryptography standards.
2.  **Smoothed Analysis:**
    Introduced by Spielman and Teng in 2001 [ST01], smoothed analysis measures the performance of algorithms under slight random perturbations of worst-case inputs. This successfully bridged the gap between theory and practice, explaining why algorithms like Simplex or local search run efficiently in the real world.
3.  **The Shift in Formal Verification (SMT Solvers):**
    The program verification community moved away from decidable set-theoretic fragments like MLS. Instead, they embraced **Satisfiability Modulo Theories (SMT)** solvers (such as Z3 and CVC5) [deM08]. Powered by Conflict-Driven Clause Learning (CDCL) and heuristic-based solvers, modern verification tools solve massive formulas with millions of variables in practice, bypassing theoretical worst-case and average-case limits.

---

## 6. Formalizing MLS in Lean 4

Below, we write a complete, self-contained deep embedding of MLS syntax in Lean 4. To represent the domain of sets, we model set-theoretic semantics using an axiomatic `ZFSet` representing Zermelo-Fraenkel sets.

```lean
-- Define the logical and syntactic structures of MLS in Lean 4

namespace MLS

/- 1. Syntactic Terms -/
inductive Term : Type
  | var   : Nat → Term
  | empty : Term
  | union : Term → Term → Term
  | inter : Term → Term → Term
  | diff  : Term → Term → Term
  deriving DecidableEq, Repr

/- 2. Set-Theoretic Relations -/
inductive Relation : Type
  | mem     : Term → Term → Relation
  | not_mem : Term → Term → Relation
  | eq      : Term → Term → Relation
  | neq     : Term → Term → Relation
  deriving DecidableEq, Repr

/- 3. Propositional Formulas -/
inductive Formula : Type
  | rel : Relation → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or  : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | iff : Formula → Formula → Formula
  deriving DecidableEq, Repr

/- 4. Axiomatic Semantics -/
-- We assume an abstract type representing Zermelo-Fraenkel sets 
-- to provide a standard mathematical universe.
axiom ZFSet : Type

axiom ZFSet.empty : ZFSet
axiom ZFSet.union : ZFSet → ZFSet → ZFSet
axiom ZFSet.inter : ZFSet → ZFSet → ZFSet
axiom ZFSet.diff  : ZFSet → ZFSet → ZFSet
axiom ZFSet.mem   : ZFSet → ZFSet → Prop

-- Map variable indices to sets
def Env : Type := Nat → ZFSet

-- Term Evaluation
def evalTerm (env : Env) : Term → ZFSet
  | Term.var n       => env n
  | Term.empty       => ZFSet.empty
  | Term.union t1 t2 => ZFSet.union (evalTerm env t1) (evalTerm env t2)
  | Term.inter t1 t2 => ZFSet.inter (evalTerm env t1) (evalTerm env t2)
  | Term.diff t1 t2  => ZFSet.diff (evalTerm env t1) (evalTerm env t2)

-- Formula Evaluation
def evalFormula (env : Env) : Formula → Prop
  | Formula.rel (Relation.mem t1 t2)     => ZFSet.mem (evalTerm env t1) (evalTerm env t2)
  | Formula.rel (Relation.not_mem t1 t2) => ¬ ZFSet.mem (evalTerm env t1) (evalTerm env t2)
  | Formula.rel (Relation.eq t1 t2)      => evalTerm env t1 = evalTerm env t2
  | Formula.rel (Relation.neq t1 t2)     => evalTerm env t1 ≠ evalTerm env t2
  | Formula.not f                        => ¬ evalFormula env f
  | Formula.and f1 f2                    => evalFormula env f1 ∧ evalFormula env f2
  | Formula.or f1 f2                     => evalFormula env f1 ∨ evalFormula env f2
  | Formula.imp f1 f2                    => evalFormula env f1 → evalFormula env f2
  | Formula.iff f1 f2                    => evalFormula env f1 ↔ evalFormula env f2

end MLS
```

---

## 7. Coding the Decision Procedures for MLS in Lean 4

We now implement a decision procedure in Lean 4. While the full model-graph algorithm is highly complex, we define a structural skeleton for a decision procedure (`decideMLS`) and state its soundness and completeness.

```lean
namespace MLS

/- A mock representation of a decision procedure for MLS formulas. -/
def decideMLS : Formula → Bool
  | Formula.rel (Relation.eq (Term.empty) (Term.empty)) => true
  | Formula.rel (Relation.neq (Term.empty) (Term.empty)) => false
  | _ => false -- In a full implementation, this runs the model-graph search.

/- Soundness: If the decision procedure returns true, the formula is valid. -/
theorem decideMLS_sound (f : Formula) (h : decideMLS f = true) :
    ∀ (env : Env), evalFormula env f := by
  intro env
  induction f with
  | rel r => 
    cases r with
    | eq t1 t2 => 
      sorry
    | neq t1 t2 => 
      sorry
    | mem t1 t2 => 
      sorry
    | not_mem t1 t2 => 
      sorry
  | not f' ih => 
    sorry
  | and f1 f2 ih1 ih2 => 
    sorry
  | or f1 f2 ih1 ih2 => 
    sorry
  | imp f1 f2 ih1 ih2 => 
    sorry
  | iff f1 f2 ih1 ih2 => 
    sorry

/- Completeness: If the formula is valid, the decision procedure must return true. -/
theorem decideMLS_complete (f : Formula) (h : ∀ (env : Env), evalFormula env f) :
    decideMLS f = true := by
  sorry

end MLS
```

---

## 8. Coding the AvCom Complexity Analysis in Lean 4

Here, we construct the average-case complexity definitions using the Reischuk-Schindelhauer framework within Lean 4.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset

-- Input representation
abbrev Bitstring := List Bool

def len (s : Bitstring) : Nat := s.length

/- A probability distribution over finite bitstrings -/
structure Distribution where
  prob : Bitstring → Real
  nonneg : ∀ s, 0 ≤ prob s
  sum_le_one : ∀ (F : Finset Bitstring), F.sum prob ≤ 1

/- The rank of an input under distribution μ -/
noncomputable def rank (μ : Distribution) (x : Bitstring) : Nat :=
  if μ.prob x = 0 then 0
  else
    -- Conceptually: |{ z : μ.prob z ≥ μ.prob x }|
    sorry

/- Structural definition of Average Polynomial Time (AvP) -/
def T_inv (T : Nat → Nat) (m : Nat) : Nat :=
  -- Inverse of a monotonically increasing complexity bound
  sorry

def IsAvTime (T : Nat → Nat) (f : Bitstring → Nat) (μ : Distribution) : Prop :=
  ∀ (l : Nat), l ≥ 1 →
    ∃ (S : Finset Bitstring),
      (∀ x, x ∈ S ↔ rank μ x ≤ l) ∧
      S.sum (fun x => (T_inv T (f x) : Real) / (len x : Real)) ≤ (l : Real)

structure DistributionalProblem where
  L : Set Bitstring
  μ : Distribution

def IsPolynomial (T : Nat → Nat) : Prop :=
  ∃ (c k : Nat), ∀ n, T n ≤ c * n^k + c

/- The class AvP: Average Polynomial Time -/
def AvP (prob : DistributionalProblem) : Prop :=
  ∃ (f : Bitstring → Nat) (T : Nat → Nat),
    IsPolynomial T ∧ IsAvTime T f prob.μ
```

---

## 9. Lean 4 Verification: Proving Average-Case Hardness Properties

The 1995 paper proves that the satisfiability of MLS formulas is **NP-average complete**. Under the defined AvCom classes, this implies that MLS cannot belong to $\text{AvP}$ under certain rankable distributions unless the nondeterministic and deterministic exponential-time hierarchies collapse.

We can represent this theorem structurally in Lean 4:

```lean
-- Abstract representation of the non-triviality of the "Nose" of MLS

axiom NEXP_neq_EXP : Prop -- Nondeterministic Exponential Time != Deterministic Exponential Time

-- Map an MLS Formula to its binary representation
axiom serializeFormula : MLS.Formula → Bitstring

-- The language of satisfiable MLS formulas
def SatMLS : Set Bitstring :=
  { s | ∃ (f : MLS.Formula), serializeFormula f = s ∧ ∃ (env : MLS.Env), MLS.evalFormula env f }

/-
  Theorem 5.1 (adapted): SatMLS is NP-average complete.
  Consequently, there exists a simple, polynomial-time rankable distribution μ 
  under which (SatMLS, μ) is not in AvP, assuming NEXP ≠ EXP.
-/
theorem SatMLS_average_hard (μ : Distribution) (h_rank : ∃ T, IsPolynomial T ∧ ∀ x, rank μ x ≤ T (len x)) :
    NEXP_neq_EXP → ¬ AvP ⟨SatMLS, μ⟩ := by
  intro h_collapse h_avp
  -- The proof sketch reduces the bounded halting problem for NTMs (NBH)
  -- to SatMLS, showing that if SatMLS was in AvP, NBH would be in AvP,
  -- collapsing NEXP to EXP.
  sorry
```

---

## 10. Suggestions for Future Work

Building on this integration of automated theorem proving and structural complexity, several avenues for future work emerge:

1.  **Formalizing Smoothed Analysis in Lean 4:**
    While average-case complexity under fixed distributions can be overly pessimistic, formalizing Spielman-Teng smoothed analysis would allow researchers to verify the typical-case tractability of modern SAT/SMT algorithms under random perturbations.
2.  **Verified SMT Solvers with Monadic Cost Models:**
    One could implement an executable SMT solver in Lean 4 (using a monadic state to track recursive steps) and formally prove that it runs in polynomial time on structured, non-random formula distributions.
3.  **Extending Mathlib's Complexity Library:**
    The current complexity theory developments in Mathlib4 are focused on worst-case bounds. Standardizing Levin’s structural average-case reductions and the domination condition in Mathlib would provide a robust framework for certifying the post-quantum security of lattice-based cryptographic protocols.

---

## References

*   **[Ajt96]** Ajtai, M. (1996). Generating hard instances of lattice problems. *STOC*.
*   **[BDCGL89]** Ben-David, S., Chor, B., Goldreich, O., & Luby, M. (1989). On the theory of average case complexity. *STOC*.
*   **[deM08]** de Moura, L., & Bjørner, N. (2008). Z3: An efficient SMT solver. *TACAS*.
*   **[DS77]** Davis, M., & Schwartz, J. T. (1977). Metamathematical extensibility for theorem verifiers. *NYU Technical Report*.
*   **[FOS80]** Ferro, A., Omodeo, E. G., & Schwartz, J. T. (1980). Decision procedures for elementary sublanguages of set theory. *CPAM*.
*   **[Gol79]** Goldberg, A. T. (1979). On the complexity of the satisfiability problem. *NYU PhD Thesis*.
*   **[Lev86]** Levin, L. (1986). Average case complete problems. *SIAM Journal on Computing*.
*   **[Reg05]** Regev, O. (2005). On lattices, learning with errors, and cryptography. *STOC*.
*   **[RS93]** Reischuk, R., & Schindelhauer, C. (1993). Precise average case complexity. *STOC*.
*   **[Sny90a]** Snyder, W. K. (1990). The SETL2 programming language. *NYU Technical Report*.
*   **[ST01]** Spielman, D. A., & Teng, S. H. (2001). Smoothed analysis of algorithms. *STOC*.
