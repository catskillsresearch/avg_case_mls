import AvgCaseMls.Foundation.Machine

/-!
# Bounded accepting tableaux

This file gives the semantic core of the Cook--Levin construction for the
concrete two-stack machines in `Foundation.Machine`.  A tableau is a nonempty
list of complete configurations.  Consecutive rows must be related by one
machine transition, and the final row must execute an accepting halt.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

/-- The rows form an accepting computation, including the final halting row. -/
def AcceptingRows (M : Machine) : List Config → Prop
  | [] => False
  | [c] => ∃ r, step M c = .error r ∧ r.accept = true
  | c :: c' :: rows => step M c = .ok c' ∧ AcceptingRows M (c' :: rows)

/--
A bounded accepting tableau starts in the prescribed initial configuration
and contains at most `time` rows.  Since the final halt consumes one machine
step, rows and fuel have exactly the same bound.
-/
def BoundedAcceptingTableau
    (M : Machine) (input : Bitstring) (time : Nat) (rows : List Config) : Prop :=
  rows.head? = some (initial input) ∧
    rows.length ≤ time ∧
    AcceptingRows M rows

private theorem evalFrom_acceptingRows_iff
    (M : Machine) (fuel : Nat) (c : Config) (elapsed : Nat) :
    (∃ r, evalFrom M fuel c elapsed = some r ∧ r.accept = true) ↔
      ∃ rows, rows.head? = some c ∧ rows.length ≤ fuel ∧ AcceptingRows M rows := by
  induction fuel generalizing c elapsed with
  | zero =>
      simp [evalFrom]
  | succ fuel ih =>
      simp only [evalFrom]
      cases hstep : step M c with
      | error halted =>
          constructor
          · intro h
            refine ⟨[c], rfl, by simp, ?_⟩
            rcases h with ⟨r, hr, ha⟩
            simp only [Option.some.injEq] at hr
            subst r
            exact ⟨halted, hstep, ha⟩
          · rintro ⟨rows, hhead, hlength, hrows⟩
            cases rows with
            | nil => simp at hhead
            | cons first rest =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                subst first
                cases rest with
                | nil =>
                    rcases hrows with ⟨r, hr, ha⟩
                    rw [hstep] at hr
                    cases hr
                    exact ⟨{
                      halted with steps := elapsed + 1
                    }, by simp, ha⟩
                | cons second tail =>
                    exact False.elim (by
                      rcases hrows with ⟨hr, _⟩
                      rw [hstep] at hr
                      contradiction)
      | ok next =>
          constructor
          · intro h
            have htail :
                ∃ rows, rows.head? = some next ∧
                  rows.length ≤ fuel ∧ AcceptingRows M rows := by
              apply (ih next (elapsed + 1)).mp
              simpa [hstep] using h
            rcases htail with ⟨rows, hhead, hlength, hrows⟩
            refine ⟨c :: rows, by simp, ?_, ?_⟩
            · simp
              omega
            · cases rows with
              | nil => simp at hhead
              | cons first rest =>
                  simp only [List.head?_cons, Option.some.injEq] at hhead
                  subst first
                  exact ⟨hstep, hrows⟩
          · rintro ⟨rows, hhead, hlength, hrows⟩
            cases rows with
            | nil => simp at hhead
            | cons first rest =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                subst first
                cases rest with
                | nil =>
                    rcases hrows with ⟨r, hr, _⟩
                    rw [hstep] at hr
                    contradiction
                | cons second tail =>
                    rcases hrows with ⟨hnext, htail⟩
                    rw [hstep] at hnext
                    cases hnext
                    apply (ih next (elapsed + 1)).mpr
                    refine ⟨next :: tail, rfl, ?_, htail⟩
                    simp at hlength ⊢
                    omega

/-- A machine accepts within `time` fuel iff it has a bounded accepting tableau. -/
theorem boundedAcceptingTableau_iff_eval
    (M : Machine) (input : Bitstring) (time : Nat) :
    (∃ r, eval M time input = some r ∧ r.accept = true) ↔
      ∃ rows, BoundedAcceptingTableau M input time rows := by
  simpa [eval, BoundedAcceptingTableau] using
    evalFrom_acceptingRows_iff M time (initial input) 0

/-- Existential bounded acceptance, packaged as a language-level predicate. -/
def AcceptsWithin (M : Machine) (input : Bitstring) (time : Nat) : Prop :=
  ∃ r, eval M time input = some r ∧ r.accept = true

theorem acceptsWithin_iff_tableau
    (M : Machine) (input : Bitstring) (time : Nat) :
    AcceptsWithin M input time ↔
      ∃ rows, BoundedAcceptingTableau M input time rows :=
  boundedAcceptingTableau_iff_eval M input time

end AvgCaseMls.Section4.CookLevin
