import AvgCaseMls.Foundation.TapeMacros.Dynamic
import AvgCaseMls.Foundation.Universal.Encoding

/-!
# Fixed framing pass for the universal parser

`rawSevenParserMachine` is a closed base machine.  It accepts three
blank-delimited runtime blocks and appends four empty blocks.  Thus it turns

`program | fuel | input |`

into a physical seven-segment tape

`program | fuel | input | | | | |`.

The contents are deliberately left raw.  Later parser phases may move the
three nonempty blocks to their canonical roles.  The contract is on `Config`,
rather than `Result.output`, because `tapeOutput` intentionally discards all
blank delimiters.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation
open AvgCaseMls.Foundation.Universal

/-- A compositional, transition-counted execution relation for base machines. -/
inductive BaseRuns (machine : Machine) : Config → Nat → Config → Prop
  | refl (config) : BaseRuns machine config 0 config
  | next {config next final : Config} {transitions : Nat}
      (hstep : step machine config = .ok next)
      (hrun : BaseRuns machine next transitions final) :
      BaseRuns machine config (transitions + 1) final

theorem BaseRuns.trans {machine : Machine} {first middle final : Config}
    {m n : Nat} (h₁ : BaseRuns machine first m middle)
    (h₂ : BaseRuns machine middle n final) :
    BaseRuns machine first (m + n) final := by
  induction h₁ with
  | refl => simpa using h₂
  | next hstep hrun ih =>
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using
        BaseRuns.next hstep (ih h₂)

theorem baseRuns_evalFrom_eq {machine : Machine} {first final : Config}
    {transitions : Nat}
    (hrun : BaseRuns machine first transitions final) (fuel elapsed : Nat) :
    evalFrom machine (transitions + fuel) first elapsed =
      evalFrom machine fuel final (elapsed + transitions) := by
  induction hrun generalizing elapsed with
  | refl => simp
  | next hstep hrun ih =>
      rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]
      simp only [AvgCaseMls.Foundation.evalFrom, hstep]
      convert ih (elapsed + 1) using 1 <;> ac_rfl

private def symbols (bits : Bitstring) : List TapeSymbol := bits.map some

private def atCells (pc : Nat) (left : List TapeSymbol) :
    List TapeSymbol → Config
  | [] => ⟨pc, left, none, []⟩
  | head :: right => ⟨pc, left, head, right⟩

/--
The only instructions are branches, right moves, and halt.  States `0`, `3`,
and `6` scan the three supplied blocks; states `8`--`11` materialize four
additional blank cells.
-/
def rawSevenParserMachine : Machine :=
  ⟨#[
    .branch 2 1 1,
    .moveRight 0,
    .moveRight 3,
    .branch 5 4 4,
    .moveRight 3,
    .moveRight 6,
    .branch 8 7 7,
    .moveRight 6,
    .moveRight 9,
    .moveRight 10,
    .moveRight 11,
    .moveRight 12,
    .halt true
  ]⟩

def rawInvocationTape (program fuel input : Bitstring) :
    List TapeSymbol :=
  physicalSegment program ++ physicalSegment fuel ++ physicalSegment input

def rawSevenTape (program fuel input : Bitstring) : List TapeSymbol :=
  rawInvocationTape program fuel input ++ List.replicate 4 none

def rawInvocationConfig (program fuel input : Bitstring) : Config :=
  atCells 0 [] (rawInvocationTape program fuel input)

def rawSevenFinalConfig (program fuel input : Bitstring) : Config :=
  ⟨12,
    List.replicate 4 none ++ (symbols input).reverse ++ none ::
      (symbols fuel).reverse ++ none :: (symbols program).reverse,
    none, []⟩

private theorem scanProgram (bits : Bitstring) (left suffix : List TapeSymbol) :
    BaseRuns rawSevenParserMachine
      (atCells 0 left (symbols bits ++ none :: suffix))
      (2 * bits.length)
      (atCells 0 ((symbols bits).reverse ++ left) (none :: suffix)) := by
  induction bits generalizing left with
  | nil => exact .refl _
  | cons bit bits ih =>
      have htwo : BaseRuns rawSevenParserMachine
          (atCells 0 left (symbols (bit :: bits) ++ none :: suffix)) 2
          (atCells 0 (some bit :: left) (symbols bits ++ none :: suffix)) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem scanFuel (bits : Bitstring) (left suffix : List TapeSymbol) :
    BaseRuns rawSevenParserMachine
      (atCells 3 left (symbols bits ++ none :: suffix))
      (2 * bits.length)
      (atCells 3 ((symbols bits).reverse ++ left) (none :: suffix)) := by
  induction bits generalizing left with
  | nil => exact .refl _
  | cons bit bits ih =>
      have htwo : BaseRuns rawSevenParserMachine
          (atCells 3 left (symbols (bit :: bits) ++ none :: suffix)) 2
          (atCells 3 (some bit :: left) (symbols bits ++ none :: suffix)) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem scanInput (bits : Bitstring) (left : List TapeSymbol) :
    BaseRuns rawSevenParserMachine
      (atCells 6 left (symbols bits ++ [none]))
      (2 * bits.length)
      (atCells 6 ((symbols bits).reverse ++ left) [none]) := by
  induction bits generalizing left with
  | nil => exact .refl _
  | cons bit bits ih =>
      have htwo : BaseRuns rawSevenParserMachine
          (atCells 6 left (symbols (bit :: bits) ++ [none])) 2
          (atCells 6 (some bit :: left) (symbols bits ++ [none])) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

def rawSevenParserTransitions (program fuel input : Bitstring) : Nat :=
  2 * (program.length + fuel.length + input.length) + 10

/--
Universal physical-tape contract.  It quantifies over all three runtime
blocks, and the machine does not depend on any of them.
-/
theorem rawSevenParser_contract (program fuel input : Bitstring) :
    BaseRuns rawSevenParserMachine (rawInvocationConfig program fuel input)
      (rawSevenParserTransitions program fuel input - 1)
      (rawSevenFinalConfig program fuel input) := by
  have hp := scanProgram program [] (physicalSegment fuel ++ physicalSegment input)
  have hp' : BaseRuns rawSevenParserMachine
      (rawInvocationConfig program fuel input) (2 * program.length)
      (atCells 0 (symbols program).reverse
        (none :: physicalSegment fuel ++ physicalSegment input)) := by
    simpa [rawInvocationConfig, rawInvocationTape, physicalSegment, symbols,
      List.append_assoc] using hp
  have hpCross : BaseRuns rawSevenParserMachine
      (atCells 0 (symbols program).reverse
        (none :: physicalSegment fuel ++ physicalSegment input)) 2
      (atCells 3 (none :: (symbols program).reverse)
        (physicalSegment fuel ++ physicalSegment input)) := by
    exact .next (by rfl) (.next (by rfl) (.refl _))
  have hf := scanFuel fuel (none :: (symbols program).reverse)
    (physicalSegment input)
  have hf' : BaseRuns rawSevenParserMachine
      (atCells 3 (none :: (symbols program).reverse)
        (physicalSegment fuel ++ physicalSegment input))
      (2 * fuel.length)
      (atCells 3 ((symbols fuel).reverse ++ none ::
        (symbols program).reverse) (none :: physicalSegment input)) := by
    simpa [physicalSegment, symbols, List.append_assoc] using hf
  have hfCross : BaseRuns rawSevenParserMachine
      (atCells 3 ((symbols fuel).reverse ++ none :: (symbols program).reverse)
        (none :: physicalSegment input)) 2
      (atCells 6
        (none :: (symbols fuel).reverse ++ none :: (symbols program).reverse)
        (physicalSegment input)) := by
    exact .next (by rfl) (.next (by rfl) (.refl _))
  have hi := scanInput input
    (none :: (symbols fuel).reverse ++ none :: (symbols program).reverse)
  have hfinish : BaseRuns rawSevenParserMachine
      (atCells 6
        ((symbols input).reverse ++
          (none :: (symbols fuel).reverse ++ none ::
            (symbols program).reverse)) [none]) 5
      (rawSevenFinalConfig program fuel input) := by
    exact .next (by rfl) (.next (by rfl) (.next (by rfl)
      (.next (by rfl) (.next (by
        simp [rawSevenParserMachine, rawSevenFinalConfig, atCells, step,
          moveRight, symbols, List.append_assoc]) (.refl _)))))
  have hall := hp'.trans (hpCross.trans (hf'.trans (hfCross.trans
    (hi.trans hfinish))))
  convert hall using 1 <;>
    simp [rawInvocationConfig, rawInvocationTape, physicalSegment, atCells,
      symbols, rawSevenParserTransitions, rawSevenFinalConfig,
      List.append_assoc] <;> omega

/-- The final physical tape has exactly seven blank-terminated segments. -/
theorem rawSevenFinalConfig_tape (program fuel input : Bitstring) :
    (rawSevenFinalConfig program fuel input).left.reverse ++
      (rawSevenFinalConfig program fuel input).head ::
      (rawSevenFinalConfig program fuel input).right =
    rawSevenTape program fuel input := by
  simp [rawSevenFinalConfig, rawSevenTape, rawInvocationTape, physicalSegment,
    symbols, List.append_assoc]

/-- The generated tape is accepted by the shared seven-segment parser. -/
theorem splitCanonicalLayout_rawSevenTape (program fuel input : Bitstring) :
    splitCanonicalLayout? (rawSevenTape program fuel input) =
      some ⟨program, fuel, input, [], [], [], []⟩ := by
  simp [splitCanonicalLayout?, rawSevenTape, rawInvocationTape,
    splitPhysicalSegment?, List.append_assoc]

/-- Exact halting execution, including the final halt transition. -/
theorem rawSevenParser_evalFrom (program fuel input : Bitstring) :
    evalFrom rawSevenParserMachine
      (rawSevenParserTransitions program fuel input)
      (rawInvocationConfig program fuel input) 0 =
    some ⟨true, program ++ fuel ++ input,
      rawSevenParserTransitions program fuel input⟩ := by
  have hrun := rawSevenParser_contract program fuel input
  rw [show rawSevenParserTransitions program fuel input =
      (rawSevenParserTransitions program fuel input - 1) + 1 by
    simp [rawSevenParserTransitions]]
  rw [baseRuns_evalFrom_eq hrun 1 0]
  simp [rawSevenFinalConfig, rawSevenParserMachine, evalFrom, step, tapeOutput,
    symbols, rawSevenParserTransitions, List.append_assoc]

def rawSevenParserBound (n : Nat) : Nat := 2 * n + 10

theorem rawSevenParserTransitions_eq_bound (program fuel input : Bitstring) :
    rawSevenParserTransitions program fuel input =
      rawSevenParserBound (program.length + fuel.length + input.length) := rfl

theorem rawSevenParserBound_polynomial :
    IsPolynomial rawSevenParserBound :=
  .bounded 12 1 (fun n => by simp [rawSevenParserBound]; omega)

/-- Splitting a nonempty segment exposes its head and rest without host parsing. -/
theorem physicalSegment_split_head (head : Bool) (rest : Bitstring) :
    physicalSegment (head :: rest) =
      some head :: physicalSegment rest := by
  rfl

/-- Moving adjacent raw segments is list concatenation at the tape invariant. -/
theorem physicalSegment_concat (first second : Bitstring) :
    physicalSegment first ++ physicalSegment second =
      first.map some ++ none :: second.map some ++ [none] := by
  simp [physicalSegment, List.append_assoc]

def firstLane : Bitstring → Bitstring
  | first :: _ :: rest => first :: firstLane rest
  | rest => rest

def secondLane : Bitstring → Bitstring
  | _ :: second :: rest => second :: secondLane rest
  | rest => rest

/--
The fixed duplicator is a preserve-copy routine in paired representation:
both independently projected lanes equal the runtime source block.
-/
theorem duplicateEncoding_preserves_two_lanes (bits : Bitstring) :
    firstLane (duplicateEncoding bits) = bits ∧
      secondLane (duplicateEncoding bits) = bits := by
  induction bits with
  | nil => simp [firstLane, secondLane]
  | cons bit bits ih =>
      simp [duplicateEncoding_cons, firstLane, secondLane, ih]

end AvgCaseMls.Foundation.TapeMacros
