import AvgCaseMls.Foundation.Universal.Execution
import AvgCaseMls.Foundation.Codec

/-!
# Contiguous self-delimiting header boundary

This file contains the fixed invocation-parsing primitive which is missing
from the blank-delimited tape macros.  Its input is an ordinary contiguous
bitstring

`encodeNat n ++ payload ++ suffix`, with `payload.length = n`.

The machine consumes the `encodeNat` header as workspace.  Its zero
terminator becomes a movable blank.  The width prefix is checked against the
binary word, the canonical high bit is checked, and that binary word is then
decremented at runtime.  One payload cell is crossed for every decrement, so
the final blank is exactly between `payload` and `suffix`.  No delimiter is
placed on the tape by the host.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation
open AvgCaseMls.Foundation.Universal

set_option maxRecDepth 8192

private def symbols (bits : Bitstring) : List TapeSymbol := bits.map some

private def atCells (pc : Nat) (left : List TapeSymbol) :
    List TapeSymbol → Config
  | [] => ⟨pc, left, none, []⟩
  | head :: right => ⟨pc, left, head, right⟩

/--
A fixed 113-state base machine.  States `0`--`53` validate and consume the
self-delimiting header.  The remaining states install a permanent counter
delimiter, repeatedly decrement the runtime binary word, and move a second
blank across the payload.
-/
def headerBoundaryMachine : Machine :=
  ⟨#[
    .moveLeft 37,                -- 0: install guard blank and sentinel
    .moveRight 2,                -- 1
    .jump 3,                     -- 2
    .branch 40 4 5,              -- 3: empty / width zero / positive width
    .write none 41,              -- 4: encodeNat 0
    .moveRight 6,                -- 5: scan unary width
    .branch 40 7 5,              -- 6
    .write none 8,               -- 7: terminator becomes moving blank
    .moveLeft 9,                 -- 8: first width token
    .write none 10,              -- 9
    .moveRight 11,               -- 10: old moving blank
    .moveRight 12,               -- 11: first binary digit
    .branch 40 13 17,            -- 12: swap digit through blank
    .write none 14,              -- 13: remember false
    .moveLeft 15,                -- 14
    .write (some false) 16,      -- 15
    .moveRight 20,               -- 16
    .write none 18,              -- 17: remember true
    .moveLeft 19,                -- 18
    .write (some true) 16,       -- 19
    .moveLeft 21,                -- 20: inspect newest high digit
    .branch 40 25 27,            -- 21: remember newest binary digit
    .branch 24 25 25,            -- 22: scan processed, remember false
    .branch 26 27 27,            -- 23: scan processed, remember true
    .branch 28 40 30,            -- 24: blank width area / sentinel / token
    .moveLeft 22,                -- 25
    .branch 29 50 30,            -- 26
    .moveLeft 23,                -- 27
    .moveLeft 24,                -- 28
    .moveLeft 26,                -- 29
    .write none 31,              -- 30: consume another width token
    .moveRight 32,               -- 31
    .branch 33 34 34,            -- 32: cross consumed width cells
    .moveRight 32,               -- 33
    .moveRight 35,               -- 34: cross processed binary digits
    .branch 36 34 34,            -- 35
    .moveRight 12,               -- 36: next binary digit
    .moveLeft 38,                -- 37
    .write (some false) 39,      -- 38
    .moveRight 1,                -- 39
    .halt false,                 -- 40: malformed
    .halt true,                  -- 41: success
    .halt false,                 -- 42
    .halt false,                 -- 43
    .halt false,                 -- 44
    .halt false,                 -- 45
    .halt false,                 -- 46
    .halt false,                 -- 47
    .halt false,                 -- 48
    .halt false,                 -- 49
    .moveRight 51,               -- 50: canonical high bit was true
    .branch 52 53 53,            -- 51: cross erased width/header cells
    .moveRight 51,               -- 52
    .moveLeft 54,                -- 53: counter start; fetch a second blank
    .moveRight 55,               -- 54
    .branch 66 56 60,            -- 55: move blank through the counter
    .write none 57,              -- 56: remember false
    .moveLeft 58,                -- 57
    .write (some false) 59,      -- 58
    .moveRight 64,               -- 59
    .write none 61,              -- 60: remember true
    .moveLeft 62,                -- 61
    .write (some true) 59,       -- 62
    .halt false,                 -- 63
    .moveRight 65,               -- 64
    .branch 66 56 60,            -- 65
    .moveLeft 67,                -- 66: permanent | moving blanks
    .moveLeft 68,                -- 67: enter counter at MSB
    .branch 69 67 67,            -- 68: find counter start
    .moveRight 70,               -- 69
    .branch 40 71 74,            -- 70: decrement, LSB first
    .write (some true) 72,       -- 71: propagate borrow
    .moveRight 70,               -- 72
    .halt false,                 -- 73
    .write (some false) 75,      -- 74: borrow discharged
    .moveLeft 76,                -- 75
    .branch 77 75 75,            -- 76: return to counter start
    .moveRight 78,               -- 77
    .branch 79 80 83,            -- 78: zero test
    .moveRight 86,               -- 79: zero; cross permanent blank
    .moveRight 78,               -- 80
    .halt false,                 -- 81
    .halt false,                 -- 82
    .moveRight 84,               -- 83: remember a set bit
    .branch 85 83 83,            -- 84
    .moveRight 90,               -- 85: nonzero; cross permanent blank
    .branch 87 88 88,            -- 86: find moving blank, zero case
    .moveRight 89,               -- 87
    .moveRight 86,               -- 88
    .branch 40 94 98,            -- 89: final required payload cell
    .branch 91 92 92,            -- 90: find moving blank, nonzero case
    .moveRight 93,               -- 91
    .moveRight 90,               -- 92
    .branch 40 102 106,          -- 93: next required payload cell
    .write none 95,              -- 94
    .moveLeft 96,                -- 95
    .write (some false) 97,      -- 96
    .moveRight 41,               -- 97: success on new moving blank
    .write none 99,              -- 98
    .moveLeft 100,               -- 99
    .write (some true) 97,       -- 100
    .halt false,                 -- 101
    .write none 103,             -- 102
    .moveLeft 104,               -- 103
    .write (some false) 105,     -- 104
    .moveRight 110,              -- 105
    .write none 107,             -- 106
    .moveLeft 108,               -- 107
    .write (some true) 105,      -- 108
    .halt false,                 -- 109
    .moveLeft 111,               -- 110: return across processed payload
    .branch 112 110 110,         -- 111
    .moveLeft 68                 -- 112: permanent blank, enter counter
  ]⟩

theorem headerBoundaryMachine_fixed (_n _m : Nat) :
    headerBoundaryMachine = headerBoundaryMachine := rfl

/-- Physical postcondition: the data and suffix are unchanged and separated. -/
def HeaderBoundary (payload suffix : Bitstring) (config : Config) : Prop :=
  config.head = none ∧
    (∃ workspace,
      config.left = (symbols payload).reverse ++ workspace) ∧
    config.right = symbols suffix

/--
The header-sweep invariant.  `processed` is the binary prefix already moved
through the header's blank, while `remainingWidth` is represented by actual
tape cells rather than a host-side machine parameter.
-/
def HeaderSweepInvariant (remainingWidth : Nat)
    (processed remaining payload suffix : Bitstring) (config : Config) : Prop :=
  config.pc = 20 ∧
    config.left =
      (symbols processed).reverse ++
        List.replicate processed.length none ++
        List.replicate remainingWidth (some true) ++ [some false] ∧
    config.head = none ∧
    config.right = symbols (remaining ++ payload ++ suffix) ∧
    processed.length + remaining.length =
      processed.length + remainingWidth

/--
The binary-counting invariant.  The first blank is permanent and gives the
counter a runtime-addressable right boundary.  The second blank is the moving
payload boundary.  Consequently arbitrary zero/one payload cells can never be
mistaken for counter cells.
-/
def BoundaryCounterInvariant (counter processed remaining suffix : Bitstring)
    (config : Config) : Prop :=
  ∃ workspace,
    config.pc = 70 ∧
    config.left.reverse = workspace ∧
    config.head :: config.right =
      symbols counter ++ [none] ++ symbols processed ++
        none :: symbols (remaining ++ suffix) ∧
    decodeBinaryPayload counter = remaining.length

/-- Semantic domain of the primitive, independent of its implementation. -/
def BoundaryInput (input : Bitstring) : Prop :=
  ∃ n payload suffix,
    payload.length = n ∧ input = encodeNat n ++ payload ++ suffix

/-- Exact malformed characterization used by parser callers. -/
def MalformedBoundaryInput (input : Bitstring) : Prop :=
  ¬ BoundaryInput input

private def RunsWithin (bound : Nat) (first last : Config) : Prop :=
  ∃ steps, steps ≤ bound ∧
    Runs headerBoundaryMachine first steps last

private theorem RunsWithin.refl (config : Config) :
    RunsWithin 0 config config :=
  ⟨0, le_rfl, .refl _⟩

private theorem RunsWithin.trans {first middle last : Config} {m n : Nat}
    (h₁ : RunsWithin m first middle) (h₂ : RunsWithin n middle last) :
    RunsWithin (m + n) first last := by
  rcases h₁ with ⟨i, hi, hrun₁⟩
  rcases h₂ with ⟨j, hj, hrun₂⟩
  exact ⟨i + j, Nat.add_le_add hi hj, hrun₁.trans hrun₂⟩

private def decWord : Bitstring → Bitstring
  | [] => []
  | false :: rest => true :: decWord rest
  | true :: rest => false :: rest

private inductive PositiveWord : Bitstring → Prop
  | here (rest) : PositiveWord (true :: rest)
  | there (rest) : PositiveWord rest → PositiveWord (false :: rest)

private theorem decWord_length (word : Bitstring) :
    (decWord word).length = word.length := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      cases bit <;> simp [decWord, ih]

private theorem decWord_value {word : Bitstring} (positive : PositiveWord word) :
    decodeBinaryPayload (decWord word) + 1 =
      decodeBinaryPayload word := by
  induction positive with
  | here rest =>
      simp [decWord, decodeBinaryPayload, Nat.bit]
  | there rest positive ih =>
      simp [decWord, decodeBinaryPayload, Nat.bit]
      omega

private theorem positiveWord_of_value {word : Bitstring}
    (positive : 0 < decodeBinaryPayload word) :
    PositiveWord word := by
  induction word with
  | nil => simp [decodeBinaryPayload] at positive
  | cons bit word ih =>
      cases bit
      · exact .there word (ih (by
          simp [decodeBinaryPayload, Nat.bit] at positive ⊢
          omega))
      · exact .here word

private theorem replicate_cons_comm (n : Nat) (a : TapeSymbol)
    (tail : List TapeSymbol) :
    List.replicate n a ++ a :: tail =
      a :: List.replicate n a ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons a) ih

private def decTransitions : Bitstring → Nat
  | [] => 0
  | false :: rest => decTransitions rest + 5
  | true :: _ => 5

private theorem decTransitions_le (word : Bitstring) :
    decTransitions word ≤ 5 * word.length := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      cases bit <;> simp [decTransitions] <;> omega

private theorem returnAcrossBorrow (borrowed : Nat)
    (workspace right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨76, List.replicate borrowed (some true) ++ none :: workspace,
        some true, right⟩
      (2 * borrowed + 4)
      (atCells 78 (none :: workspace)
        (List.replicate (borrowed + 1) (some true) ++ right)) := by
  induction borrowed generalizing right with
  | zero =>
      simp [atCells]
      exact .next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.refl _))))
  | succ borrowed ih =>
      have first : Runs headerBoundaryMachine
          ⟨76, List.replicate (borrowed + 1) (some true) ++ none :: workspace,
            some true, right⟩ 2
          ⟨76, List.replicate borrowed (some true) ++ none :: workspace,
            some true, some true :: right⟩ := by
        simp [List.replicate_succ]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have all := first.trans (ih (some true :: right))
      convert all using 1
      · omega
      · simp [atCells, List.replicate_succ,
          replicate_cons_comm]

private theorem decrementAndReturn (borrowed : Nat) {word : Bitstring}
    (positive : PositiveWord word) (workspace tail : List TapeSymbol) :
    Runs headerBoundaryMachine
      (atCells 70
        (List.replicate borrowed (some true) ++ none :: workspace)
        (symbols word ++ none :: tail))
      (decTransitions word + 2 * borrowed)
      (atCells 78 (none :: workspace)
        (symbols (List.replicate borrowed true ++ decWord word) ++
          none :: tail)) := by
  induction positive generalizing borrowed with
  | here rest =>
      cases borrowed with
      | zero =>
          simp [atCells, symbols, decTransitions, decWord]
          exact .next (by rfl) (.next (by rfl) (.next (by rfl)
            (.next (by rfl) (.next (by rfl) (.refl _)))))
      | succ borrowed =>
          have first : Runs headerBoundaryMachine
              (atCells 70
                (List.replicate (borrowed + 1) (some true) ++
                  none :: workspace)
                (symbols (true :: rest) ++ none :: tail))
              3
              ⟨76, List.replicate borrowed (some true) ++ none :: workspace,
                some true, symbols (false :: rest) ++ none :: tail⟩ := by
            simp [atCells, symbols, List.replicate_succ]
            exact .next (by rfl) (.next (by rfl)
              (.next (by rfl) (.refl _)))
          have all := first.trans
            (returnAcrossBorrow borrowed workspace
              (symbols (false :: rest) ++ none :: tail))
          convert all using 1 <;>
            simp [decTransitions, decWord, symbols, List.replicate_succ,
              List.append_assoc] <;> omega
  | there rest positive ih =>
      have first : Runs headerBoundaryMachine
          (atCells 70
            (List.replicate borrowed (some true) ++ none :: workspace)
            (symbols (false :: rest) ++ none :: tail))
          3
          (atCells 70
            (List.replicate (borrowed + 1) (some true) ++ none :: workspace)
            (symbols rest ++ none :: tail)) := by
        simp [atCells, symbols, List.replicate_succ]
        exact .next (by rfl) (.next (by rfl)
          (.next (by rfl) (.refl _)))
      have all := first.trans (ih (borrowed + 1))
      convert all using 1
      · simp [decTransitions]
        omega
      · simp [decWord, symbols, List.replicate_succ, List.append_assoc,
          replicate_cons_comm]

private theorem word_eq_zeros {word : Bitstring}
    (zero : decodeBinaryPayload word = 0) :
    word = List.replicate word.length false := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      cases bit
      · have hword : decodeBinaryPayload word = 0 := by
          simp [decodeBinaryPayload, Nat.bit] at zero
          omega
        rw [ih hword]
        simp [List.replicate_succ]
      · simp [decodeBinaryPayload, Nat.bit] at zero

private theorem scanZeroCounter (width : Nat)
    (left tail : List TapeSymbol) :
    Runs headerBoundaryMachine
      (atCells 78 left
        (List.replicate width (some false) ++ none :: tail))
      (2 * width + 1)
      ⟨79, List.replicate width (some false) ++ left,
        none, tail⟩ := by
  induction width generalizing left with
  | zero =>
      exact .next (by rfl) (.refl _)
  | succ width ih =>
      have first : Runs headerBoundaryMachine
          (atCells 78 left
            (List.replicate (width + 1) (some false) ++ none :: tail))
          2
          (atCells 78 (some false :: left)
            (List.replicate width (some false) ++ none :: tail)) := by
        simp [atCells, List.replicate_succ]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have all := first.trans (ih (some false :: left))
      convert all using 1
      · omega
      · simp [List.replicate_succ, replicate_cons_comm]

private theorem scanPositiveCounter {word : Bitstring}
    (positive : PositiveWord word) (left tail : List TapeSymbol) :
    ∃ steps, steps = 2 * word.length + 1 ∧
      Runs headerBoundaryMachine
        (atCells 78 left (symbols word ++ none :: tail))
        steps
        ⟨85, (symbols word).reverse ++ left, none, tail⟩ := by
  induction word generalizing left with
  | nil => cases positive
  | cons bit word ih =>
      cases bit
      · cases positive with
        | there _ positive =>
            rcases ih positive (some false :: left) with
              ⟨steps, rfl, run⟩
            refine ⟨2 * (false :: word).length + 1, rfl, ?_⟩
            have first : Runs headerBoundaryMachine
                (atCells 78 left
                  (symbols (false :: word) ++ none :: tail))
                2
                (atCells 78 (some false :: left)
                  (symbols word ++ none :: tail)) := by
              simp [atCells, symbols]
              exact .next (by rfl) (.next (by rfl) (.refl _))
            convert first.trans run using 1 <;> simp [symbols] <;> omega
      · refine ⟨2 * (true :: word).length + 1, rfl, ?_⟩
        have enter : Runs headerBoundaryMachine
            (atCells 78 left
              (symbols (true :: word) ++ none :: tail))
            2
            (atCells 84 (some true :: left)
              (symbols word ++ none :: tail)) := by
          simp [atCells, symbols]
          exact .next (by rfl) (.next (by rfl) (.refl _))
        have scan : ∀ rest left,
            Runs headerBoundaryMachine
              (atCells 84 left (symbols rest ++ none :: tail))
              (2 * rest.length + 1)
              ⟨85, (symbols rest).reverse ++ left, none, tail⟩ := by
          intro rest
          induction rest with
          | nil =>
              intro left
              exact .next (by rfl) (.refl _)
          | cons next rest ih =>
              intro left
              have first : Runs headerBoundaryMachine
                  (atCells 84 left (symbols (next :: rest) ++ none :: tail))
                  2
                  (atCells 84 (some next :: left)
                    (symbols rest ++ none :: tail)) := by
                cases next <;>
                  exact .next (by rfl) (.next (by rfl) (.refl _))
              convert first.trans (ih (some next :: left)) using 1 <;>
                simp [symbols, List.append_assoc] <;> omega
        convert enter.trans (scan word (some true :: left))
          using 1 <;> simp [symbols] <;> omega

private theorem scanFinalMoving (processed : Bitstring)
    (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      (atCells 86 left (symbols processed ++ none :: right))
      (2 * processed.length + 1)
      ⟨87, (symbols processed).reverse ++ left, none, right⟩ := by
  induction processed generalizing left with
  | nil =>
      exact .next (by rfl) (.refl _)
  | cons bit processed ih =>
      have first : Runs headerBoundaryMachine
          (atCells 86 left
            (symbols (bit :: processed) ++ none :: right)) 2
          (atCells 86 (some bit :: left)
            (symbols processed ++ none :: right)) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols, List.append_assoc] <;> omega

private theorem payloadFinalAdvance (word processed : Bitstring)
    (bit : Bool) (workspace : List TapeSymbol) (suffix : Bitstring) :
    Runs headerBoundaryMachine
      ⟨79, (symbols word).reverse ++ none :: workspace, none,
        symbols processed ++ none :: some bit :: symbols suffix⟩
      (2 * processed.length + 8)
      ⟨41, some bit :: (symbols processed).reverse ++ none ::
          (symbols word).reverse ++ none :: workspace,
        none, symbols suffix⟩ := by
  have scan : Runs headerBoundaryMachine
      (atCells 86 (none :: (symbols word).reverse ++ none :: workspace)
        (symbols processed ++ none :: some bit :: symbols suffix))
      (2 * processed.length + 1)
      ⟨87, (symbols processed).reverse ++ none ::
          (symbols word).reverse ++ none :: workspace,
        none, some bit :: symbols suffix⟩ := by
    simpa [atCells, List.append_assoc] using
      scanFinalMoving processed
        (none :: (symbols word).reverse ++ none :: workspace)
        (some bit :: symbols suffix)
  have enter : Runs headerBoundaryMachine
      ⟨79, (symbols word).reverse ++ none :: workspace, none,
        symbols processed ++ none :: some bit :: symbols suffix⟩ 1
      (atCells 86 (none :: (symbols word).reverse ++ none :: workspace)
        (symbols processed ++ none :: some bit :: symbols suffix)) :=
    .next (by rfl) (.refl _)
  have finish : Runs headerBoundaryMachine
      ⟨87, (symbols processed).reverse ++ none ::
          (symbols word).reverse ++ none :: workspace,
        none, some bit :: symbols suffix⟩ 6
      ⟨41, some bit :: (symbols processed).reverse ++ none ::
          (symbols word).reverse ++ none :: workspace,
        none, symbols suffix⟩ := by
    cases bit <;>
      exact .next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))))
  convert enter.trans (scan.trans finish) using 1 <;> omega

private theorem scanNextMoving (processed : Bitstring)
    (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      (atCells 90 left (symbols processed ++ none :: right))
      (2 * processed.length + 1)
      ⟨91, (symbols processed).reverse ++ left, none, right⟩ := by
  induction processed generalizing left with
  | nil => exact .next (by rfl) (.refl _)
  | cons bit processed ih =>
      have first : Runs headerBoundaryMachine
          (atCells 90 left
            (symbols (bit :: processed) ++ none :: right)) 2
          (atCells 90 (some bit :: left)
            (symbols processed ++ none :: right)) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols, List.append_assoc] <;> omega

private theorem returnAcrossPayload (cells : Bitstring)
    (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨110, symbols cells ++ none :: left, none, right⟩
      (2 * cells.length + 2)
      ⟨112, left, none, (symbols cells).reverse ++ none :: right⟩ := by
  cases cells with
  | nil =>
      exact .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit cells =>
      have enter : Runs headerBoundaryMachine
          ⟨110, symbols (bit :: cells) ++ none :: left, none, right⟩ 1
          ⟨111, symbols cells ++ none :: left, some bit, none :: right⟩ :=
        .next (by rfl) (.refl _)
      have scan : ∀ cells bit right,
          Runs headerBoundaryMachine
            ⟨111, symbols cells ++ none :: left, some bit, right⟩
            (2 * cells.length + 3)
            ⟨112, left, none, (symbols cells).reverse ++ some bit :: right⟩ := by
        intro rest
        induction rest with
        | nil =>
            intro current right
            cases current <;>
              exact .next (by rfl) (.next (by rfl)
                (.next (by rfl) (.refl _)))
        | cons next rest ih =>
            intro current right
            have two : Runs headerBoundaryMachine
                ⟨111, symbols (next :: rest) ++ none :: left,
                  some current, right⟩ 2
                ⟨111, symbols rest ++ none :: left,
                  some next, some current :: right⟩ := by
              cases current <;>
                exact .next (by rfl) (.next (by rfl) (.refl _))
            convert two.trans (ih next (some current :: right)) using 1 <;>
              simp [symbols, List.append_assoc] <;> omega
      convert enter.trans (scan cells bit (none :: right)) using 1 <;>
        simp [symbols, List.append_assoc] <;> omega

private theorem enterCounterFromMSB (front : Bitstring) (last : Bool)
    (workspace right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨112, some last :: (symbols front).reverse ++ none :: workspace,
        none, right⟩
      (2 * (front.length + 1) + 3)
      (atCells 70 (none :: workspace)
        (symbols (front ++ [last]) ++ none :: right)) := by
  have enter : Runs headerBoundaryMachine
      ⟨112, some last :: (symbols front).reverse ++ none :: workspace,
        none, right⟩ 1
      ⟨68, (symbols front).reverse ++ none :: workspace, some last,
        none :: right⟩ :=
    .next (by rfl) (.refl _)
  have scan : ∀ cells current right,
      Runs headerBoundaryMachine
        ⟨68, symbols cells ++ none :: workspace, some current, right⟩
        (2 * (cells.length + 1) + 2)
        (atCells 70 (none :: workspace)
          (symbols (cells.reverse ++ [current]) ++ right)) := by
    intro cells
    induction cells with
    | nil =>
        intro current right
        cases current <;>
          exact .next (by rfl) (.next (by rfl)
            (.next (by rfl) (.next (by rfl) (.refl _))))
    | cons next cells ih =>
        intro current right
        have two : Runs headerBoundaryMachine
            ⟨68, symbols (next :: cells) ++ none :: workspace,
              some current, right⟩ 2
            ⟨68, symbols cells ++ none :: workspace,
              some next, some current :: right⟩ := by
          cases current <;>
            exact .next (by rfl) (.next (by rfl) (.refl _))
        convert two.trans (ih next (some current :: right)) using 1 <;>
          simp [symbols, List.append_assoc] <;> omega
  have scanned := scan front.reverse last (none :: right)
  have scanned' : Runs headerBoundaryMachine
      ⟨68, (symbols front).reverse ++ none :: workspace, some last,
        none :: right⟩
      (2 * (front.length + 1) + 2)
      (atCells 70 (none :: workspace)
        (symbols (front ++ [last]) ++ none :: right)) := by
    simpa [symbols, List.append_assoc] using scanned
  have all := enter.trans scanned'
  convert all using 1
  · omega

private theorem payloadNextAdvance (front : Bitstring) (last bit : Bool)
    (processed : Bitstring) (workspace : List TapeSymbol)
    (remaining suffix : Bitstring) :
    Runs headerBoundaryMachine
      ⟨85, (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols processed ++ none :: some bit ::
          symbols (remaining ++ suffix)⟩
      (4 * processed.length + 2 * (front.length + 1) + 15)
      (atCells 70 (none :: workspace)
        (symbols (front ++ [last]) ++ none ::
          symbols (processed ++ [bit]) ++ none ::
          symbols (remaining ++ suffix))) := by
  have enter : Runs headerBoundaryMachine
      ⟨85, (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols processed ++ none :: some bit ::
          symbols (remaining ++ suffix)⟩ 1
      (atCells 90
        (none :: (symbols (front ++ [last])).reverse ++ none :: workspace)
        (symbols processed ++ none :: some bit ::
          symbols (remaining ++ suffix))) :=
    .next (by rfl) (.refl _)
  have scan := scanNextMoving processed
    (none :: (symbols (front ++ [last])).reverse ++ none :: workspace)
    (some bit :: symbols (remaining ++ suffix))
  have scan' : Runs headerBoundaryMachine
      (atCells 90
        (none :: (symbols (front ++ [last])).reverse ++ none :: workspace)
        (symbols processed ++ none :: some bit ::
          symbols (remaining ++ suffix)))
      (2 * processed.length + 1)
      ⟨91, (symbols processed).reverse ++ none ::
          (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, some bit :: symbols (remaining ++ suffix)⟩ := by
    simpa [List.append_assoc] using scan
  have swap : Runs headerBoundaryMachine
      ⟨91, (symbols processed).reverse ++ none ::
          (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, some bit :: symbols (remaining ++ suffix)⟩ 6
      ⟨110, some bit :: (symbols processed).reverse ++ none ::
          (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols (remaining ++ suffix)⟩ := by
    cases bit <;>
      exact .next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))))
  have back := returnAcrossPayload
    (bit :: processed.reverse)
    ((symbols (front ++ [last])).reverse ++ none :: workspace)
    (symbols (remaining ++ suffix))
  have back' : Runs headerBoundaryMachine
      ⟨110, some bit :: (symbols processed).reverse ++ none ::
          (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols (remaining ++ suffix)⟩
      (2 * (processed.length + 1) + 2)
      ⟨112, (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols (processed ++ [bit]) ++ none ::
          symbols (remaining ++ suffix)⟩ := by
    simpa [symbols, List.append_assoc] using back
  have counter := enterCounterFromMSB front last workspace
    (symbols (processed ++ [bit]) ++ none :: symbols (remaining ++ suffix))
  have counter' : Runs headerBoundaryMachine
      ⟨112, (symbols (front ++ [last])).reverse ++ none :: workspace,
        none, symbols (processed ++ [bit]) ++ none ::
          symbols (remaining ++ suffix)⟩
      (2 * (front.length + 1) + 3)
      (atCells 70 (none :: workspace)
        (symbols (front ++ [last]) ++ none ::
          symbols (processed ++ [bit]) ++ none ::
          symbols (remaining ++ suffix))) := by
    simpa [symbols, List.append_assoc] using counter
  have all := enter.trans (scan'.trans (swap.trans (back'.trans counter')))
  convert all using 1
  · omega

private theorem counterPayloadRun {word payload : Bitstring}
    (hvalue : decodeBinaryPayload word = payload.length)
    (hpayload : 0 < payload.length)
    (processed suffix : Bitstring) (workspace : List TapeSymbol) :
    ∃ steps final,
      Runs headerBoundaryMachine
        (atCells 70 (none :: workspace)
          (symbols word ++ none :: symbols processed ++ none ::
            symbols (payload ++ suffix)))
        steps final ∧
      HeaderBoundary (processed ++ payload) suffix final ∧
      final.pc = 41 ∧
      steps ≤
        100 * payload.length *
          (word.length + processed.length + payload.length + 1) := by
  induction payload generalizing word processed with
  | nil =>
      simp at hpayload
  | cons bit payload ih =>
      have hpos : 0 < decodeBinaryPayload word := by
        rw [hvalue]
        simp
      have positive := positiveWord_of_value hpos
      have dec := decrementAndReturn 0 positive workspace
        (symbols processed ++ none :: symbols ((bit :: payload) ++ suffix))
      have hdecValue :
          decodeBinaryPayload (decWord word) = payload.length := by
        have := decWord_value positive
        rw [hvalue] at this
        simp at this ⊢
        omega
      by_cases htail : payload = []
      · subst payload
        have dec' : Runs headerBoundaryMachine
            (atCells 70 (none :: workspace)
              (symbols word ++ none :: symbols processed ++
                none :: some bit :: symbols suffix))
            (decTransitions word)
            (atCells 78 (none :: workspace)
              (symbols (decWord word) ++ none :: symbols processed ++
                none :: some bit :: symbols suffix)) := by
          simpa [symbols, List.append_assoc] using dec
        have hzero : decWord word =
            List.replicate (decWord word).length false :=
          word_eq_zeros (by simpa using hdecValue)
        have zeroScan := scanZeroCounter (decWord word).length
          (none :: workspace)
          (symbols processed ++ none :: some bit :: symbols suffix)
        have zeroScan' : Runs headerBoundaryMachine
            (atCells 78 (none :: workspace)
              (symbols (decWord word) ++ none :: symbols processed ++
                none :: some bit :: symbols suffix))
            (2 * (decWord word).length + 1)
            ⟨79, (symbols (decWord word)).reverse ++ none :: workspace,
              none, symbols processed ++ none :: some bit :: symbols suffix⟩ := by
          rw [hzero]
          convert zeroScan using 1 <;>
            simp [symbols, List.append_assoc]
        have finish := payloadFinalAdvance (decWord word) processed bit
          workspace suffix
        let final : Config :=
          ⟨41, some bit :: (symbols processed).reverse ++ none ::
              (symbols (decWord word)).reverse ++ none :: workspace,
            none, symbols suffix⟩
        have run := dec'.trans (zeroScan'.trans finish)
        refine ⟨decTransitions word +
            (2 * (decWord word).length + 1) +
            (2 * processed.length + 8), final, ?_, ?_, rfl, ?_⟩
        · dsimp [final]
          simpa [symbols, List.append_assoc, Nat.add_assoc] using run
        · refine ⟨rfl, ?_, rfl⟩
          refine ⟨none :: (symbols (decWord word)).reverse ++
            none :: workspace, ?_⟩
          dsimp [final]
          rw [show (symbols (processed ++ [bit])).reverse =
              some bit :: (symbols processed).reverse by simp [symbols]]
          simp [List.append_assoc]
        · have hd := decTransitions_le word
          have hl := decWord_length word
          simp only [List.length_cons, List.length_nil, Nat.add_zero]
          nlinarith
      · have htailPos : 0 < decodeBinaryPayload (decWord word) := by
          rw [hdecValue]
          exact List.length_pos_iff.mpr htail
        have nextPositive := positiveWord_of_value htailPos
        rcases scanPositiveCounter nextPositive (none :: workspace)
            (symbols processed ++ none :: some bit ::
              symbols (payload ++ suffix)) with
          ⟨scanSteps, rfl, scanned⟩
        have hwordNonempty : decWord word ≠ [] := by
          intro hempty
          simp [hempty, decodeBinaryPayload] at htailPos
        let front := (decWord word).dropLast
        let last := (decWord word).getLast hwordNonempty
        have hword : decWord word = front ++ [last] := by
          exact (List.dropLast_append_getLast hwordNonempty).symm
        have advance := payloadNextAdvance front last bit processed workspace
          payload suffix
        rw [← hword] at advance
        rcases ih hdecValue (List.length_pos_iff.mpr htail)
            (processed ++ [bit]) with
          ⟨tailSteps, final, tailRun, boundary, hpc, hbound⟩
        have run := dec.trans (scanned.trans (advance.trans tailRun))
        refine ⟨decTransitions word + (2 * (decWord word).length + 1) +
            (4 * processed.length + 2 * (front.length + 1) + 15) +
            tailSteps, final, ?_, ?_, hpc, ?_⟩
        · simpa [hword, Nat.add_assoc] using run
        · simpa [List.append_assoc] using boundary
        · have hd := decTransitions_le word
          have hlen := decWord_length word
          have hfront : front.length + 1 = word.length := by
            rw [← hlen, hword]
            simp
          have htailLen : payload.length < (bit :: payload).length := by simp
          have hbound' := hbound
          simp only [List.length_append, List.length_cons,
            List.length_singleton] at hbound' ⊢
          have htailBound : tailSteps ≤
              100 * payload.length *
                (word.length + processed.length + payload.length + 2) := by
            simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hbound'
          have hover : decTransitions word +
                (2 * (decWord word).length + 1) +
                (4 * processed.length + 2 * (front.length + 1) + 15) ≤
              100 * (word.length + processed.length + payload.length + 2) := by
            omega
          nlinarith

private theorem positiveHeaderSetup (width : Nat) (word tail : Bitstring) :
    Runs headerBoundaryMachine
      (initial
        (List.replicate (width + 1) true ++ false :: word ++ tail))
      (2 * width + 10)
      ⟨8, List.replicate (width + 1) (some true) ++ [none, some false],
        none, symbols (word ++ tail)⟩ := by
  have setup : Runs headerBoundaryMachine
      (initial
        (List.replicate (width + 1) true ++ false :: word ++ tail))
      6
      (atCells 3 [none, some false]
        (List.replicate (width + 1) (some true) ++
          some false :: symbols (word ++ tail))) := by
    simp [initial, atCells, symbols, List.map_append, List.replicate_succ]
    exact .next (by rfl) (.next (by rfl) (.next (by rfl)
      (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))))
  have scan : ∀ count left,
      Runs headerBoundaryMachine
        (atCells 6 left
          (List.replicate count (some true) ++
            some false :: symbols (word ++ tail)))
        (2 * count + 1)
        ⟨7, List.replicate count (some true) ++ left,
          some false, symbols (word ++ tail)⟩ := by
    intro count
    induction count with
    | zero =>
        intro left
        exact .next (by rfl) (.refl _)
    | succ count ih =>
        intro left
        have first : Runs headerBoundaryMachine
            (atCells 6 left
              (List.replicate (count + 1) (some true) ++
                some false :: symbols (word ++ tail)))
            2
            (atCells 6 (some true :: left)
              (List.replicate count (some true) ++
                some false :: symbols (word ++ tail))) := by
          simp [atCells, List.replicate_succ]
          exact .next (by rfl) (.next (by rfl) (.refl _))
        convert first.trans (ih (some true :: left)) using 1
        · omega
        · simp [List.replicate_succ, replicate_cons_comm]
  have enter : Runs headerBoundaryMachine
      (atCells 3 [none, some false]
        (List.replicate (width + 1) (some true) ++
          some false :: symbols (word ++ tail)))
      2
      (atCells 6 [some true, none, some false]
        (List.replicate width (some true) ++
          some false :: symbols (word ++ tail))) := by
    simp [atCells, List.replicate_succ]
    exact .next (by rfl) (.next (by rfl) (.refl _))
  have scanned := scan width [some true, none, some false]
  have finish : Runs headerBoundaryMachine
      ⟨7, List.replicate width (some true) ++
          [some true, none, some false],
        some false, symbols (word ++ tail)⟩
      1
      ⟨8, List.replicate (width + 1) (some true) ++
          [none, some false],
        none, symbols (word ++ tail)⟩ := by
    have hreorder :
        List.replicate width (some true) ++
            [some true, none, some false] =
          List.replicate (width + 1) (some true) ++
            [none, some false] := by
      rw [List.replicate_succ]
      exact replicate_cons_comm width (some true) [none, some false]
    rw [hreorder]
    exact .next (by rfl) (.refl _)
  have all := setup.trans (enter.trans (scanned.trans finish))
  convert all using 1 <;> omega

private theorem beginHeaderSweep (bit : Bool) (rest tail : Bitstring) :
    Runs headerBoundaryMachine
      ⟨8, List.replicate (rest.length + 1) (some true) ++
          [none, some false],
        none, symbols ((bit :: rest) ++ tail)⟩
      9
      ⟨20, some bit :: none ::
          List.replicate rest.length (some true) ++ [none, some false],
        none, symbols (rest ++ tail)⟩ := by
  cases bit <;>
    simp [symbols, List.replicate_succ, List.append_assoc] <;>
    exact .next (by rfl) (.next (by rfl) (.next (by rfl)
      (.next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))))))))

/--
The processed-prefix scan runs *leftward*: at pc 22/23 a non-blank cell sends
the machine to pc 25/27, which is a `moveLeft`.  So the scanned cells are
consumed from `config.left` and deposited onto `config.right`, and the scan
stops one step after the permanent blank becomes the head.
-/
private theorem scanRememberedLeft (remembered : Bool) (front : Bitstring)
    (bit : Bool) (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨if remembered then 23 else 22, symbols front ++ none :: left,
        some bit, right⟩
      (2 * (front.length + 1) + 1)
      ⟨if remembered then 26 else 24, left, none,
        (symbols front).reverse ++ some bit :: right⟩ := by
  induction front generalizing bit right with
  | nil =>
      cases remembered <;> cases bit <;>
        exact .next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))
  | cons cell front ih =>
      have first : Runs headerBoundaryMachine
          ⟨if remembered then 23 else 22,
            symbols (cell :: front) ++ none :: left, some bit, right⟩
          2
          ⟨if remembered then 23 else 22, symbols front ++ none :: left,
            some cell, some bit :: right⟩ := by
        cases remembered <;> cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (bit := cell) (right := some bit :: right))
          using 1 <;>
        simp [symbols, List.append_assoc] <;> omega

/--
The erased-width scan also runs leftward: at pc 24/26 a blank sends the machine
to pc 28/29, which is a `moveLeft`.  The scan crosses the erased width cells and
stops at pc 30 one step after the surviving width token becomes the head.
-/
private theorem scanRememberedBlanksLeft (remembered : Bool) (count : Nat)
    (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨if remembered then 26 else 24,
        List.replicate count none ++ some true :: left, none, right⟩
      (2 * count + 3)
      ⟨30, left, some true, List.replicate (count + 1) none ++ right⟩ := by
  induction count generalizing right with
  | zero =>
      cases remembered <;>
        exact .next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))
  | succ count ih =>
      have first : Runs headerBoundaryMachine
          ⟨if remembered then 26 else 24,
            List.replicate (count + 1) none ++ some true :: left, none, right⟩
          2
          ⟨if remembered then 26 else 24,
            List.replicate count none ++ some true :: left, none,
            none :: right⟩ := by
        cases remembered <;>
          simp [List.replicate_succ] <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (right := none :: right)) using 1
      · omega
      · simp [List.replicate_succ, replicate_cons_comm]

private theorem scanHeaderBlanksRight (count : Nat)
    (left right : List TapeSymbol) (bit : Bool) :
    Runs headerBoundaryMachine
      (atCells 32 left
        (List.replicate count none ++ some bit :: right))
      (2 * count + 1)
      ⟨34, List.replicate count none ++ left, some bit, right⟩ := by
  induction count generalizing left with
  | zero =>
      cases bit <;> exact .next (by rfl) (.refl _)
  | succ count ih =>
      have first : Runs headerBoundaryMachine
          (atCells 32 left
            (List.replicate (count + 1) none ++ some bit :: right))
          2
          (atCells 32 (none :: left)
            (List.replicate count none ++ some bit :: right)) := by
        simp [atCells, List.replicate_succ]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (none :: left)) using 1
      · omega
      · simp [List.replicate_succ, replicate_cons_comm]

private theorem scanHeaderWordRight (first : Bool) (rest : Bitstring)
    (left right : List TapeSymbol) :
    Runs headerBoundaryMachine
      ⟨34, left, some first, symbols rest ++ none :: right⟩
      (2 * (rest.length + 1) + 1)
      ⟨12, none :: (symbols rest).reverse ++ some first :: left,
        (right.head?.join), right.drop 1⟩ := by
  have scan : ∀ rest left,
      Runs headerBoundaryMachine
        (atCells 35 left (symbols rest ++ none :: right))
        (2 * rest.length + 2)
        ⟨12, none :: (symbols rest).reverse ++ left,
          right.head?.join, right.drop 1⟩ := by
    intro cells
    induction cells with
    | nil =>
        intro left
        cases right with
        | nil =>
            exact .next (by rfl) (.next (by rfl) (.refl _))
        | cons symbol right =>
            cases symbol <;>
              exact .next (by rfl) (.next (by rfl) (.refl _))
    | cons bit cells ih =>
        intro left
        have two : Runs headerBoundaryMachine
            (atCells 35 left (symbols (bit :: cells) ++ none :: right))
            2
            (atCells 35 (some bit :: left)
              (symbols cells ++ none :: right)) := by
          cases bit <;>
            exact .next (by rfl) (.next (by rfl) (.refl _))
        convert two.trans (ih (some bit :: left)) using 1 <;>
          simp [symbols, List.append_assoc] <;> omega
  have enter : Runs headerBoundaryMachine
      ⟨34, left, some first, symbols rest ++ none :: right⟩ 1
      (atCells 35 (some first :: left) (symbols rest ++ none :: right)) :=
    .next (by rfl) (.refl _)
  convert enter.trans (scan rest (some first :: left)) using 1 <;>
    omega

/--
Exact positive-count theorem for the counter phase.  This is the induction
used by the contiguous-header theorem: the counter is the runtime
`Nat.bits n`, not a source-indexed machine or a host-created payload marker.
-/
theorem headerBoundary_positive_counter (n : Nat) (hn : 0 < n)
    (payload suffix : Bitstring) (hlen : payload.length = n)
    (workspace : List TapeSymbol) :
    ∃ steps final,
      Runs headerBoundaryMachine
        (atCells 70 (none :: workspace)
          (symbols (Nat.bits n) ++ none :: none ::
            symbols (payload ++ suffix)))
        steps final ∧
      HeaderBoundary payload suffix final ∧
      final.pc = 41 ∧
      steps ≤
        100 * n * ((Nat.bits n).length + n + 1) := by
  have hvalue : decodeBinaryPayload (Nat.bits n) = payload.length := by
    rw [decodeBinaryPayload_bits, hlen]
  rcases counterPayloadRun hvalue (by simpa [hlen] using hn)
      [] suffix workspace with
    ⟨steps, final, run, boundary, hpc, hbound⟩
  refine ⟨steps, final, ?_, by simpa using boundary, hpc, ?_⟩
  · simpa [symbols, List.append_assoc] using run
  · simpa [hlen] using hbound

/-- A conservative quadratic fuel bound in the total contiguous input size. -/
def headerBoundaryTime (length : Nat) : Nat := 40 * (length + 1) ^ 2

theorem headerBoundaryTime_polynomial : IsPolynomial headerBoundaryTime :=
  .bounded 120 2 (fun n => by
    simp [headerBoundaryTime]
    nlinarith)

private theorem unterminatedRun (width : Nat) :
    Runs headerBoundaryMachine (initial (List.replicate width true))
      (2 * width + 7)
      ⟨40, List.replicate width (some true) ++ [none, some false],
        none, []⟩ := by
  have setup : Runs headerBoundaryMachine
      (initial (List.replicate width true)) 6
      (atCells 3 [none, some false]
        (List.replicate width (some true))) := by
    cases width with
    | zero =>
        exact .next (by rfl) (.next (by rfl) (.next (by rfl)
          (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))))
    | succ width =>
        simp [initial, atCells, List.replicate_succ, List.map_replicate]
        exact .next (by rfl) (.next (by rfl) (.next (by rfl)
          (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))))
  have scan : ∀ width left,
      Runs headerBoundaryMachine
        (atCells 6 left (List.replicate width (some true)))
        (2 * width + 1)
        ⟨40, List.replicate width (some true) ++ left, none, []⟩ := by
    intro count
    induction count with
    | zero =>
        intro left
        simp [atCells]
        exact .next (by rfl) (.refl _)
    | succ count ih =>
        intro left
        have first : Runs headerBoundaryMachine
            (atCells 6 left
              (List.replicate (count + 1) (some true))) 2
            (atCells 6 (some true :: left)
              (List.replicate count (some true))) := by
          simp [atCells, List.replicate_succ]
          exact .next (by rfl) (.next (by rfl) (.refl _))
        have tail := ih (some true :: left)
        have hreorder :
            List.replicate count (some true) ++ some true :: left =
              some true :: List.replicate count (some true) ++ left := by
          have hrep := List.replicate_append_replicate
            (n := count) (m := 1) (a := some true)
          have happ := congrArg (fun cells => cells ++ left) hrep
          simpa [List.replicate_succ, List.append_assoc] using happ
        convert first.trans tail using 1
        · omega
        · simp [hreorder, List.replicate_succ]
  cases width with
  | zero =>
      have reject : Runs headerBoundaryMachine
          (atCells 3 [none, some false] []) 1
          ⟨40, [none, some false], none, []⟩ :=
        .next (by rfl) (.refl _)
      simpa using setup.trans reject
  | succ width =>
      have enter : Runs headerBoundaryMachine
          (atCells 3 [none, some false]
            (List.replicate (width + 1) (some true))) 2
          (atCells 6 [some true, none, some false]
            (List.replicate width (some true))) := by
        simp [atCells, List.replicate_succ]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have tail := scan width [some true, none, some false]
      have all := setup.trans (enter.trans tail)
      have hreorder :
          List.replicate width (some true) ++
              [some true, none, some false] =
            some true :: List.replicate width (some true) ++
              [none, some false] := by
        have hrep := List.replicate_append_replicate
          (n := width) (m := 1) (a := some true)
        have happ := congrArg
          (fun cells => cells ++ [none, some false]) hrep
        simpa [List.replicate_succ, List.append_assoc] using happ
      convert all using 1
      · omega
      · simp [hreorder, List.replicate_succ]

/-- Every all-one input is an unterminated self-delimiting header and rejects. -/
theorem headerBoundary_rejects_unterminated (width : Nat) :
    eval headerBoundaryMachine (2 * width + 8)
      (List.replicate width true) =
    some ⟨false, false :: List.replicate width true, 2 * width + 8⟩ := by
  have run := unterminatedRun width
  have halt : step headerBoundaryMachine
      ⟨40, List.replicate width (some true) ++ [none, some false],
        none, []⟩ =
      .error
        ⟨false, false :: List.replicate width true, 0⟩ := by
    simp [step, headerBoundaryMachine, tapeOutput]
  simpa [eval] using run.halt halt (elapsed := 0)

/-- The width-zero header creates the boundary without inspecting the suffix. -/
theorem headerBoundary_zero_run (suffix : Bitstring) :
    Runs headerBoundaryMachine (initial (encodeNat 0 ++ suffix)) 8
      ⟨41, [none, some false], none, symbols suffix⟩ := by
  cases suffix with
  | nil =>
      exact .next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.next (by rfl)
          (.next (by rfl) (.next (by rfl) (.refl _))))))))
  | cons bit suffix =>
      cases bit <;>
        exact .next (by rfl) (.next (by rfl) (.next (by rfl)
          (.next (by rfl) (.next (by rfl) (.next (by rfl)
            (.next (by rfl) (.next (by rfl) (.refl _))))))))

theorem headerBoundary_zero_contract (suffix : Bitstring) :
    HeaderBoundary [] suffix ⟨41, [none, some false], none, symbols suffix⟩ ∧
      eval headerBoundaryMachine 9 (encodeNat 0 ++ suffix) =
        some ⟨true, false :: suffix, 9⟩ := by
  constructor
  · exact ⟨rfl, ⟨[none, some false], by simp [symbols]⟩, rfl⟩
  · have run := headerBoundary_zero_run suffix
    have halt : step headerBoundaryMachine
        ⟨41, [none, some false], none, symbols suffix⟩ =
        .error ⟨true, false :: suffix, 0⟩ := by
      simp [step, headerBoundaryMachine, tapeOutput, symbols]
    simpa [eval] using run.halt halt (elapsed := 0)

end AvgCaseMls.Foundation.TapeMacros
