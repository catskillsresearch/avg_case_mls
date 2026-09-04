import AvgCaseMls.Foundation.Universal.Dispatch
import AvgCaseMls.Foundation.TapeMacros.Assembler

/-!
# Fixed runtime counters and program-counter updates

The monotone prefix marking used by `markedProgramAt` is useful for a single
lookup but cannot represent a backward edge after execution.  Runtime state
therefore uses a separate two-track one-hot table.  Each logical entry is the
pair `(current, successor)`.  A fixed rewrite sweep copies the successor track
to the current track; instruction records remain immutable.

All machines below are closed constants over the six base instructions.
-/

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation
open AvgCaseMls.Foundation.TapeMacros

/-- Interleave two equal-width Boolean tracks. -/
def interleave : Bitstring → Bitstring → Bitstring
  | first :: rest, second :: tail =>
      first :: second :: interleave rest tail
  | _, _ => []

def oneHot (width pc : Nat) : Bitstring :=
  (List.range width).map fun index => index = pc

@[simp] theorem oneHot_length (width pc : Nat) :
    (oneHot width pc).length = width := by
  simp [oneHot]

theorem oneHot_getElem (width pc index : Nat) (hi : index < width) :
    (oneHot width pc)[index]'(by simp [oneHot, hi]) = (index = pc) := by
  simp [oneHot, hi]

/--
The mutable prefix of a runtime serialization.  The blank after the table is
permanent; `records` contains the immutable instruction records and the
simulated work tape may follow after another delimiter.
-/
def runtimeLayout (current successor : Bitstring)
    (records : List TapeSymbol) : List TapeSymbol :=
  (interleave current successor).map some ++ none :: records

/-- Three adjacent runtime tracks, without the trailing delimiter. -/
def runtimeTracks : Bitstring → Bitstring → Bitstring → List TapeSymbol
  | current :: currents, scratch :: scratches, decoded :: decodeds =>
      some current :: some scratch :: some decoded ::
        runtimeTracks currents scratches decodeds
  | _, _, _ => []

/-- Three-track runtime table before successor materialization. -/
def runtimeDecodedLayout (current scratch decoded : Bitstring)
    (records : List TapeSymbol) : List TapeSymbol :=
  runtimeTracks current scratch decoded ++ none :: records

/--
Fixed sweep copying runtime-decoded successor bits onto the mutable scratch
track.  The current-PC and decoded tracks are preserved.
-/
def successorMaterializeMachine : Machine :=
  ⟨#[
    .branch 10 1 1,
    .moveRight 2,
    .moveRight 3,
    .branch 10 4 7,
    .moveLeft 5,
    .write (some false) 6,
    .moveRight 9,
    .moveLeft 8,
    .write (some true) 6,
    .moveRight 0,
    .halt true
  ]⟩

private theorem materializeDecoded (current scratch decoded : Bitstring)
    (h₁ : current.length = scratch.length)
    (h₂ : current.length = decoded.length)
    (left records : List TapeSymbol) :
    Runs successorMaterializeMachine
      (physicalConfig 0 left
        (runtimeDecodedLayout current scratch decoded records))
      (8 * current.length + 1)
      ⟨10,
        (runtimeTracks current decoded decoded).reverse ++ left,
        none, records⟩ := by
  induction current generalizing scratch decoded left with
  | nil =>
      have hscratch : scratch = [] := List.eq_nil_of_length_eq_zero (by
        simpa using h₁.symm)
      have hdecoded : decoded = [] := List.eq_nil_of_length_eq_zero (by
        simpa using h₂.symm)
      subst scratch
      subst decoded
      simpa [runtimeDecodedLayout, runtimeTracks, physicalConfig] using
        (Runs.next (machine := successorMaterializeMachine)
          (by rfl) (Runs.refl _))
  | cons current currents ih =>
      cases scratch with
      | nil => simp at h₁
      | cons scratch scratches =>
          cases decoded with
          | nil => simp at h₂
          | cons decoded decodeds =>
              have ht₁ : currents.length = scratches.length := by
                simpa using h₁
              have ht₂ : currents.length = decodeds.length := by
                simpa using h₂
              have cycle : Runs successorMaterializeMachine
                  (physicalConfig 0 left
                    (runtimeDecodedLayout (current :: currents)
                      (scratch :: scratches) (decoded :: decodeds) records))
                  8
                  (physicalConfig 0
                    ([some decoded, some decoded, some current] ++ left)
                    (runtimeDecodedLayout currents scratches decodeds
                      records)) := by
                cases current <;> cases scratch <;> cases decoded
                all_goals
                  exact .next (by rfl)
                    (.next (by rfl)
                      (.next (by rfl)
                        (.next (by rfl)
                          (.next (by rfl)
                            (.next (by rfl)
                              (.next (by rfl)
                                (.next (by rfl) (.refl _))))))))
              have tailRun := ih scratches decodeds ht₁ ht₂
                ([some decoded, some decoded, some current] ++ left)
              have all := cycle.trans tailRun
              convert all using 1
              · simp
                omega
              · simp [runtimeDecodedLayout, runtimeTracks, List.append_assoc]

def successorMaterializeTime (width : Nat) : Nat := 8 * width + 2

theorem successorMaterializeTime_polynomial :
    IsPolynomial successorMaterializeTime :=
  .bounded 8 1 (fun n => by simp [successorMaterializeTime])

/--
Decoded successor bits, rather than a prepopulated scratch track, determine
the materialized marker track.
-/
theorem successorMaterialize_contract
    (current scratch decoded : Bitstring)
    (h₁ : current.length = scratch.length)
    (h₂ : current.length = decoded.length)
    (records : List TapeSymbol) :
    evalFrom successorMaterializeMachine
      (successorMaterializeTime current.length)
      (physicalConfig 0 []
        (runtimeDecodedLayout current scratch decoded records)) 0 =
      some ⟨true,
        (runtimeTracks current decoded decoded).filterMap id ++
          records.filterMap id,
        successorMaterializeTime current.length⟩ := by
  have run : Runs successorMaterializeMachine
      (physicalConfig 0 []
        (runtimeDecodedLayout current scratch decoded records))
      (8 * current.length + 1)
      ⟨10,
        (runtimeTracks current decoded decoded).reverse,
        none, records⟩ := by
    simpa using materializeDecoded current scratch decoded h₁ h₂ [] records
  have halt : step successorMaterializeMachine
      ⟨10,
        (runtimeTracks current decoded decoded).reverse,
        none, records⟩ =
      .error ⟨true,
        (runtimeTracks current decoded decoded).filterMap id ++
          records.filterMap id, 0⟩ := by
    simp [step, successorMaterializeMachine, tapeOutput,
      List.filterMap_reverse]
  simpa [successorMaterializeTime] using run.halt halt (elapsed := 0)

/-- Locate the set bit on the current-PC track, skipping successor cells. -/
def runtimeLookupMachine : Machine :=
  ⟨#[
    .branch 6 1 5,
    .moveRight 2,
    .moveRight 0,
    .jump 6,
    .jump 6,
    .halt true,
    .halt false
  ]⟩

private theorem runtimeLookupPrefix (before scratch : Bitstring)
    (hlen : before.length = scratch.length)
    (selectedScratch : Bool) (after left : List TapeSymbol) :
    Runs runtimeLookupMachine
      (physicalConfig 0 left
        ((interleave (List.replicate before.length false) scratch).map some ++
          some true :: some selectedScratch :: after))
      (3 * before.length + 1)
      ⟨5,
        ((interleave (List.replicate before.length false) scratch).map
          some).reverse ++ left,
        some true,
        some selectedScratch :: after⟩ := by
  induction before generalizing scratch left with
  | nil =>
      have : scratch = [] := List.eq_nil_of_length_eq_zero (by
        simpa using hlen.symm)
      subst scratch
      simpa [interleave, physicalConfig] using
        (Runs.next (machine := runtimeLookupMachine) (by rfl) (Runs.refl _))
  | cons bit before ih =>
      cases scratch with
      | nil => simp at hlen
      | cons scratchBit scratch =>
          have htail : before.length = scratch.length := by simpa using hlen
          have first : Runs runtimeLookupMachine
              (physicalConfig 0 left
                ((interleave (List.replicate (bit :: before).length false)
                    (scratchBit :: scratch)).map some ++
                  some true :: some selectedScratch :: after))
              3
              (physicalConfig 0
                ([some scratchBit, some false] ++ left)
                ((interleave (List.replicate before.length false) scratch).map
                    some ++ some true :: some selectedScratch :: after)) := by
            simp [interleave, physicalConfig, List.replicate_succ]
            exact .next (by rfl) (.next (by rfl)
              (.next (by rfl) (.refl _)))
          have tailRun := ih scratch htail
            ([some scratchBit, some false] ++ left)
          have all := first.trans tailRun
          convert all using 1 <;>
            simp [interleave, List.replicate_succ, physicalConfig,
              List.append_assoc] <;> omega

/-- Locate the table entry selected by an arbitrary runtime PC. -/
theorem runtimeLookup_pc (pc : Nat) (scratchPrefix : Bitstring)
    (hlen : scratchPrefix.length = pc) (selectedScratch : Bool)
    (after : List TapeSymbol) :
    Runs runtimeLookupMachine
      (physicalConfig 0 []
        ((interleave (List.replicate pc false) scratchPrefix).map some ++
          some true :: some selectedScratch :: after))
      (3 * pc + 1)
      ⟨5,
        ((interleave (List.replicate pc false) scratchPrefix).map some).reverse,
        some true, some selectedScratch :: after⟩ := by
  simpa [hlen] using runtimeLookupPrefix scratchPrefix scratchPrefix
    (by rfl) selectedScratch after []

def runtimeLookupTime (pc : Nat) : Nat := 3 * pc + 1

theorem runtimeLookupTime_polynomial : IsPolynomial runtimeLookupTime :=
  .bounded 3 1 (fun n => by simp [runtimeLookupTime])

/--
Copy one adjacent successor bit to its current-PC bit and advance to the next
pair.  On the delimiter the machine halts.  This is the runtime marker update;
its code is independent of both table width and successor.
-/
def markerRewriteMachine : Machine :=
  ⟨#[
    .branch 9 1 1,
    .moveRight 2,
    .branch 9 3 6,
    .moveLeft 4,
    .write (some false) 5,
    .moveRight 8,
    .moveLeft 7,
    .write (some true) 5,
    .moveRight 0,
    .halt true
  ]⟩

private theorem rewriteInterleave (current successor : Bitstring)
    (hlen : current.length = successor.length)
    (left suffix : List TapeSymbol) :
    Runs markerRewriteMachine
      (physicalConfig 0 left
        ((interleave current successor).map some ++ none :: suffix))
      (7 * current.length + 1)
      ⟨9, ((interleave successor successor).map some).reverse ++ left,
        none, suffix⟩ := by
  induction current generalizing successor left with
  | nil =>
      have : successor = [] := List.eq_nil_of_length_eq_zero (by
        simpa using hlen.symm)
      subst successor
      simpa [interleave, physicalConfig] using
        (Runs.next (machine := markerRewriteMachine) (by rfl) (Runs.refl _))
  | cons current rest ih =>
      cases successor with
      | nil => simp at hlen
      | cons next tail =>
          have htail : rest.length = tail.length := by simpa using hlen
          have cycle : Runs markerRewriteMachine
              (physicalConfig 0 left
                ((interleave (current :: rest) (next :: tail)).map some ++
                  none :: suffix))
              7
              (physicalConfig 0 ([some next, some next] ++ left)
                ((interleave rest tail).map some ++ none :: suffix)) := by
            cases current <;> cases next
            all_goals
              exact .next (by rfl)
                (.next (by rfl)
                  (.next (by rfl)
                    (.next (by rfl)
                      (.next (by rfl)
                        (.next (by rfl)
                          (.next (by rfl) (.refl _)))))))
          have tailRun := ih tail htail ([some next, some next] ++ left)
          have all := cycle.trans tailRun
          convert all using 1
          · simp
            omega
          · simp [interleave, List.append_assoc]

def markerRewriteTime (width : Nat) : Nat := 7 * width + 2

theorem markerRewriteTime_polynomial : IsPolynomial markerRewriteTime :=
  .bounded 7 1 (fun n => by simp [markerRewriteTime])

/-- Exact arbitrary-successor marker rewrite, preserving immutable records. -/
theorem markerRewrite_contract (current successor : Bitstring)
    (hlen : current.length = successor.length)
    (records : List TapeSymbol) :
    evalFrom markerRewriteMachine (markerRewriteTime current.length)
      (physicalConfig 0 []
        (runtimeLayout current successor records)) 0 =
      some ⟨true,
        (interleave successor successor) ++ records.filterMap id,
        markerRewriteTime current.length⟩ := by
  have run : Runs markerRewriteMachine
      (physicalConfig 0 []
        ((interleave current successor).map some ++ none :: records))
      (7 * current.length + 1)
      ⟨9, ((interleave successor successor).map some).reverse,
        none, records⟩ := by
    simpa using rewriteInterleave current successor hlen [] records
  have halt : step markerRewriteMachine
      ⟨9, ((interleave successor successor).map some).reverse,
        none, records⟩ =
      .error ⟨true,
        (interleave successor successor) ++ records.filterMap id, 0⟩ := by
    simp [step, markerRewriteMachine, tapeOutput, List.filterMap_reverse]
  simpa [markerRewriteTime, runtimeLayout] using run.halt halt (elapsed := 0)

/-- In particular, a runtime PC can move to any in-range decoded successor. -/
theorem markerRewrite_oneHot (width pc successor : Nat)
    (records : List TapeSymbol) :
    evalFrom markerRewriteMachine (markerRewriteTime width)
      (physicalConfig 0 []
        (runtimeLayout (oneHot width pc) (oneHot width successor) records)) 0 =
      some ⟨true,
        interleave (oneHot width successor) (oneHot width successor) ++
          records.filterMap id,
        markerRewriteTime width⟩ := by
  simpa using markerRewrite_contract (oneHot width pc)
    (oneHot width successor) (by simp) records

/--
Scan the unary width prefix of `encodeNat`, landing on the first payload bit.
This is the fixed unary/binary counter boundary scanner.
-/
def binaryCounterScanMachine : Machine :=
  ⟨#[
    .branch 4 1 3,
    .moveRight 2,
    .halt true,
    .moveRight 0,
    .halt false
  ]⟩

theorem binaryCounterScan (width : Nat) (payload : Bitstring)
    (left suffix : List TapeSymbol) :
    Runs binaryCounterScanMachine
      (physicalConfig 0 left
        ((List.replicate width true ++ false :: payload).map some ++ suffix))
      (2 * width + 2)
      (physicalConfig 2
        (some false :: List.replicate width (some true) ++ left)
        (payload.map some ++ suffix)) := by
  induction width generalizing left with
  | zero =>
      simp [physicalConfig]
      exact .next (by rfl) (.next (by rfl) (.refl _))
  | succ width ih =>
      have first : Runs binaryCounterScanMachine
          (physicalConfig 0 left
            ((List.replicate (width + 1) true ++ false :: payload).map some ++
              suffix))
          2
          (physicalConfig 0 (some true :: left)
            ((List.replicate width true ++ false :: payload).map some ++
              suffix)) := by
        simp [List.replicate_succ, physicalConfig]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have all := first.trans (ih (some true :: left))
      have hreorder :
          List.replicate width (some true) ++ some true :: left =
            some true :: List.replicate width (some true) ++ left := by
        calc
          _ = (List.replicate width (some true) ++ [some true]) ++ left := by
            simp
          _ = List.replicate (width + 1) (some true) ++ left := by
            have hrep := List.replicate_append_replicate
              (n := width) (m := 1) (a := some true)
            simpa using congrArg (fun xs => xs ++ left) hrep
          _ = _ := by rw [List.replicate_succ]
      convert all using 1
      · omega
      · simp [List.replicate_succ, hreorder]

theorem binaryCounterScan_encodeNat (value : Nat)
    (left suffix : List TapeSymbol) :
    Runs binaryCounterScanMachine
      (physicalConfig 0 left ((encodeNat value).map some ++ suffix))
      (2 * (Nat.bits value).length + 2)
      (physicalConfig 2
        (some false ::
          List.replicate (Nat.bits value).length (some true) ++ left)
        ((Nat.bits value).map some ++ suffix)) := by
  simpa [encodeNat, List.map_append] using
    binaryCounterScan (Nat.bits value).length (Nat.bits value) left suffix

def binaryCounterScanTime (width : Nat) : Nat := 2 * width + 2

theorem binaryCounterScanTime_polynomial :
    IsPolynomial binaryCounterScanTime :=
  .bounded 2 1 (fun n => by simp [binaryCounterScanTime])

/--
Fixed invocation-fuel parser.  The runtime wire format is `1^fuel 0`; this
machine scans the unary payload and replaces its terminating zero by the blank
that terminates the canonical fuel segment.  Encountering a blank before the
zero reaches the rejecting state.
-/
def invocationFuelParserMachine : Machine :=
  ⟨#[
    .branch 4 1 2,
    .write none 3,
    .moveRight 0,
    .halt true,
    .halt false
  ]⟩

private theorem invocationFuelParser_run (fuel : Nat)
    (left suffix : List TapeSymbol) :
    Runs invocationFuelParserMachine
      (physicalConfig 0 left
        ((encodeInvocationFuel fuel).map some ++ suffix))
      (2 * fuel + 2)
      ⟨3, List.replicate fuel (some true) ++ left, none, suffix⟩ := by
  induction fuel generalizing left with
  | zero =>
      simpa [encodeInvocationFuel, physicalConfig] using
        (Runs.next (machine := invocationFuelParserMachine) (by rfl)
          (Runs.next (by rfl) (Runs.refl _)))
  | succ fuel ih =>
      have first : Runs invocationFuelParserMachine
          (physicalConfig 0 left
            ((encodeInvocationFuel (fuel + 1)).map some ++ suffix))
          2
          (physicalConfig 0 (some true :: left)
            ((encodeInvocationFuel fuel).map some ++ suffix)) := by
        simp [encodeInvocationFuel, List.replicate_succ, physicalConfig]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have all := first.trans (ih (some true :: left))
      convert all using 1
      · omega
      · have hrep := List.replicate_append_replicate
          (n := fuel) (m := 1) (a := some true)
        simpa [List.replicate_succ, List.append_assoc] using
          congrArg (fun cells => cells ++ left) hrep.symm

def invocationFuelParserTime (fuel : Nat) : Nat := 2 * fuel + 3

theorem invocationFuelParserTime_polynomial :
    IsPolynomial invocationFuelParserTime :=
  .bounded 3 1 (fun n => by simp [invocationFuelParserTime]; omega)

theorem invocationFuelParser_contract (fuel : Nat)
    (suffix : List TapeSymbol) :
    evalFrom invocationFuelParserMachine (invocationFuelParserTime fuel)
      (physicalConfig 0 []
        ((encodeInvocationFuel fuel).map some ++ suffix)) 0 =
      some ⟨true,
        List.replicate fuel true ++ suffix.filterMap id,
        invocationFuelParserTime fuel⟩ := by
  have run : Runs invocationFuelParserMachine
      (physicalConfig 0 []
        ((encodeInvocationFuel fuel).map some ++ suffix))
      (2 * fuel + 2)
      ⟨3, List.replicate fuel (some true), none, suffix⟩ := by
    simpa using invocationFuelParser_run fuel [] suffix
  have halt : step invocationFuelParserMachine
      ⟨3, List.replicate fuel (some true), none, suffix⟩ =
      .error
        ⟨true, List.replicate fuel true ++ suffix.filterMap id, 0⟩ := by
    simp [step, invocationFuelParserMachine, tapeOutput,
      List.filterMap_reverse]
  simpa [invocationFuelParserTime] using run.halt halt (elapsed := 0)

private theorem invocationFuelParser_unterminated_run (fuel : Nat)
    (left : List TapeSymbol) :
    Runs invocationFuelParserMachine
      (physicalConfig 0 left (List.replicate fuel (some true)))
      (2 * fuel + 1)
      ⟨4, List.replicate fuel (some true) ++ left, none, []⟩ := by
  induction fuel generalizing left with
  | zero =>
      simpa [physicalConfig] using
        (Runs.next (machine := invocationFuelParserMachine)
          (by rfl) (Runs.refl _))
  | succ fuel ih =>
      have first : Runs invocationFuelParserMachine
          (physicalConfig 0 left
            (List.replicate (fuel + 1) (some true)))
          2
          (physicalConfig 0 (some true :: left)
            (List.replicate fuel (some true))) := by
        simp [List.replicate_succ, physicalConfig]
        exact .next (by rfl) (.next (by rfl) (.refl _))
      have all := first.trans (ih (some true :: left))
      convert all using 1
      · omega
      · have hrep := List.replicate_append_replicate
          (n := fuel) (m := 1) (a := some true)
        simpa [List.replicate_succ, List.append_assoc] using
          congrArg (fun cells => cells ++ left) hrep.symm

theorem invocationFuelParser_rejects_unterminated (fuel : Nat) :
    eval invocationFuelParserMachine (2 * fuel + 2)
      (List.replicate fuel true) =
    some ⟨false, List.replicate fuel true, 2 * fuel + 2⟩ := by
  have run : Runs invocationFuelParserMachine
      (initial (List.replicate fuel true))
      (2 * fuel + 1)
      ⟨4, List.replicate fuel (some true), none, []⟩ := by
    have hinitial :
        initial (List.replicate fuel true) =
          physicalConfig 0 [] (List.replicate fuel (some true)) := by
      cases fuel <;>
        simp [initial, physicalConfig, List.replicate_succ,
          List.map_replicate]
    rw [hinitial]
    simpa using invocationFuelParser_unterminated_run fuel []
  have halt : step invocationFuelParserMachine
      ⟨4, List.replicate fuel (some true), none, []⟩ =
      .error ⟨false, List.replicate fuel true, 0⟩ := by
    simp [step, invocationFuelParserMachine, tapeOutput]
  simpa [eval] using run.halt halt (elapsed := 0)

/--
Unary fuel loop.  Every iteration erases one fuel cell.  Blank means zero;
`false` is an early simulated-halt marker.  Both paths stop in fixed states.
-/
def unaryFuelMachine : Machine :=
  ⟨#[
    .branch 3 4 1,
    .write none 2,
    .moveRight 0,
    .halt true,
    .halt true
  ]⟩

private theorem consumeUnaryFuel (fuel : Nat) (left suffix : List TapeSymbol) :
    Runs unaryFuelMachine
      (physicalConfig 0 left
        (List.replicate fuel (some true) ++ none :: suffix))
      (3 * fuel + 1)
      ⟨3, List.replicate fuel none ++ left, none, suffix⟩ := by
  induction fuel generalizing left with
  | zero =>
      simpa [physicalConfig] using
        (Runs.next (machine := unaryFuelMachine) (by rfl) (Runs.refl _))
  | succ fuel ih =>
      have first : Runs unaryFuelMachine
          (physicalConfig 0 left
            (List.replicate (fuel + 1) (some true) ++ none :: suffix))
          3
          (physicalConfig 0 (none :: left)
            (List.replicate fuel (some true) ++ none :: suffix)) := by
        simp [List.replicate_succ, physicalConfig]
        exact .next (by rfl) (.next (by rfl)
          (.next (by rfl) (.refl _)))
      have all := first.trans (ih (none :: left))
      have hreorder :
          List.replicate fuel none ++ none :: left =
            none :: List.replicate fuel none ++ left := by
        calc
          _ = (List.replicate fuel none ++ [none]) ++ left := by simp
          _ = List.replicate (fuel + 1) none ++ left := by
            have hrep := List.replicate_append_replicate
              (n := fuel) (m := 1) (a := (none : TapeSymbol))
            simpa using congrArg (fun xs => xs ++ left) hrep
          _ = _ := by rw [List.replicate_succ]
      convert all using 1
      · omega
      · simp [List.replicate_succ, hreorder]

private theorem consumeUnaryUntilHalt (fuel : Nat)
    (left suffix : List TapeSymbol) :
    Runs unaryFuelMachine
      (physicalConfig 0 left
        (List.replicate fuel (some true) ++ some false :: suffix))
      (3 * fuel + 1)
      ⟨4, List.replicate fuel none ++ left, some false, suffix⟩ := by
  induction fuel generalizing left with
  | zero =>
      simpa [physicalConfig] using
        (Runs.next (machine := unaryFuelMachine) (by rfl) (Runs.refl _))
  | succ fuel ih =>
      have first : Runs unaryFuelMachine
          (physicalConfig 0 left
            (List.replicate (fuel + 1) (some true) ++ some false :: suffix))
          3
          (physicalConfig 0 (none :: left)
            (List.replicate fuel (some true) ++ some false :: suffix)) := by
        simp [List.replicate_succ, physicalConfig]
        exact .next (by rfl) (.next (by rfl)
          (.next (by rfl) (.refl _)))
      have all := first.trans (ih (none :: left))
      have hreorder :
          List.replicate fuel none ++ none :: left =
            none :: List.replicate fuel none ++ left := by
        calc
          _ = (List.replicate fuel none ++ [none]) ++ left := by simp
          _ = List.replicate (fuel + 1) none ++ left := by
            have hrep := List.replicate_append_replicate
              (n := fuel) (m := 1) (a := (none : TapeSymbol))
            simpa using congrArg (fun xs => xs ++ left) hrep
          _ = _ := by rw [List.replicate_succ]
      convert all using 1
      · omega
      · simp [List.replicate_succ, hreorder]

def unaryFuelTime (fuel : Nat) : Nat := 3 * fuel + 2

theorem unaryFuelTime_polynomial : IsPolynomial unaryFuelTime :=
  .bounded 3 1 (fun n => by simp [unaryFuelTime])

/-- Repeatedly decrement runtime fuel and halt exactly when it reaches zero. -/
theorem unaryFuel_zero_contract (fuel : Nat) (suffix : List TapeSymbol) :
    evalFrom unaryFuelMachine (unaryFuelTime fuel)
      (physicalConfig 0 []
        (List.replicate fuel (some true) ++ none :: suffix)) 0 =
      some ⟨true, suffix.filterMap id, unaryFuelTime fuel⟩ := by
  have run : Runs unaryFuelMachine
      (physicalConfig 0 []
        (List.replicate fuel (some true) ++ none :: suffix))
      (3 * fuel + 1)
      ⟨3, List.replicate fuel none, none, suffix⟩ := by
    simpa using consumeUnaryFuel fuel [] suffix
  have halt : step unaryFuelMachine
      ⟨3, List.replicate fuel none, none, suffix⟩ =
      .error ⟨true, suffix.filterMap id, 0⟩ := by
    simp [step, unaryFuelMachine, tapeOutput]
  simpa [unaryFuelTime] using run.halt halt (elapsed := 0)

/-- A simulated halt marker terminates the same loop before zero dispatch. -/
theorem unaryFuel_halt_contract (fuel : Nat) (suffix : List TapeSymbol) :
    evalFrom unaryFuelMachine (unaryFuelTime fuel)
      (physicalConfig 0 []
        (List.replicate fuel (some true) ++ some false :: suffix)) 0 =
      some ⟨true, false :: suffix.filterMap id, unaryFuelTime fuel⟩ := by
  have run : Runs unaryFuelMachine
      (physicalConfig 0 []
        (List.replicate fuel (some true) ++ some false :: suffix))
      (3 * fuel + 1)
      ⟨4, List.replicate fuel none, some false, suffix⟩ := by
    simpa using consumeUnaryUntilHalt fuel [] suffix
  have halt : step unaryFuelMachine
      ⟨4, List.replicate fuel none, some false, suffix⟩ =
      .error ⟨true, false :: suffix.filterMap id, 0⟩ := by
    simp [step, unaryFuelMachine, tapeOutput]
  simpa [unaryFuelTime] using run.halt halt (elapsed := 0)

theorem canonical_pcBits_eq_oneHot (image : CanonicalImage) :
    image.pcBits = oneHot image.machine.code.size image.pc := by
  rfl

/-- The fixed unary controller acts directly on the canonical fuel segment. -/
theorem unaryFuel_canonical_segment (image : CanonicalImage)
    (suffix : List TapeSymbol) :
    evalFrom unaryFuelMachine (unaryFuelTime image.fuel)
      (physicalConfig 0 []
        (physicalSegment image.fuelBits ++ suffix)) 0 =
      some ⟨true, suffix.filterMap id, unaryFuelTime image.fuel⟩ := by
  simpa [physicalSegment, CanonicalImage.fuelBits, List.append_assoc] using
    unaryFuel_zero_contract image.fuel suffix

theorem runtimeMachines_fixed (first second : Machine) :
    runtimeLookupMachine = runtimeLookupMachine ∧
    markerRewriteMachine = markerRewriteMachine ∧
    binaryCounterScanMachine = binaryCounterScanMachine ∧
    unaryFuelMachine = unaryFuelMachine := by
  simp

end AvgCaseMls.Foundation.Universal
