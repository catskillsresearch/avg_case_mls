import AvgCaseMls.Foundation.Universal.Execution

/-!
# Fixed sequential instruction lookup

`lookupMachine` has eight states and is independent of the simulated source
machine.  It skips records carrying a `true` cursor bit and stops, with its
head on the first opcode bit, at the first record carrying `false`.
-/

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

def lookupMachine : Machine :=
  ⟨#[
    .branch 5 3 1,
    .moveRight 2,
    .branch 6 7 7,
    .moveRight 4,
    .halt true,
    .halt false,
    .moveRight 0,
    .moveRight 2
  ]⟩

def recordScanSteps (instruction : Instruction) : Nat :=
  2 * (encodeInstruction instruction).length + 4

def prefixScanSteps (instructions : List Instruction) : Nat :=
  (instructions.map recordScanSteps).sum

def lookupOverhead (wireLength : Nat) : Nat := 4 * wireLength + 2

theorem lookupOverhead_polynomial : IsPolynomial lookupOverhead :=
  .bounded 4 1 (fun n => by simp [lookupOverhead])

theorem prefixScanSteps_eq (instructions : List Instruction) :
    prefixScanSteps instructions =
      2 * (encodeInstructions instructions).length +
        4 * instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions ih =>
      change recordScanSteps instruction + prefixScanSteps instructions =
        2 * (encodeInstructions (instruction :: instructions)).length +
          4 * (instruction :: instructions).length
      rw [ih]
      simp [recordScanSteps, encodeInstructions]
      omega

theorem prefixScanSteps_le (instructions : List Instruction) :
    prefixScanSteps instructions + 2 ≤
      lookupOverhead
        ((encodeInstructions instructions).length + instructions.length) := by
  rw [prefixScanSteps_eq]
  simp [lookupOverhead]
  omega

private theorem scanBits (bits : Bitstring) (left rest : List TapeSymbol) :
    Runs lookupMachine
      (physicalConfig 2 left (bits.map some ++ none :: rest))
      (2 * bits.length)
      ⟨2, (bits.map some).reverse ++ left, none, rest⟩ := by
  induction bits generalizing left with
  | nil => simpa [physicalConfig] using
      (Runs.refl (machine := lookupMachine)
        ({ pc := 2, left := left, head := none, right := rest } : Config))
  | cons bit bits ih =>
      have first : Runs lookupMachine
          (physicalConfig 2 left
            ((bit :: bits).map some ++ none :: rest))
          2
          (physicalConfig 2 (some bit :: left)
            (bits.map some ++ none :: rest)) := by
        cases bit <;>
          exact .next (by rfl) (.next (by rfl) (.refl _))
      convert first.trans (ih (some bit :: left)) using 1 <;>
        simp [physicalConfig] <;> omega

private theorem skipRecord (instruction : Instruction)
    (left rest : List TapeSymbol) :
    Runs lookupMachine
      (physicalConfig 0 left (markedRecord true instruction ++ rest))
      (recordScanSteps instruction)
      (physicalConfig 0
        ((markedRecord true instruction).reverse ++ left) rest) := by
  have enter : Runs lookupMachine
      (physicalConfig 0 left (markedRecord true instruction ++ rest)) 2
      (physicalConfig 2 (some true :: left)
        ((encodeInstruction instruction).map some ++ none :: rest)) := by
    simp only [markedRecord, instructionRecord, List.cons_append,
      List.append_assoc]
    exact .next (by rfl) (.next (by rfl) (.refl _))
  have scan := scanBits (encodeInstruction instruction)
    (some true :: left) rest
  have leave : Runs lookupMachine
      ⟨2, ((encodeInstruction instruction).map some).reverse ++
          some true :: left, none, rest⟩ 2
      (physicalConfig 0
        ((markedRecord true instruction).reverse ++ left) rest) := by
    simp only [markedRecord, instructionRecord, List.reverse_cons,
      List.reverse_append, List.reverse_singleton, List.cons_append,
      List.append_assoc]
    exact .next (by rfl) (.next (by
      cases rest <;> rfl) (.refl _))
  have all := enter.trans (scan.trans leave)
  convert all using 1 <;>
    simp [recordScanSteps, markedRecord, instructionRecord,
      physicalConfig] <;> omega

theorem lookup_prefix (before : List Instruction) (selected : Instruction)
    (after : List Instruction) (left : List TapeSymbol) :
    Runs lookupMachine
      (physicalConfig 0 left (markedProgramAt before selected after))
      (prefixScanSteps before + 2)
      (physicalConfig 4
        (some false :: (markedPrefix before).reverse ++ left)
        ((encodeInstruction selected).map some ++ none ::
          after.flatMap (markedRecord false))) := by
  induction before generalizing left with
  | nil =>
      simpa [markedProgramAt, markedPrefix, prefixScanSteps, markedRecord,
        instructionRecord, physicalConfig] using
        (Runs.next (machine := lookupMachine) (by rfl)
          (Runs.next (by rfl) (Runs.refl _)))
  | cons instruction before ih =>
      have skip := skipRecord instruction left
        (markedProgramAt before selected after)
      have tail := ih
        ((markedRecord true instruction).reverse ++ left)
      have all := skip.trans tail
      convert all using 1 <;>
        simp [markedProgramAt, markedPrefix, prefixScanSteps,
          List.append_assoc, Nat.add_assoc]

/--
The one-step lookup invariant: for an in-range source counter, the fixed
controller reaches precisely the serialized instruction selected by that
counter.  No source-machine datum occurs in `lookupMachine`.
-/
theorem lookup_selected_instruction (machine : Machine) (pc : Nat)
    (instruction : Instruction)
    (hlookup : machine.code[pc]? = some instruction) :
    ∃ before after,
      before.length = pc ∧
      machine.code.toList = before ++ instruction :: after ∧
      Runs lookupMachine
        (physicalConfig 0 []
          (markedProgramAt before instruction after))
        (prefixScanSteps before + 2)
        (physicalConfig 4
          (some false :: (markedPrefix before).reverse)
          ((encodeInstruction instruction).map some ++ none ::
            after.flatMap (markedRecord false))) := by
  refine ⟨machine.code.toList.take pc, machine.code.toList.drop (pc + 1),
    List.length_take_of_le ?_, ?_, ?_⟩
  · have hpc : pc < machine.code.size :=
      (Array.getElem?_eq_some_iff.mp hlookup).1
    simpa using Nat.le_of_lt hpc
  · exact code_get_decomposition machine.code.toList pc instruction (by
      simpa using hlookup)
  · simpa using lookup_prefix _ _ _ []

theorem lookupMachine_fixed (first second : Machine) :
    lookupMachine = lookupMachine := rfl

/-!
The old marked-record scanner above remains a proved low-level building
block.  Canonical images do not use its destructive monotone marker: their
only program counter is the separate one-hot segment.  The following contract
is the shared lookup invariant used by subsequent canonical phases.
-/

theorem canonical_pc_marker_get (image : CanonicalImage) (index : Nat)
    (hindex : index < image.machine.code.size) :
    image.pcBits[index]'(by simpa using hindex) = (index = image.pc) := by
  simp [CanonicalImage.pcBits, hindex]

theorem canonical_lookup_contract (image : CanonicalImage)
    (instruction : Instruction)
    (hpc : image.machine.code[image.pc]? = some instruction) :
    decodeMachine? image.programBits = some (image.machine, []) ∧
    image.pc < image.machine.code.size ∧
    image.pcBits[image.pc]'(by
      simpa using (Array.getElem?_eq_some_iff.mp hpc).1) = true := by
  constructor
  · simpa [CanonicalImage.programBits] using
      decodeMachine?_suffix image.machine []
  constructor
  · exact (Array.getElem?_eq_some_iff.mp hpc).1
  · simpa using canonical_pc_marker_get image image.pc
      (Array.getElem?_eq_some_iff.mp hpc).1

end AvgCaseMls.Foundation.Universal
