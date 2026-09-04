import AvgCaseMls.Foundation.Universal.Lookup

/-!
# Fixed opcode dispatch

The serialized instruction format has a three-bit constructor tag.  This
finite controller reads exactly those three cells and reaches a distinct
control state for each of the six source instruction constructors.
-/

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

def instructionTagState : Instruction → Nat
  | .halt _ => 14
  | .jump _ => 15
  | .branch _ _ _ => 16
  | .write _ _ => 17
  | .moveLeft _ => 18
  | .moveRight _ => 19

def dispatchMachine : Machine :=
  ⟨#[
    .branch 20 1 8,
    .moveRight 2,
    .branch 20 3 5,
    .moveRight 4,
    .branch 20 14 15,
    .moveRight 6,
    .branch 20 16 17,
    .jump 20,
    .moveRight 9,
    .branch 20 10 20,
    .moveRight 11,
    .branch 20 18 19,
    .jump 20,
    .jump 20,
    .halt true,
    .halt true,
    .halt true,
    .halt true,
    .halt true,
    .halt true,
    .halt false
  ]⟩

private theorem dispatch000 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([false, false, false].map some ++ rest)) 5
      ⟨14, [some false, some false] ++ left, some false, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

private theorem dispatch001 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([false, false, true].map some ++ rest)) 5
      ⟨15, [some false, some false] ++ left, some true, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

private theorem dispatch010 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([false, true, false].map some ++ rest)) 5
      ⟨16, [some true, some false] ++ left, some false, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

private theorem dispatch011 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([false, true, true].map some ++ rest)) 5
      ⟨17, [some true, some false] ++ left, some true, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

private theorem dispatch100 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([true, false, false].map some ++ rest)) 5
      ⟨18, [some false, some true] ++ left, some false, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

private theorem dispatch101 (left rest : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ([true, false, true].map some ++ rest)) 5
      ⟨19, [some false, some true] ++ left, some true, rest⟩ := by
  exact .next (by rfl) (.next (by rfl) (.next (by rfl)
    (.next (by rfl) (.next (by rfl) (.refl _)))))

def dispatchLanding (instruction : Instruction) (left : List TapeSymbol)
    (suffix : List TapeSymbol) : Config :=
  match instruction with
  | .halt accept =>
      ⟨14, [some false, some false] ++ left, some false,
        some accept :: suffix⟩
  | .jump next =>
      ⟨15, [some false, some false] ++ left, some true,
        (encodeNat next).map some ++ suffix⟩
  | .branch blank zero one =>
      ⟨16, [some true, some false] ++ left, some false,
        (encodeNat blank ++ encodeNat zero ++ encodeNat one).map some ++ suffix⟩
  | .write symbol next =>
      ⟨17, [some true, some false] ++ left, some true,
        (encodeTapeSymbol symbol ++ encodeNat next).map some ++ suffix⟩
  | .moveLeft next =>
      ⟨18, [some false, some true] ++ left, some false,
        (encodeNat next).map some ++ suffix⟩
  | .moveRight next =>
      ⟨19, [some false, some true] ++ left, some true,
        (encodeNat next).map some ++ suffix⟩

/-- Exact constructor dispatch for every serialized source instruction. -/
theorem dispatch_instruction (instruction : Instruction)
    (left suffix : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        ((encodeInstruction instruction).map some ++ suffix))
      5 (dispatchLanding instruction left suffix) := by
  cases instruction with
  | halt accept =>
      simpa [encodeInstruction, dispatchLanding] using
        dispatch000 left (some accept :: suffix)
  | jump next =>
      simpa [encodeInstruction, dispatchLanding] using
        dispatch001 left ((encodeNat next).map some ++ suffix)
  | branch blank zero one =>
      simpa [encodeInstruction, dispatchLanding, List.map_append,
        List.append_assoc] using
        dispatch010 left
          ((encodeNat blank ++ encodeNat zero ++ encodeNat one).map some ++
            suffix)
  | write symbol next =>
      simpa [encodeInstruction, dispatchLanding, List.map_append,
        List.append_assoc] using
        dispatch011 left
          ((encodeTapeSymbol symbol ++ encodeNat next).map some ++ suffix)
  | moveLeft next =>
      simpa [encodeInstruction, dispatchLanding] using
        dispatch100 left ((encodeNat next).map some ++ suffix)
  | moveRight next =>
      simpa [encodeInstruction, dispatchLanding] using
        dispatch101 left ((encodeNat next).map some ++ suffix)

/-- Dispatch consumes only the data cells of one canonical bit segment. -/
theorem dispatch_canonical_segment (instruction : Instruction)
    (left suffix : List TapeSymbol) :
    Runs dispatchMachine
      (physicalConfig 0 left
        (physicalSegment (encodeInstruction instruction) ++ suffix))
      5
      (dispatchLanding instruction left (none :: suffix)) := by
  simpa [physicalSegment, List.append_assoc] using
    dispatch_instruction instruction left (none :: suffix)

end AvgCaseMls.Foundation.Universal
