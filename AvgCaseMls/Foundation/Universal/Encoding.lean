import AvgCaseMls.Foundation.Serialization

/-!
# Physical layouts for the fixed universal controller

The program is stored as blank-delimited instruction records.  The bit in
front of each record is a cursor bit: records preceding the current program
counter carry `true`, while the selected record carries `false`.  This lets a
fixed controller find the selected instruction by a destructive-free
left-to-right scan.
-/

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

def instructionRecord (instruction : Instruction) : List TapeSymbol :=
  (encodeInstruction instruction).map some ++ [none]

def markedRecord (selected : Bool) (instruction : Instruction) :
    List TapeSymbol :=
  some selected :: instructionRecord instruction

def markedPrefix (instructions : List Instruction) : List TapeSymbol :=
  instructions.flatMap (markedRecord true)

def markedProgramAt (before : List Instruction) (instruction : Instruction)
    (after : List Instruction) : List TapeSymbol :=
  markedPrefix before ++ markedRecord false instruction ++
    after.flatMap (markedRecord false)

def physicalConfig (pc : Nat) (left : List TapeSymbol) :
    List TapeSymbol → Config
  | [] => ⟨pc, left, none, []⟩
  | head :: right => ⟨pc, left, head, right⟩

/-!
## Canonical universal tape image

Every variable-width field is a bit-only segment terminated by one blank.
Consequently a blank is structural and never data.  The seven segments are,
in order: encoded program table, one-hot runtime PC, encoded virtual left
stack, encoded virtual head, encoded virtual right stack, unary fuel, and
scratch.  The physical controller may move its head between segment starts,
but no phase is allowed to reinterpret a blank as a virtual tape symbol.
-/

def physicalSegment (bits : Bitstring) : List TapeSymbol :=
  bits.map some ++ [none]

def splitPhysicalSegment? :
    List TapeSymbol → Option (Bitstring × List TapeSymbol)
  | [] => none
  | none :: rest => some ([], rest)
  | some bit :: rest => do
      let (bits, suffix) ← splitPhysicalSegment? rest
      some (bit :: bits, suffix)

@[simp] theorem splitPhysicalSegment?_suffix (bits : Bitstring)
    (suffix : List TapeSymbol) :
    splitPhysicalSegment? (physicalSegment bits ++ suffix) =
      some (bits, suffix) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [physicalSegment, List.map_cons, List.cons_append,
        splitPhysicalSegment?]
      change (splitPhysicalSegment? (physicalSegment bits ++ suffix)).bind
        (fun pair => some (bit :: pair.1, pair.2)) =
        some (bit :: bits, suffix)
      rw [ih]
      rfl

@[simp] theorem splitPhysicalSegment?_physicalSegment (bits : Bitstring) :
    splitPhysicalSegment? (physicalSegment bits) = some (bits, []) := by
  simpa using splitPhysicalSegment?_suffix bits []

structure CanonicalFields where
  program : Bitstring
  pc : Bitstring
  left : Bitstring
  head : Bitstring
  right : Bitstring
  fuel : Bitstring
  scratch : Bitstring
  deriving DecidableEq, Repr

def splitCanonicalLayout? (tape : List TapeSymbol) :
    Option CanonicalFields := do
  let (program, rest₁) ← splitPhysicalSegment? tape
  let (pc, rest₂) ← splitPhysicalSegment? rest₁
  let (left, rest₃) ← splitPhysicalSegment? rest₂
  let (head, rest₄) ← splitPhysicalSegment? rest₃
  let (right, rest₅) ← splitPhysicalSegment? rest₄
  let (fuel, rest₆) ← splitPhysicalSegment? rest₅
  let (scratch, rest₇) ← splitPhysicalSegment? rest₆
  if rest₇ = [] then
    some ⟨program, pc, left, head, right, fuel, scratch⟩
  else none

structure CanonicalImage where
  machine : Machine
  pc : Nat
  left : List TapeSymbol
  head : TapeSymbol
  right : List TapeSymbol
  fuel : Nat
  scratch : Bitstring
  deriving DecidableEq, Repr

def CanonicalImage.programBits (image : CanonicalImage) : Bitstring :=
  encodeMachine image.machine

def CanonicalImage.pcBits (image : CanonicalImage) : Bitstring :=
  (List.range image.machine.code.size).map fun index => index = image.pc

def CanonicalImage.leftBits (image : CanonicalImage) : Bitstring :=
  encodeTapeSymbols image.left

def CanonicalImage.headBits (image : CanonicalImage) : Bitstring :=
  encodeTapeSymbol image.head

def CanonicalImage.rightBits (image : CanonicalImage) : Bitstring :=
  encodeTapeSymbols image.right

def CanonicalImage.fuelBits (image : CanonicalImage) : Bitstring :=
  List.replicate image.fuel true

def canonicalLayout (image : CanonicalImage) : List TapeSymbol :=
  physicalSegment image.programBits ++
  physicalSegment image.pcBits ++
  physicalSegment image.leftBits ++
  physicalSegment image.headBits ++
  physicalSegment image.rightBits ++
  physicalSegment image.fuelBits ++
  physicalSegment image.scratch

def CanonicalImage.fields (image : CanonicalImage) : CanonicalFields :=
  ⟨image.programBits, image.pcBits, image.leftBits, image.headBits,
    image.rightBits, image.fuelBits, image.scratch⟩

@[simp] theorem splitCanonicalLayout?_canonicalLayout
    (image : CanonicalImage) :
    splitCanonicalLayout? (canonicalLayout image) = some image.fields := by
  simp [splitCanonicalLayout?, canonicalLayout, CanonicalImage.fields,
    List.append_assoc]

def CanonicalImage.segmentLengths (image : CanonicalImage) : List Nat :=
  [image.programBits.length + 1, image.pcBits.length + 1,
   image.leftBits.length + 1, image.headBits.length + 1,
   image.rightBits.length + 1, image.fuelBits.length + 1,
   image.scratch.length + 1]

def CanonicalImage.segmentStart (image : CanonicalImage) (segment : Nat) : Nat :=
  (image.segmentLengths.take segment).sum

@[simp] theorem physicalSegment_length (bits : Bitstring) :
    (physicalSegment bits).length = bits.length + 1 := by
  simp [physicalSegment]

@[simp] theorem physicalSegment_filterMap (bits : Bitstring) :
    (physicalSegment bits).filterMap id = bits := by
  simp [physicalSegment]

theorem physicalSegment_data_ne_blank (bits : Bitstring) (index : Nat)
    (hindex : index < bits.length) :
    (physicalSegment bits)[index]? = some (some (bits[index]'hindex)) := by
  rw [physicalSegment, List.getElem?_append_left]
  · simp
  · simpa using hindex

theorem physicalSegment_delimiter (bits : Bitstring) :
    (physicalSegment bits)[bits.length]? = some none := by
  simp [physicalSegment]

@[simp] theorem CanonicalImage.pcBits_length (image : CanonicalImage) :
    image.pcBits.length = image.machine.code.size := by
  simp [CanonicalImage.pcBits]

@[simp] theorem CanonicalImage.headBits_length (image : CanonicalImage) :
    image.headBits.length = 2 := by
  unfold CanonicalImage.headBits
  cases image.head with
  | none => rfl
  | some bit => cases bit <;> rfl

@[simp] theorem CanonicalImage.fuelBits_length (image : CanonicalImage) :
    image.fuelBits.length = image.fuel := by
  simp [CanonicalImage.fuelBits]

@[simp] theorem canonicalLayout_length (image : CanonicalImage) :
    (canonicalLayout image).length = image.segmentLengths.sum := by
  simp [canonicalLayout, CanonicalImage.segmentLengths]

/-- Starts of distinct canonical fields are strictly ordered. -/
theorem canonical_segment_starts_strict (image : CanonicalImage) :
    image.segmentStart 0 < image.segmentStart 1 ∧
    image.segmentStart 1 < image.segmentStart 2 ∧
    image.segmentStart 2 < image.segmentStart 3 ∧
    image.segmentStart 3 < image.segmentStart 4 ∧
    image.segmentStart 4 < image.segmentStart 5 ∧
    image.segmentStart 5 < image.segmentStart 6 ∧
    image.segmentStart 6 < (canonicalLayout image).length := by
  simp [CanonicalImage.segmentStart, CanonicalImage.segmentLengths,
    canonicalLayout]

def canonicalInitialImage (machine : Machine) (input : Bitstring)
    (fuel : Nat) : CanonicalImage :=
  let config := initial input
  { machine
    pc := config.pc
    left := config.left
    head := config.head
    right := config.right
    fuel
    scratch := List.replicate machine.code.size false }

def encodeInvocationFuel (fuel : Nat) : Bitstring :=
  List.replicate fuel true ++ [false]

def decodeInvocationFuel? : Bitstring → Option (Nat × Bitstring)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (fuel, suffix) ← decodeInvocationFuel? rest
      some (fuel + 1, suffix)

@[simp] theorem decodeInvocationFuel?_suffix (fuel : Nat)
    (suffix : Bitstring) :
    decodeInvocationFuel? (encodeInvocationFuel fuel ++ suffix) =
      some (fuel, suffix) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [encodeInvocationFuel, List.replicate_succ,
        List.cons_append, decodeInvocationFuel?]
      change (decodeInvocationFuel?
        (encodeInvocationFuel fuel ++ suffix)).bind
          (fun pair => some (pair.1 + 1, pair.2)) =
        some (fuel + 1, suffix)
      rw [ih]
      rfl

@[simp] theorem decodeInvocationFuel?_unterminated (fuel : Nat) :
    decodeInvocationFuel? (List.replicate fuel true) = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [List.replicate_succ, decodeInvocationFuel?]
      rw [ih]
      rfl

def parseInvocationImage? (bits : Bitstring) : Option CanonicalImage := do
  let (machine, rest) ← decodeMachine? bits
  let (fuel, rest) ← decodeInvocationFuel? rest
  let (width, input) ← decodeNat? rest
  if width = input.length then
    some (canonicalInitialImage machine input fuel)
  else none

def canonicalInvocation (machine : Machine) (fuel : Nat)
    (input : Bitstring) : Bitstring :=
  encodeMachine machine ++ encodeInvocationFuel fuel ++
    encodeNat input.length ++ input

@[simp] theorem parseInvocationImage?_canonicalInvocation
    (machine : Machine) (input : Bitstring) (fuel : Nat) :
    parseInvocationImage? (canonicalInvocation machine fuel input) =
      some (canonicalInitialImage machine input fuel) := by
  simp [parseInvocationImage?, canonicalInvocation, decodeMachine?_suffix,
    decodeInvocationFuel?_suffix, decodeNat?_suffix, List.append_assoc]

/-- The parser produces exactly the canonical seven-field physical image. -/
theorem parseInvocation_layout (machine : Machine) (input : Bitstring)
    (fuel : Nat) :
    (parseInvocationImage? (canonicalInvocation machine fuel input)).map
      canonicalLayout =
    some (canonicalLayout (canonicalInitialImage machine input fuel)) := by
  simp

def focusAt (pc : Nat) (tape : List TapeSymbol) (offset : Nat) : Config :=
  physicalConfig pc (tape.take offset).reverse (tape.drop offset)

def focusCanonicalSegment (pc : Nat) (image : CanonicalImage)
    (segment : Nat) : Config :=
  focusAt pc (canonicalLayout image) (image.segmentStart segment)

@[simp] theorem instructionRecord_ne_nil (instruction : Instruction) :
    instructionRecord instruction ≠ [] := by
  simp [instructionRecord]

@[simp] theorem markedPrefix_append (first second : List Instruction) :
    markedPrefix (first ++ second) =
      markedPrefix first ++ markedPrefix second := by
  simp [markedPrefix, List.flatMap_append]

theorem code_get_decomposition (code : List Instruction) (pc : Nat)
    (instruction : Instruction) (h : code[pc]? = some instruction) :
    code = code.take pc ++ instruction :: code.drop (pc + 1) := by
  induction code generalizing pc with
  | nil => simp at h
  | cons first rest ih =>
      cases pc with
      | zero =>
          have hfirst : first = instruction := by simpa using h
          subst first
          rfl
      | succ pc =>
          have hrest : rest[pc]? = some instruction := by simpa using h
          have htail := ih pc hrest
          simpa [Nat.add_assoc] using congrArg (List.cons first) htail

end AvgCaseMls.Foundation.Universal
