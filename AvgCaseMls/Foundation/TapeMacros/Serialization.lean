import AvgCaseMls.Foundation.TapeMacros.Blocks
import AvgCaseMls.Foundation.Codec

/-!
# Length framing and nested-list serialization specifications

The codecs are canonical and suffix preserving.  The accompanying assembler
templates below are intentionally named `static`: they are useful only when a
compiler already knows the complete source block.  They are not runtime-input
transducers and are not used as evidence for dynamic macro correctness.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def frame (bits : Bitstring) : Bitstring := encodeNat bits.length ++ bits

def unframe? (bits : Bitstring) : Option (Bitstring × Bitstring) := do
  let (width, rest) ← decodeNat? bits
  if width ≤ rest.length then
    some (rest.take width, rest.drop width)
  else none

@[simp] theorem unframe?_frame_suffix (bits rest : Bitstring) :
    unframe? (frame bits ++ rest) = some (bits, rest) := by
  simp [frame, unframe?, decodeNat?_suffix]

def encodeList (items : List Bitstring) : Bitstring :=
  encodeNat items.length ++ items.flatMap frame

def decodeListBody? : Nat → Bitstring → Option (List Bitstring × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (item, rest) ← unframe? bits
      let (items, suffix) ← decodeListBody? count rest
      some (item :: items, suffix)

def decodeList? (bits : Bitstring) : Option (List Bitstring × Bitstring) := do
  let (count, rest) ← decodeNat? bits
  decodeListBody? count rest

private theorem decodeListBody?_suffix (items : List Bitstring)
    (rest : Bitstring) :
    decodeListBody? items.length (items.flatMap frame ++ rest) =
      some (items, rest) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp [decodeListBody?, unframe?_frame_suffix, ih]

@[simp] theorem decodeList?_encodeList_suffix (items : List Bitstring)
    (rest : Bitstring) :
    decodeList? (encodeList items ++ rest) = some (items, rest) := by
  simp [encodeList, decodeList?, decodeNat?_suffix,
    decodeListBody?_suffix]

@[simp] theorem decodeList?_encodeList (items : List Bitstring) :
    decodeList? (encodeList items) = some (items, []) := by
  simpa using decodeList?_encodeList_suffix items []

def encodeNestedList (items : List (List Bitstring)) : Bitstring :=
  encodeList (items.map encodeList)

def decodeNestedList? (bits : Bitstring) :
    Option (List (List Bitstring) × Bitstring) := do
  let (encoded, rest) ← decodeList? bits
  let decoded ← encoded.mapM fun item => do
    let (value, suffix) ← decodeList? item
    if suffix = [] then some value else none
  some (decoded, rest)

private def decodeClosedList? (bits : Bitstring) : Option (List Bitstring) := do
  let (value, suffix) ← decodeList? bits
  if suffix = [] then some value else none

@[simp] private theorem decodeClosedList?_encodeList (items : List Bitstring) :
    decodeClosedList? (encodeList items) = some items := by
  simp [decodeClosedList?]

private theorem mapM_decodeClosedList_encode
    (items : List (List Bitstring)) :
    (items.map encodeList).mapM decodeClosedList? = some items := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

@[simp] theorem decodeNestedList?_encodeNestedList
    (items : List (List Bitstring)) :
    decodeNestedList? (encodeNestedList items) = some (items, []) := by
  simp only [encodeNestedList, decodeNestedList?, decodeList?_encodeList]
  change ((items.map encodeList).mapM decodeClosedList?).bind
      (fun decoded => some (decoded, [])) = some (items, [])
  rw [mapM_decodeClosedList_encode]
  rfl

/-- A write/move pair; the move is retained after the final bit for linking. -/
def emitCell (bit : Bool) : Fragment :=
  [.write (some bit) (.local 1), .moveRight .exit]

def emitWord : Bitstring → Fragment
  | [] => []
  | bit :: rest => (emitCell bit).seq (emitWord rest)

def eraseCells : Nat → Fragment
  | 0 => []
  | count + 1 =>
      Fragment.seq
        ([.write none (.local 1), .moveRight .exit] : Fragment)
        (eraseCells count)

/--
Compile-time-known block replacement.  It overwrites the source span and
clears any old suffix not occupied by the target.
-/
def overwriteFragment (source target : Bitstring) : Fragment :=
  (emitWord target).seq (eraseCells (source.length - target.length))

def overwriteMachine (source target : Bitstring) : Machine :=
  (overwriteFragment source target).close

def overwriteTransitions (source target : Bitstring) : Nat :=
  2 * max source.length target.length + 1

@[simp] theorem emitWord_length (bits : Bitstring) :
    (emitWord bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp [emitWord, emitCell, ih]
      omega

@[simp] theorem eraseCells_length (count : Nat) :
    (eraseCells count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [eraseCells, ih]
      omega

@[simp] theorem overwriteFragment_length (source target : Bitstring) :
    (overwriteFragment source target).length =
      2 * max source.length target.length := by
  simp [overwriteFragment]
  omega

@[simp] theorem overwriteMachine_code_size (source target : Bitstring) :
    (overwriteMachine source target).code.size =
      overwriteTransitions source target := by
  simp [overwriteMachine, Fragment.close, Fragment.machine,
    Fragment.halt, overwriteTransitions]

/-- A static code-generation template, not a runtime parser. -/
def staticEncodeNatTemplate (n : Nat) : Machine :=
  overwriteMachine (Nat.bits n) (encodeNat n)

/-- A static code-generation template, not a runtime parser. -/
def staticDecodeNatTemplate (n : Nat) : Machine :=
  overwriteMachine (encodeNat n) (Nat.bits n)

def staticCopyTemplate (bits : Bitstring) : Machine :=
  overwriteMachine bits (copyBlock bits)

def staticAppendTemplate (first second : Bitstring) : Machine :=
  overwriteMachine first (appendBlock first second)

def staticFrameTemplate (bits : Bitstring) : Machine :=
  overwriteMachine bits (frame bits)

def staticNestedListTemplate (items : List (List Bitstring)) : Machine :=
  overwriteMachine [] (encodeNestedList items)

/-- A concrete list-map example on serialized one-bit booleans. -/
def mapNotEncoded (items : List Bool) : Bitstring :=
  encodeList ((items.map (!·)).map fun bit => [bit])

/-- A concrete fold example: parity serialized as a one-bit block. -/
def foldXorEncoded (items : List Bool) : Bitstring :=
  frame [items.foldl xor false]

def staticMapNotTemplate (items : List Bool) : Machine :=
  overwriteMachine (encodeList (items.map fun bit => [bit]))
    (mapNotEncoded items)

def staticFoldXorTemplate (items : List Bool) : Machine :=
  overwriteMachine (encodeList (items.map fun bit => [bit]))
    (foldXorEncoded items)

theorem overwriteTransitions_linear (source target : Bitstring) :
    overwriteTransitions source target ≤
      2 * (source.length + target.length) + 1 := by
  simp [overwriteTransitions]

theorem serialized_map_fold_are_base_code (items : List Bool)
    (instruction : Instruction)
    (h : instruction ∈
      (overwriteFragment
        (encodeList (items.map fun bit => [bit]))
        (mapNotEncoded items)).compileAt 0 0) :
    (∃ accept, instruction = .halt accept) ∨
    (∃ next, instruction = .jump next) ∨
    (∃ blank zero one, instruction = .branch blank zero one) ∨
    (∃ symbol next, instruction = .write symbol next) ∨
    (∃ next, instruction = .moveLeft next) ∨
    (∃ next, instruction = .moveRight next) :=
  Fragment.compile_constructors _ _ _ _ h

end AvgCaseMls.Foundation.TapeMacros
