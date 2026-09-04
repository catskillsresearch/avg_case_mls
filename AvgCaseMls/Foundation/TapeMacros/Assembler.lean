import AvgCaseMls.Foundation.TapeMacros.Core

/-!
# A relocatable assembler for `Machine`

`Fragment` is deliberately only syntax.  Its compiler emits the six
constructors of `Instruction`; execution is still exclusively through
`Machine.step` and `evalFrom`.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

/-- A control-flow destination, relative to a fragment or at its exit. -/
inductive Target where
  | local (offset : Nat)
  | exit
  deriving DecidableEq, Repr

/-- Relocatable machine instructions. -/
inductive Asm where
  | halt (accept : Bool)
  | jump (next : Target)
  | branch (onBlank onFalse onTrue : Target)
  | write (symbol : TapeSymbol) (next : Target)
  | moveLeft (next : Target)
  | moveRight (next : Target)
  deriving DecidableEq, Repr

abbrev Fragment := List Asm

def Target.resolve (base exit : Nat) : Target → Nat
  | .local offset => base + offset
  | .exit => exit

def Asm.compile (base exit : Nat) : Asm → Instruction
  | .halt accept => .halt accept
  | .jump next => .jump (next.resolve base exit)
  | .branch blank zero one =>
      .branch (blank.resolve base exit) (zero.resolve base exit)
        (one.resolve base exit)
  | .write symbol next => .write symbol (next.resolve base exit)
  | .moveLeft next => .moveLeft (next.resolve base exit)
  | .moveRight next => .moveRight (next.resolve base exit)

/-- Compile a fragment placed at `base`, resolving its open exit to `exit`. -/
def Fragment.compileAt (code : Fragment) (base exit : Nat) :
    List Instruction :=
  code.map (Asm.compile base exit)

def Fragment.machine (code : Fragment) (exit : Nat := code.length) : Machine :=
  ⟨(code.compileAt 0 exit).toArray⟩

/-- All local edges stay inside the finite control graph. -/
def Target.wellFormed (size : Nat) : Target → Prop
  | .local offset => offset < size
  | .exit => True

def Asm.wellFormed (size : Nat) : Asm → Prop
  | .halt _ => True
  | .jump next => next.wellFormed size
  | .branch blank zero one =>
      blank.wellFormed size ∧ zero.wellFormed size ∧ one.wellFormed size
  | .write _ next | .moveLeft next | .moveRight next =>
      next.wellFormed size

def Fragment.wellFormed (code : Fragment) : Prop :=
  ∀ instruction ∈ code, instruction.wellFormed code.length

@[simp] theorem Fragment.length_compileAt (code : Fragment) (base exit : Nat) :
    (code.compileAt base exit).length = code.length := by
  simp [Fragment.compileAt]

theorem Fragment.getElem_compileAt (code : Fragment) (base exit i : Nat)
    (hi : i < code.length) :
    (code.compileAt base exit)[i]'(by simpa using hi) =
      (code[i]'hi).compile base exit := by
  simp [Fragment.compileAt]

/-- Relocation changes every local address by exactly the base displacement. -/
theorem Target.resolve_relocate (target : Target) (base exit delta : Nat) :
    target.resolve (base + delta) exit =
      match target with
      | .local offset => base + (delta + offset)
      | .exit => exit := by
  cases target <;> simp [Target.resolve, Nat.add_assoc]

/-- Retarget the open exit while preserving all internal control edges. -/
def Asm.retarget (newExit : Target) : Asm → Asm
  | .halt accept => .halt accept
  | .jump .exit => .jump newExit
  | .jump target => .jump target
  | .branch blank zero one =>
      .branch (replace blank) (replace zero) (replace one)
  | .write symbol next => .write symbol (replace next)
  | .moveLeft next => .moveLeft (replace next)
  | .moveRight next => .moveRight (replace next)
where
  replace : Target → Target
    | .exit => newExit
    | target => target

def Asm.shiftLocals (delta : Nat) : Asm → Asm
  | .halt accept => .halt accept
  | .jump next => .jump (shift next)
  | .branch blank zero one => .branch (shift blank) (shift zero) (shift one)
  | .write symbol next => .write symbol (shift next)
  | .moveLeft next => .moveLeft (shift next)
  | .moveRight next => .moveRight (shift next)
where
  shift : Target → Target
    | .local offset => .local (delta + offset)
    | .exit => .exit

/--
Sequential composition is genuine link-time composition: exits of the first
fragment become the entry of the second, whose local labels are shifted.
-/
def Fragment.seq (first second : Fragment) : Fragment :=
  first.map (Asm.retarget (.local first.length)) ++
    second.map (Asm.shiftLocals first.length)

@[simp] theorem Fragment.length_seq (first second : Fragment) :
    (first.seq second).length = first.length + second.length := by
  simp [Fragment.seq]

def Fragment.halt (accept : Bool) : Fragment := [.halt accept]
def Fragment.jump : Fragment := [.jump .exit]
def Fragment.write (symbol : TapeSymbol) : Fragment := [.write symbol .exit]
def Fragment.moveLeft : Fragment := [.moveLeft .exit]
def Fragment.moveRight : Fragment := [.moveRight .exit]
def Fragment.branch : Fragment := [.branch .exit .exit .exit]

/-- A fragment followed by a concrete halting continuation. -/
def Fragment.close (body : Fragment) (accept : Bool := true) : Machine :=
  (body.seq (.halt accept)).machine

/-- Hoare-style partial correctness with an explicit transition bound. -/
def Hoare (M : Machine) (entry : Nat) (pre post : Config → Prop)
    (bound : Config → Nat) : Prop :=
  ∀ c, pre c → ∃ r,
    evalFrom M (bound c) { c with pc := entry } 0 = some r ∧
      r.steps ≤ bound c ∧
      ∀ c', step M c' = .error r → post c'

/-- A simpler total-output specification used by closed transducers. -/
def TransducesWithin (M : Machine) (input output : Bitstring)
    (bound : Nat) : Prop :=
  ∃ steps, steps ≤ bound ∧
    eval M bound input = some ⟨true, output, steps⟩

theorem Fragment.compile_constructors (code : Fragment) (base exit : Nat)
    (instruction : Instruction)
    (h : instruction ∈ code.compileAt base exit) :
    (∃ accept, instruction = .halt accept) ∨
    (∃ next, instruction = .jump next) ∨
    (∃ blank zero one, instruction = .branch blank zero one) ∨
    (∃ symbol next, instruction = .write symbol next) ∨
    (∃ next, instruction = .moveLeft next) ∨
    (∃ next, instruction = .moveRight next) := by
  rcases List.mem_map.mp h with ⟨asm, _, rfl⟩
  cases asm <;> simp [Asm.compile]

end AvgCaseMls.Foundation.TapeMacros
