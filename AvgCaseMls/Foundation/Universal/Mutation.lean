import AvgCaseMls.Foundation.Universal.Runtime

/-!
# Fixed virtual-tape mutation controller

Program-counter selection lives on the two-track runtime table.  Consequently
this controller only mutates the represented tape.  Its entry state is chosen
by the fixed opcode dispatcher; every successful path joins at state `7`.
-/

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

def tapeMutationMachine : Machine :=
  ⟨#[
    .jump 7,
    .write none 7,
    .write (some false) 7,
    .write (some true) 7,
    .moveLeft 7,
    .moveRight 7,
    .halt false,
    .halt true
  ]⟩

def mutationEntry : Instruction → Nat
  | .halt false => 6
  | .halt true => 7
  | .jump _ | .branch _ _ _ => 0
  | .write none _ => 1
  | .write (some false) _ => 2
  | .write (some true) _ => 3
  | .moveLeft _ => 4
  | .moveRight _ => 5

def instructionSuccessor (instruction : Instruction)
    (head : TapeSymbol) : Option Nat :=
  match instruction with
  | .halt _ => none
  | .jump next => some next
  | .branch blank zero one =>
      some <| match head with
        | none => blank
        | some false => zero
        | some true => one
  | .write _ next | .moveLeft next | .moveRight next => some next

def mutateVirtualTape (instruction : Instruction) (config : Config) : Config :=
  match instruction with
  | .write symbol _ => { config with head := symbol }
  | .moveLeft _ => moveLeft config config.pc
  | .moveRight _ => moveRight config config.pc
  | _ => config

def CanonicalImage.virtualConfig (image : CanonicalImage) : Config :=
  ⟨image.pc, image.left, image.head, image.right⟩

def CanonicalImage.withVirtualConfig (image : CanonicalImage)
    (config : Config) : CanonicalImage :=
  { image with
    pc := config.pc
    left := config.left
    head := config.head
    right := config.right }

def mutateCanonicalImage (instruction : Instruction)
    (image : CanonicalImage) : CanonicalImage :=
  image.withVirtualConfig
    (mutateVirtualTape instruction image.virtualConfig)

@[simp] theorem mutateCanonicalImage_machine (instruction : Instruction)
    (image : CanonicalImage) :
    (mutateCanonicalImage instruction image).machine = image.machine := rfl

@[simp] theorem mutateCanonicalImage_fuel (instruction : Instruction)
    (image : CanonicalImage) :
    (mutateCanonicalImage instruction image).fuel = image.fuel := rfl

@[simp] theorem mutateCanonicalImage_scratch (instruction : Instruction)
    (image : CanonicalImage) :
    (mutateCanonicalImage instruction image).scratch = image.scratch := rfl

theorem canonical_mutation_contract (instruction : Instruction)
    (image : CanonicalImage) :
    (mutateCanonicalImage instruction image).virtualConfig =
      mutateVirtualTape instruction image.virtualConfig := by
  cases instruction <;> cases image <;>
    simp [mutateCanonicalImage, CanonicalImage.withVirtualConfig,
      CanonicalImage.virtualConfig, mutateVirtualTape, moveLeft, moveRight]

@[simp] theorem mutateVirtualTape_pc (instruction : Instruction)
    (config : Config) :
    (mutateVirtualTape instruction config).pc = config.pc := by
  cases instruction <;> simp [mutateVirtualTape, moveLeft, moveRight] <;>
    split <;> rfl

theorem mutation_run_nonhalt (instruction : Instruction) (config : Config)
    (successor : Nat)
    (hsuccessor : instructionSuccessor instruction config.head =
      some successor) :
    Runs tapeMutationMachine
      { config with pc := mutationEntry instruction }
      1
      { mutateVirtualTape instruction config with pc := 7 } := by
  cases instruction with
  | halt accept => simp [instructionSuccessor] at hsuccessor
  | jump next =>
      simp [instructionSuccessor] at hsuccessor
      exact .next (by rfl) (.refl _)
  | branch blank zero one =>
      simp [instructionSuccessor] at hsuccessor
      exact .next (by rfl) (.refl _)
  | write symbol next =>
      cases symbol with
      | none =>
          exact .next (by rfl) (.refl _)
      | some bit =>
          cases bit <;> exact .next (by rfl) (.refl _)
  | moveLeft next =>
      rcases config with ⟨pc, left, head, right⟩
      cases left <;> exact .next (by rfl) (.refl _)
  | moveRight next =>
      rcases config with ⟨pc, left, head, right⟩
      cases right <;> exact .next (by rfl) (.refl _)

theorem mutation_halt (accept : Bool) (config : Config) :
    step tapeMutationMachine { config with pc := mutationEntry (.halt accept) } =
      .error ⟨accept, tapeOutput config, 0⟩ := by
  cases accept <;> rfl

theorem source_step_nonhalt (machine : Machine) (config nextConfig : Config)
    (instruction : Instruction)
    (hlookup : machine.code[config.pc]? = some instruction)
    (hstep : step machine config = .ok nextConfig) :
    ∃ successor,
      instructionSuccessor instruction config.head = some successor ∧
      nextConfig =
        { mutateVirtualTape instruction config with pc := successor } ∧
      Runs tapeMutationMachine
        { config with pc := mutationEntry instruction }
        1
        { mutateVirtualTape instruction config with pc := 7 } := by
  simp only [step, hlookup] at hstep
  rcases config with ⟨pc, left, head, right⟩
  cases instruction with
  | halt accept => simp at hstep
  | jump successor =>
      simp at hstep
      subst nextConfig
      exact ⟨successor, rfl, rfl,
        mutation_run_nonhalt (.jump successor) _ successor rfl⟩
  | branch blank zero one =>
      cases head with
      | none =>
          simp at hstep
          subst nextConfig
          exact ⟨blank, rfl, rfl,
            mutation_run_nonhalt (.branch blank zero one) _ blank rfl⟩
      | some bit =>
          cases bit
          · simp at hstep
            subst nextConfig
            exact ⟨zero, rfl, rfl,
              mutation_run_nonhalt (.branch blank zero one) _ zero rfl⟩
          · simp at hstep
            subst nextConfig
            exact ⟨one, rfl, rfl,
              mutation_run_nonhalt (.branch blank zero one) _ one rfl⟩
  | write symbol successor =>
      simp at hstep
      subst nextConfig
      exact ⟨successor, rfl, rfl,
        mutation_run_nonhalt (.write symbol successor) _ successor rfl⟩
  | moveLeft successor =>
      cases left <;> simp [moveLeft] at hstep
      all_goals
        subst nextConfig
        exact ⟨successor, rfl, rfl,
          mutation_run_nonhalt (.moveLeft successor) _ successor rfl⟩
  | moveRight successor =>
      cases right <;> simp [moveRight] at hstep
      all_goals
        subst nextConfig
        exact ⟨successor, rfl, rfl,
          mutation_run_nonhalt (.moveRight successor) _ successor rfl⟩

theorem source_step_halt (machine : Machine) (config : Config)
    (instruction : Instruction) (result : Result)
    (hlookup : machine.code[config.pc]? = some instruction)
    (hstep : step machine config = .error result) :
    ∃ accept, instruction = .halt accept ∧
      result = ⟨accept, tapeOutput config, 0⟩ := by
  simp only [step, hlookup] at hstep
  rcases config with ⟨pc, left, head, right⟩
  cases instruction with
  | halt accept => exact ⟨accept, rfl, by simpa using hstep.symm⟩
  | jump next => simp at hstep
  | branch blank zero one =>
      cases head with
      | none => simp at hstep
      | some bit => cases bit <;> simp at hstep
  | write symbol next => simp at hstep
  | moveLeft next => simp at hstep
  | moveRight next => simp at hstep

end AvgCaseMls.Foundation.Universal
