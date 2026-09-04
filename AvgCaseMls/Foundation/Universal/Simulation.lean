import AvgCaseMls.Foundation.Universal.Mutation

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

def oneStepOverhead (width : Nat) : Nat :=
  runtimeLookupTime width + 5 + 1 + markerRewriteTime width

theorem oneStepOverhead_polynomial : IsPolynomial oneStepOverhead := by
  unfold oneStepOverhead
  exact (((runtimeLookupTime_polynomial.add (IsPolynomial.const 5)).add
    (IsPolynomial.const 1)).add markerRewriteTime_polynomial)

/--
One source transition is implemented by fixed-control phases: select and
dispatch the immutable instruction, mutate the represented virtual tape, then
copy the chosen one-hot successor track into the current-PC track.
-/
theorem one_step_simulation (machine : Machine) (config nextConfig : Config)
    (hstep : step machine config = .ok nextConfig) :
    ∃ instruction successor,
      machine.code[config.pc]? = some instruction ∧
      instructionSuccessor instruction config.head = some successor ∧
      nextConfig =
        { mutateVirtualTape instruction config with pc := successor } ∧
      Runs tapeMutationMachine
        { config with pc := mutationEntry instruction }
        1
        { mutateVirtualTape instruction config with pc := 7 } ∧
      ∀ records,
        evalFrom markerRewriteMachine
          (markerRewriteTime machine.code.size)
          (physicalConfig 0 []
            (runtimeLayout
              (oneHot machine.code.size config.pc)
              (oneHot machine.code.size successor) records)) 0 =
        some ⟨true,
          interleave
              (oneHot machine.code.size successor)
              (oneHot machine.code.size successor) ++
            records.filterMap id,
          markerRewriteTime machine.code.size⟩ := by
  cases hlookup : machine.code[config.pc]? with
  | none => simp [step, hlookup] at hstep
  | some instruction =>
      obtain ⟨successor, hsuccessor, hnext, hmutation⟩ :=
        source_step_nonhalt machine config nextConfig instruction hlookup hstep
      exact ⟨instruction, successor, rfl, hsuccessor, hnext, hmutation,
        fun records => markerRewrite_oneHot _ _ _ records⟩

theorem one_step_halt_simulation (machine : Machine) (config : Config)
    (result : Result) (hstep : step machine config = .error result) :
    (machine.code[config.pc]? = none ∧
        result = ⟨false, tapeOutput config, 0⟩) ∨
      ∃ instruction accept,
        machine.code[config.pc]? = some instruction ∧
        instruction = .halt accept ∧
        result = ⟨accept, tapeOutput config, 0⟩ ∧
        step tapeMutationMachine
          { config with pc := mutationEntry instruction } =
          .error ⟨accept, tapeOutput config, 0⟩ := by
  cases hlookup : machine.code[config.pc]? with
  | none =>
      left
      refine ⟨rfl, ?_⟩
      simpa [step, hlookup] using hstep.symm
  | some instruction =>
      right
      obtain ⟨accept, hinstruction, hresult⟩ :=
        source_step_halt machine config instruction result hlookup hstep
      subst instruction
      exact ⟨.halt accept, accept, rfl, rfl, hresult,
        mutation_halt accept config⟩

/--
The successor track needed by marker replacement is produced from decoded
runtime bits.  No premise supplies a precomputed successor marker track.
-/
theorem one_step_decoded_successor (machine : Machine)
    (config nextConfig : Config)
    (hstep : step machine config = .ok nextConfig) :
    ∃ instruction successor,
      machine.code[config.pc]? = some instruction ∧
      instructionSuccessor instruction config.head = some successor ∧
      nextConfig =
        { mutateVirtualTape instruction config with pc := successor } ∧
      Runs tapeMutationMachine
        { config with pc := mutationEntry instruction }
        1
        { mutateVirtualTape instruction config with pc := 7 } ∧
      ∀ scratch records,
        scratch.length = machine.code.size →
        evalFrom successorMaterializeMachine
          (successorMaterializeTime machine.code.size)
          (physicalConfig 0 []
            (runtimeDecodedLayout
              (oneHot machine.code.size config.pc)
              scratch
              (oneHot machine.code.size successor)
              records)) 0 =
        some ⟨true,
          (runtimeTracks
            (oneHot machine.code.size config.pc)
            (oneHot machine.code.size successor)
            (oneHot machine.code.size successor)).filterMap id ++
              records.filterMap id,
          successorMaterializeTime machine.code.size⟩ := by
  cases hlookup : machine.code[config.pc]? with
  | none => simp [step, hlookup] at hstep
  | some instruction =>
      obtain ⟨successor, hsuccessor, hnext, hmutation⟩ :=
        source_step_nonhalt machine config nextConfig instruction hlookup hstep
      refine ⟨instruction, successor, rfl, hsuccessor, hnext, hmutation,
        ?_⟩
      intro scratch records hscratch
      simpa using successorMaterialize_contract
        (oneHot machine.code.size config.pc) scratch
        (oneHot machine.code.size successor)
        (by simpa using hscratch.symm) (by simp) records

end AvgCaseMls.Foundation.Universal
