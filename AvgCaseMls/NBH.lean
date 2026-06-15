/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom
import Mathlib.Tactic

/-!
Phase **4A:** bounded halting for nondeterministic Turing machines (NBH) and a simple
POL-rankable distribution $`\mu_0`$ (TR1995-711 / Levin BH).

Literature: $`\mathrm{BH} = \{(M,x,1^t) : M \text{ is an NTM accepting } x \text{ in } \le t \text{ steps}\}`$.

**Lean fork:** instances reference a canonical finite machine table by index; step bound uses
[`encodeNat`] rather than unary $`1^t`$. See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace NBH

open AvCom

/-! ### Nat codec -/

def encodeNat : Nat → Bitstring
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def decodeNat? : Bitstring → Option (Nat × Bitstring)
  | [] => none
  | [false] => some (0, [])
  | true :: rest =>
    match decodeNat? rest with
    | some (n, rest') => some (n + 1, rest')
    | none => none
  | false :: _ :: _ => none

namespace decodeNat?

theorem encode (n : Nat) : decodeNat? (encodeNat n) = some (n, []) := by
  induction n with
  | zero => simp [encodeNat, decodeNat?]
  | succ n ih =>
    simp [encodeNat, decodeNat?]
    rw [ih]

end decodeNat?

/-! ### One-tape NTM scaffold -/

structure Trans where
  read : Bool
  write : Bool
  next : Nat
  right : Bool
  deriving Repr, DecidableEq

structure NTM where
  numStates : Nat
  hStates : 0 < numStates
  start : Nat
  accept : Nat
  hStart : start < numStates
  hAccept : accept < numStates
  trans : Nat → Bool → Option Trans
  hTrans : ∀ s b t, trans s b = some t → t.next < numStates

namespace NTM

def tapeGet (tape : Bitstring) (i : Nat) : Bool :=
  match tape[i]? with
  | some b => b
  | none => false

def tapeSet (tape : Bitstring) (i : Nat) (b : Bool) : Bitstring :=
  if hi : i < tape.length then
    tape.take i ++ [b] ++ tape.drop (i + 1)
  else
    tape ++ List.replicate (i - tape.length) false ++ [b]

def step (M : NTM) (state head : Nat) (tape : Bitstring) : Option (Nat × Nat × Bitstring) :=
  match M.trans state (tapeGet tape head) with
  | none => none
  | some t =>
    if t.read = tapeGet tape head then
      let tape' := tapeSet tape head t.write
      let head' := if t.right then head + 1 else head - 1
      if t.next < M.numStates then
        some (t.next, head', tape')
      else
        none
    else
      none

end NTM

/-! ### Canonical machines and instances -/

def trivialAcceptNTM : NTM where
  numStates := 1
  hStates := by decide
  start := 0
  accept := 0
  hStart := by decide
  hAccept := by decide
  trans := fun _ _ => none
  hTrans := by intro s b t ht; simp at ht

def canonicalMachines : List NTM := [trivialAcceptNTM]

def lookupMachine? (id : Nat) : Option NTM :=
  canonicalMachines[id]?

structure NBHInstance where
  machineId : Nat
  input : Bitstring
  bound : Nat

namespace NBHInstance

/-- Field delimiter `[false, false, true]`; never a substring of [`encodeNat`] outputs. -/
def delim : Bitstring := [false, false, true]

def delimFree (s : Bitstring) : Prop :=
  ¬ List.Sublist delim s

def WellFormed (inst : NBHInstance) : Prop :=
  delimFree inst.input

def splitDelim.go (pref rest : Bitstring) : Option (Bitstring × Bitstring) :=
  match rest with
  | [] => none
  | false :: false :: true :: suffix => some (pref, suffix)
  | b :: suffix => splitDelim.go (pref ++ [b]) suffix

def splitDelim (s : Bitstring) : Option (Bitstring × Bitstring) :=
  splitDelim.go [] s

namespace splitDelim

theorem go_delim_suffix (pref suffix : Bitstring) :
    splitDelim.go pref (delim ++ suffix) = some (pref, suffix) := by
  induction pref generalizing suffix with
  | nil => simp [go, delim]
  | cons b pref' _ => simp [go, delim, List.cons_append, List.nil_append]

theorem delimFree_cons_append_eq_delim (b : Bool) (pref' s t : Bitstring)
    (h : delimFree (b :: pref'))
    (heq : b :: pref' ++ (delim ++ s) = delim ++ t) : False := by
  rw [delim] at heq
  set p := b :: pref'
  by_cases hlt : p.length < 3
  · have h1 := congrArg (fun l => l[1]!) heq
    have h2 := congrArg (fun l => l[2]!) heq
    rcases b with rfl | rfl
    · cases pref' with
      | nil => simp [List.cons_append, delim] at h1 h2
      | cons head tail =>
        cases head with
        | false =>
          cases tail with
          | nil => simp [List.cons_append, delim] at h1 h2
          | cons b1 tl => cases b1 <;> cases tl <;> simp [List.cons_append, delim] at h1 h2
        | true => simp [List.cons_append, delim] at h1 h2
    · simp [p, List.cons_append, delim] at h1 h2
  · have hp : 3 ≤ p.length := Nat.le_of_not_gt hlt
    have htake : p.take 3 = delim := by
      have eq := congrArg (List.take 3) heq
      simp [List.take_append, hp, delim] at eq
      exact eq
    apply h
    exact List.IsPrefix.sublist ⟨p.drop 3, by rw [← htake, List.take_append_drop 3 p]⟩

theorem go_cons_not_delim (acc : Bitstring) (headBit : Bool) (rest : Bitstring)
    (hne : headBit :: rest ≠ [])
    (hdel : ¬ ∃ s, headBit :: rest = false :: false :: true :: s) :
    go acc (headBit :: rest) = go (acc ++ [headBit]) rest := by
  rw [go]
  simp [hne, hdel, delim]

theorem go_acc_append (acc pref suffix : Bitstring) (h : delimFree pref) :
    splitDelim.go acc (pref ++ (delim ++ suffix)) = some (acc ++ pref, suffix) := by
  induction pref generalizing acc suffix with
  | nil => simp [go_delim_suffix, List.nil_append]
  | cons b pref' ih =>
    rw [List.cons_append]
    by_cases hdel : ∃ s, b :: (pref' ++ (delim ++ suffix)) = false :: false :: true :: s
    · obtain ⟨s, heq⟩ := hdel
      exfalso
      apply delimFree_cons_append_eq_delim b pref' suffix s h
      rw [delim] at heq
      exact heq
    · rw [go_cons_not_delim acc b (pref' ++ (delim ++ suffix))
        (List.cons_ne_nil _ _) hdel]
      exact ih (acc ++ [b]) suffix fun hsub => h (List.Sublist.cons b hsub)

theorem append (pref suffix : Bitstring) (h : delimFree pref) :
    splitDelim (pref ++ (delim ++ suffix)) = some (pref, suffix) := by
  rw [splitDelim, go_acc_append [] pref suffix h, List.nil_append]

end splitDelim

def encode (inst : NBHInstance) : Bitstring :=
  inst.input ++ (delim ++ (encodeNat inst.machineId ++ (delim ++ encodeNat inst.bound)))

def decode? (s : Bitstring) : Option (NBHInstance × Bitstring) :=
  match splitDelim s with
  | none => none
  | some (input, rest1) =>
    match splitDelim rest1 with
    | none => none
    | some (mid, rest2) =>
      match decodeNat? mid with
      | none => none
      | some (machineId, _) =>
        match decodeNat? rest2 with
        | none => none
        | some (bound, rest3) => some ({ machineId, input, bound }, rest3)

def ntm? (inst : NBHInstance) : Option NTM :=
  lookupMachine? inst.machineId

end NBHInstance

namespace encodeNat

theorem length (n : Nat) : (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeNat, ih]

theorem count_false (n : Nat) : (encodeNat n).count false = 1 := by
  induction n with
  | zero => simp [encodeNat, List.count]
  | succ n ih => simp [encodeNat, List.count_cons, ih, Bool.false_eq_true]

theorem not_sublist_delim (n : Nat) : ¬ List.Sublist NBHInstance.delim (encodeNat n) := by
  intro hsub
  have hle := List.Sublist.count_le (a := false) hsub
  have hdelim : NBHInstance.delim.count false = 2 := by decide
  simpa [count_false, hdelim] using hle

theorem delimFree (n : Nat) : NBHInstance.delimFree (encodeNat n) :=
  not_sublist_delim n

end encodeNat

namespace NBHInstance

theorem decode_encode (inst : NBHInstance) (h : WellFormed inst) :
    decode? (encode inst) = some (inst, []) := by
  simp only [decode?, encode]
  rw [splitDelim.append inst.input (encodeNat inst.machineId ++ (delim ++ encodeNat inst.bound)) h]
  simp only [splitDelim.append (encodeNat inst.machineId) (encodeNat inst.bound)
    (encodeNat.delimFree inst.machineId), decodeNat?.encode]

theorem decode_encode_trivial (inst : NBHInstance) (h : inst.input = []) :
    decode? (encode inst) = some (inst, []) :=
  decode_encode inst (by
    intro hsub
    rw [h] at hsub
    exact (by simp [delim] : delim ≠ []) (List.eq_nil_of_sublist_nil hsub))

end NBHInstance

/-! ### Run certificates -/

structure Config where
  state : Nat
  head : Nat
  tape : Bitstring
  deriving Repr, DecidableEq

namespace Config

def delimFree (tape : Bitstring) : Prop :=
  NBHInstance.delimFree tape

def WellFormed (c : Config) : Prop :=
  delimFree c.tape

def initial (M : NTM) (input : Bitstring) : Config :=
  { state := M.start, head := 0, tape := input }

def step (M : NTM) (c : Config) : Option Config :=
  match NTM.step M c.state c.head c.tape with
  | none => none
  | some (s, h, t) => some { state := s, head := h, tape := t }

def encode (c : Config) : Bitstring :=
  encodeNat c.state ++ (NBHInstance.delim ++
    (encodeNat c.head ++ (NBHInstance.delim ++
      encodeNat c.tape.length ++ (NBHInstance.delim ++ c.tape))))

def decode? (s : Bitstring) : Option (Config × Bitstring) :=
  match NBHInstance.splitDelim s with
  | none => none
  | some (stateBits, rest1) =>
    match decodeNat? stateBits with
    | none => none
    | some (state, _) =>
      match NBHInstance.splitDelim rest1 with
      | none => none
      | some (headBits, rest2) =>
        match decodeNat? headBits with
        | none => none
        | some (head, _) =>
          match NBHInstance.splitDelim rest2 with
          | none => none
          | some (tapeLenBits, rest3) =>
            match decodeNat? tapeLenBits with
            | none => none
            | some (tapeLen, _) =>
              if tapeLen ≤ rest3.length then
                some ({ state, head, tape := rest3.take tapeLen }, rest3.drop tapeLen)
              else
                none

theorem decode_encode (c : Config) : decode? (encode c) = some (c, []) := by
  simp only [decode?, encode]
  rw [NBHInstance.splitDelim.append (encodeNat c.state)
    (encodeNat c.head ++ (NBHInstance.delim ++ encodeNat c.tape.length ++ (NBHInstance.delim ++ c.tape)))
    (encodeNat.delimFree c.state)]
  simp [decodeNat?.encode]
  rw [NBHInstance.splitDelim.append (encodeNat c.head)
    (encodeNat c.tape.length ++ (NBHInstance.delim ++ c.tape)) (encodeNat.delimFree c.head)]
  simp [decodeNat?.encode]
  rw [NBHInstance.splitDelim.append (encodeNat c.tape.length) c.tape (encodeNat.delimFree c.tape.length)]
  simp [decodeNat?.encode, encodeNat.length, if_pos (Nat.le_refl c.tape.length),
    List.take_length, List.drop_length]

theorem decode?_append (c : Config) (rest : Bitstring) :
    decode? (encode c ++ rest) = some (c, rest) := by
  have henc :
      encode c ++ rest =
        encodeNat c.state ++
          (NBHInstance.delim ++
            (encodeNat c.head ++ (NBHInstance.delim ++
              encodeNat c.tape.length ++ (NBHInstance.delim ++ (c.tape ++ rest))))) := by
    simp [encode, List.append_assoc]
  simp only [decode?]
  rw [henc]
  rw [NBHInstance.splitDelim.append (encodeNat c.state)
    (encodeNat c.head ++ (NBHInstance.delim ++ encodeNat c.tape.length ++ (NBHInstance.delim ++ (c.tape ++ rest))))
    (encodeNat.delimFree c.state)]
  simp [decodeNat?.encode]
  rw [NBHInstance.splitDelim.append (encodeNat c.head)
    (encodeNat c.tape.length ++ (NBHInstance.delim ++ (c.tape ++ rest))) (encodeNat.delimFree c.head)]
  simp [decodeNat?.encode]
  rw [NBHInstance.splitDelim.append (encodeNat c.tape.length) (c.tape ++ rest)
    (encodeNat.delimFree c.tape.length)]
  have hle : c.tape.length ≤ (c.tape ++ rest).length := by
    rw [List.length_append]
    exact Nat.le_add_right _ _
  simp [decodeNat?.encode, encodeNat.length, if_pos hle, List.length_take,
    List.take_append, List.drop_append]

theorem encode_length_pos (c : Config) : 0 < (encode c).length := by
  simp [encode, NBHInstance.delim, encodeNat.length]

end Config

def encodeRun (run : List Config) : Bitstring :=
  run.foldl (fun acc c => acc ++ Config.encode c) []

theorem encodeRun_cons (c : Config) (cs : List Config) :
    encodeRun (c :: cs) = Config.encode c ++ encodeRun cs := by
  simp [encodeRun, List.foldl_cons, List.foldl_nil, List.append_nil]

def decodeRun?Fuel : Nat → Bitstring → Option (List Config × Bitstring)
  | 0, _ => none
  | fuel + 1, [] => some ([], [])
  | fuel + 1, s =>
    match Config.decode? s with
    | none => none
    | some (c, rest) =>
      match decodeRun?Fuel fuel rest with
      | none => none
      | some (run, rest') => some (c :: run, rest')

def decodeRun? (s : Bitstring) : Option (List Config × Bitstring) :=
  decodeRun?Fuel (s.length + 1) s

theorem decodeRun?Fuel_ge (fuel : Nat) (run : List Config)
    (h : (encodeRun run).length + 1 ≤ fuel) :
    decodeRun?Fuel fuel (encodeRun run) = some (run, []) := by
  revert fuel
  induction run with
  | nil =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [encodeRun, decodeRun?Fuel]
  | cons c cs ih =>
    intro fuel h
    rw [encodeRun_cons] at h
    rw [List.length_append] at h
    have hpos := Config.encode_length_pos c
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hcs := ih fuel (by omega)
      have hlen : 0 < (c.encode ++ encodeRun cs).length := by
        rw [List.length_append]
        exact Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)
      have hne : c.encode ++ encodeRun cs ≠ [] := List.ne_nil_of_length_pos hlen
      simp [encodeRun_cons, decodeRun?Fuel, Config.decode?_append, hcs, hne]

theorem decodeRun?_encodeRun (run : List Config) :
    decodeRun? (encodeRun run) = some (run, []) := by
  simp [decodeRun?]
  exact decodeRun?Fuel_ge _ _ (Nat.le_refl _)

def runSteps (run : List Config) : Nat :=
  run.length.pred

def runValid (M : NTM) (input : Bitstring) (run : List Config) : Bool :=
  match run with
  | [] => false
  | c0 :: cs =>
    let rec check (prev : Config) (rest : List Config) : Bool :=
      match rest with
      | [] => true
      | c :: rest' =>
        match Config.step M prev with
        | some next => decide (next == c) && check c rest'
        | none => false
    decide (c0 == Config.initial M input) && check c0 cs

def runAccepts (M : NTM) (input : Bitstring) (bound : Nat) (run : List Config) : Bool :=
  runValid M input run &&
  decide (runSteps run ≤ bound) &&
  match run.getLast? with
  | none => false
  | some c => decide (c.state == M.accept)

def verifyRun (inst : NBHInstance) (cert : Bitstring) : Bool :=
  match inst.ntm?, decodeRun? cert with
  | some M, some (run, rest) =>
    decide (rest = [] && runAccepts M inst.input inst.bound run)
  | _, _ => false

/-! ### NBH languages -/

def NBH (inst : NBHInstance) : Prop :=
  match inst.ntm? with
  | none => False
  | some M => ∃ run : List Config, runAccepts M inst.input inst.bound run

def NBHSemantic : Set Bitstring :=
  { s | ∃ inst, NBHInstance.encode inst = s ∧ NBH inst }

def nbhCertBound (n : Nat) : Nat := (n + 1) ^ 2 * 4 + 1

theorem nbhCertBound_poly : IsPolynomial nbhCertBound := by
  refine ⟨100, 2, fun n => ?_⟩
  simp only [nbhCertBound]
  have h : (n + 1) ^ 2 * 4 + 1 ≤ 100 * n ^ 2 + 100 := by
    cases n with
    | zero => decide
    | succ n => nlinarith
  exact h

def verifyNBH (x cert : Bitstring) : Bool :=
  match NBHInstance.decode? x with
  | none => false
  | some (inst, rest) =>
    decide (rest = [] ∧ len cert ≤ nbhCertBound (len x) ∧ verifyRun inst cert = true)

theorem verifyNBH_true_iff (x cert : Bitstring) :
    verifyNBH x cert = true ↔
      match NBHInstance.decode? x with
      | none => False
      | some (inst, rest) =>
        rest = [] ∧ len cert ≤ nbhCertBound (len x) ∧ verifyRun inst cert = true := by
  simp [verifyNBH, decide_eq_true_iff]
  split <;> simp [decide_eq_true_iff, and_assoc]

def NBHChecker : Set Bitstring :=
  { s | ∃ cert, verifyNBH s cert = true }

theorem NBHChecker_in_NP : InNP NBHChecker :=
  InNP.intro nbhCertBound_poly fun x => by
    constructor
    · intro ⟨cert, hver⟩
      cases dec : NBHInstance.decode? x with
      | none =>
        have hf : verifyNBH x cert = false := by simp [verifyNBH, dec]
        rw [hf] at hver
        cases hver
      | some p =>
        obtain ⟨inst, rest⟩ := p
        have hb := (verifyNBH_true_iff x cert).mp hver
        simp [dec] at hb
        exact ⟨cert, hb.2.1, hver⟩
    · intro ⟨cert, _, hver⟩
      exact ⟨cert, hver⟩

/-! ### POL-rankable $`\mu_0`$ -/

def trivialInstance : NBHInstance :=
  { machineId := 0, input := [], bound := 0 }

def μ₀Support : Finset Bitstring :=
  {NBHInstance.encode trivialInstance}

theorem μ₀Support_nonempty : μ₀Support.Nonempty :=
  ⟨NBHInstance.encode trivialInstance, by simp [μ₀Support]⟩

noncomputable def μ₀ : Distribution :=
  uniformOn μ₀Support μ₀Support_nonempty

theorem μ₀_polRankable : IsPolRankable μ₀ :=
  IsPolRankable.uniformOn_polRankable μ₀Support μ₀Support_nonempty

noncomputable def nbhProb : DistributionalProblem :=
  { L := NBHChecker, μ := μ₀ }

theorem nbhProb_in_DistNP : InDistNP nbhProb :=
  InDistNP.intro NBHChecker_in_NP μ₀_polRankable

def trivialCert : Bitstring :=
  encodeRun [Config.initial trivialAcceptNTM []]

theorem trivialInstance_in_NBHChecker :
    NBHInstance.encode trivialInstance ∈ NBHChecker := by
  refine ⟨trivialCert, ?_⟩
  native_decide

theorem μ₀_mass_on_trivial :
    μ₀.prob (NBHInstance.encode trivialInstance) = 1 := by
  simp [μ₀, uniformOn, uniformProb, μ₀Support]

end NBH
