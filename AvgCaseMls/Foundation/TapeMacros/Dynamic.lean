import AvgCaseMls.Foundation.TapeMacros.Serialization

/-!
# Uniform runtime-input tape routines

Unlike the static assembler templates, every machine in this file is a closed
constant.  `duplicateMachine` destructively transfers an arbitrary runtime
block to the right of a blank separator, writing two copies of each consumed
cell.  Its code is independent of the input.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

/-- Cell-doubled encoding; this is injective and self-synchronizing in pairs. -/
def duplicateEncoding (bits : Bitstring) : Bitstring :=
  bits.flatMap fun bit => [bit, bit]

@[simp] theorem duplicateEncoding_nil : duplicateEncoding [] = [] := rfl

@[simp] theorem duplicateEncoding_cons (bit : Bool) (bits : Bitstring) :
    duplicateEncoding (bit :: bits) =
      bit :: bit :: duplicateEncoding bits := by
  simp [duplicateEncoding]

@[simp] theorem duplicateEncoding_length (bits : Bitstring) :
    (duplicateEncoding bits).length = 2 * bits.length := by
  simp [duplicateEncoding]
  omega

theorem duplicateEncoding_injective : Function.Injective duplicateEncoding := by
  intro first
  induction first with
  | nil =>
      intro second h
      cases second with
      | nil => rfl
      | cons bit rest => simp at h
  | cons bit rest ih =>
      intro second h
      cases second with
      | nil => simp at h
      | cons bit' rest' =>
          simp only [duplicateEncoding_cons] at h
          have hbit : bit = bit' := by simpa using congrArg List.head? h
          subst bit'
          have htail : duplicateEncoding rest = duplicateEncoding rest' := by
            simpa using congrArg (List.drop 2) h
          exact congrArg (List.cons bit) (ih htail)

/--
Uniform destructive block duplicator.

The source is consumed left-to-right.  A blank marks each consumed source
cell.  The remembered finite-control bit is appended twice beyond a permanent
blank separator.  The return sweep locates the next unconsumed source cell.
-/
def duplicateMachine : Machine :=
  ⟨#[
    .branch 18 1 2,  -- 0: dispatch source bit
    .write none 6,   -- 1: remember false, then leave marker
    .write none 14,  -- 2: remember true, then leave marker
    .branch 5 6 6,   -- 3: scan source right, false state
    .branch 13 14 14,-- 4: scan source right, true state
    .moveRight 7,    -- 5: cross separator
    .moveRight 3,    -- 6
    .branch 8 9 9,   -- 7: scan emitted block right
    .write (some false) 10, -- 8
    .moveRight 7,    -- 9
    .moveRight 11,   -- 10
    .write (some false) 12, -- 11
    .moveLeft 21,    -- 12: begin common return
    .moveRight 15,   -- 13: cross separator
    .moveRight 4,    -- 14
    .branch 16 17 17,-- 15: scan emitted block right
    .write (some true) 19,  -- 16
    .moveRight 15,   -- 17
    .halt true,      -- 18
    .moveRight 20,   -- 19
    .write (some true) 12,  -- 20
    .branch 22 23 23,-- 21: scan emitted block left
    .moveLeft 24,    -- 22: cross separator
    .moveLeft 21,    -- 23
    .branch 25 26 26,-- 24: scan remaining source left
    .moveRight 0,    -- 25: enter next source cell
    .moveLeft 24     -- 26
  ]⟩

theorem duplicateMachine_fixed (_bits₁ _bits₂ : Bitstring) :
    duplicateMachine = duplicateMachine := rfl

def duplicateTime (n : Nat) : Nat := 6 * n * n + 10 * n + 2

theorem duplicateTime_polynomial : IsPolynomial duplicateTime :=
  .bounded 15 2 (fun n => by
    simp [duplicateTime]
    nlinarith)

/-- Runtime framing is duplicated by the same fixed machine. -/
def duplicateFramedEncoding (payload : Bitstring) : Bitstring :=
  duplicateEncoding (frame payload)

@[simp] theorem duplicateFramedEncoding_length (payload : Bitstring) :
    (duplicateFramedEncoding payload).length = 2 * (frame payload).length := by
  simp [duplicateFramedEncoding]

/--
The semantic contract used by callers.  It quantifies over runtime input;
there is no source-indexed machine in the statement.
-/
def DuplicateContract : Prop :=
  ∀ bits, eval duplicateMachine (duplicateTime bits.length) bits =
    some ⟨true, duplicateEncoding bits, duplicateTime bits.length⟩

private def symbols (bits : Bitstring) : List TapeSymbol :=
  bits.map some

private def atCells (pc : Nat) (left : List TapeSymbol) :
    List TapeSymbol → Config
  | [] => ⟨pc, left, none, []⟩
  | symbol :: right => ⟨pc, left, symbol, right⟩

private inductive Runs (M : Machine) : Config → Nat → Config → Prop
  | refl (c) : Runs M c 0 c
  | next (hstep : step M c = .ok c') (hrun : Runs M c' n d) :
      Runs M c (n + 1) d

private theorem Runs.trans {M : Machine} {a b c : Config} {m n : Nat}
    (hab : Runs M a m b) (hbc : Runs M b n c) :
    Runs M a (m + n) c := by
  induction hab with
  | refl => simpa using hbc
  | next hstep hrun ih =>
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using
        (Runs.next hstep (ih hbc))

private theorem Runs.evalFrom_eq {M : Machine} {c d : Config} {n : Nat}
    (hrun : Runs M c n d) (fuel elapsed : Nat) :
    evalFrom M (n + fuel) c elapsed =
      evalFrom M fuel d (elapsed + n) := by
  induction hrun generalizing elapsed with
  | refl => simp
  | next hstep hrun ih =>
      rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]
      simp only [evalFrom, hstep]
      convert ih (elapsed + 1) using 1 <;> ac_rfl

private theorem Runs.halt {M : Machine} {c d : Config} {n elapsed : Nat}
    {result : Result} (hrun : Runs M c n d)
    (hhalt : step M d = .error result) :
    evalFrom M (n + 1) c elapsed =
      some { result with steps := elapsed + n + 1 } := by
  rw [hrun.evalFrom_eq 1 elapsed]
  simp [evalFrom, hhalt, Nat.add_assoc]

private theorem Runs.two {M : Machine} {a b c : Config}
    (hab : step M a = .ok b) (hbc : step M b = .ok c) :
    Runs M a 2 c := by
  exact .next hab (.next hbc (.refl _))

private theorem sourceRightFalse (rest out : Bitstring)
    (left : List TapeSymbol) :
    Runs duplicateMachine
      (atCells 3 left (symbols rest ++ none :: symbols out))
      (2 * rest.length + 2)
      (atCells 7 (none :: (symbols rest).reverse ++ left) (symbols out)) := by
  induction rest generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit rest ih =>
      have htwo : Runs duplicateMachine
          (atCells 3 left (symbols (bit :: rest) ++ none :: symbols out)) 2
          (atCells 3 (some bit :: left)
            (symbols rest ++ none :: symbols out)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem sourceRightTrue (rest out : Bitstring)
    (left : List TapeSymbol) :
    Runs duplicateMachine
      (atCells 4 left (symbols rest ++ none :: symbols out))
      (2 * rest.length + 2)
      (atCells 15 (none :: (symbols rest).reverse ++ left) (symbols out)) := by
  induction rest generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit rest ih =>
      have htwo : Runs duplicateMachine
          (atCells 4 left (symbols (bit :: rest) ++ none :: symbols out)) 2
          (atCells 4 (some bit :: left)
            (symbols rest ++ none :: symbols out)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem sourceRightFalseInitialAux (rest : Bitstring)
    (left : List TapeSymbol) :
    Runs duplicateMachine (atCells 3 left (symbols rest))
      (2 * rest.length + 2)
      (atCells 7 (none :: (symbols rest).reverse ++ left) []) := by
  induction rest generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit rest ih =>
      have htwo : Runs duplicateMachine
          (atCells 3 left (symbols (bit :: rest))) 2
          (atCells 3 (some bit :: left) (symbols rest)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem sourceRightTrueInitialAux (rest : Bitstring)
    (left : List TapeSymbol) :
    Runs duplicateMachine (atCells 4 left (symbols rest))
      (2 * rest.length + 2)
      (atCells 15 (none :: (symbols rest).reverse ++ left) []) := by
  induction rest generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit rest ih =>
      have htwo : Runs duplicateMachine
          (atCells 4 left (symbols (bit :: rest))) 2
          (atCells 4 (some bit :: left) (symbols rest)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem appendFalse (out : Bitstring) (left : List TapeSymbol) :
    Runs duplicateMachine (atCells 7 left (symbols out))
      (2 * out.length + 5)
      ⟨21, (symbols out).reverse ++ left, some false, [some false]⟩ := by
  induction out generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.refl _)))))
  | cons bit out ih =>
      have htwo : Runs duplicateMachine
          (atCells 7 left (symbols (bit :: out))) 2
          (atCells 7 (some bit :: left) (symbols out)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem appendTrue (out : Bitstring) (left : List TapeSymbol) :
    Runs duplicateMachine (atCells 15 left (symbols out))
      (2 * out.length + 5)
      ⟨21, (symbols out).reverse ++ left, some true, [some true]⟩ := by
  induction out generalizing left with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.next (by rfl)
        (.next (by rfl) (.next (by rfl) (.refl _)))))
  | cons bit out ih =>
      have htwo : Runs duplicateMachine
          (atCells 15 left (symbols (bit :: out))) 2
          (atCells 15 (some bit :: left) (symbols out)) := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih (some bit :: left)) using 1 <;>
        simp [symbols] <;> omega

private theorem returnAcrossOutput (cells : List Bool) (bit : Bool)
    (left : List TapeSymbol) (right : List TapeSymbol) :
    Runs duplicateMachine
      ⟨21, symbols cells ++ none :: left, some bit, right⟩
      (2 * (cells.length + 1))
      ⟨21, left, none, (symbols cells).reverse ++ some bit :: right⟩ := by
  induction cells generalizing bit right with
  | nil =>
      cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons next cells ih =>
      have htwo : Runs duplicateMachine
          ⟨21, symbols (next :: cells) ++ none :: left, some bit, right⟩ 2
          ⟨21, symbols cells ++ none :: left, some next,
            some bit :: right⟩ := by
        cases bit <;> refine .next (by rfl) (.next (by rfl) (.refl _))
      convert htwo.trans (ih next (some bit :: right)) using 1 <;>
        simp [symbols] <;> omega

private def leftCells (pc : Nat) (left : List TapeSymbol)
    (right : List TapeSymbol) : Bitstring → Config
  | [] => ⟨pc, left, none, right⟩
  | bit :: bits => ⟨pc, symbols bits ++ none :: left, some bit, right⟩

private theorem returnAcrossSource (cells : Bitstring)
    (left right : List TapeSymbol) :
    Runs duplicateMachine (leftCells 24 left right cells)
      (2 * cells.length + 2)
      (atCells 0 (none :: left) ((symbols cells).reverse ++ right)) := by
  induction cells generalizing right with
  | nil =>
      refine .next (by rfl) (.next (by rfl) (.refl _))
  | cons bit cells ih =>
      have htwo : Runs duplicateMachine
          (leftCells 24 left right (bit :: cells)) 2
          (leftCells 24 left (some bit :: right) cells) := by
        cases bit <;> refine .next (by rfl) (.next (by
          cases cells <;> rfl) (.refl _))
      convert htwo.trans (ih (some bit :: right)) using 1 <;>
        simp [leftCells, symbols, atCells] <;> omega

private theorem duplicateCycle (k : Nat) (bit : Bool)
    (rest out : Bitstring) :
    Runs duplicateMachine
      (atCells 0 (List.replicate k none)
        (some bit :: symbols rest ++ none :: symbols out))
      (4 * rest.length + 4 * out.length + 16)
      (atCells 0 (List.replicate (k + 1) none)
        (symbols rest ++ none :: symbols (out ++ [bit, bit]))) := by
  have hstart : Runs duplicateMachine
      (atCells 0 (List.replicate k none)
        (some bit :: symbols rest ++ none :: symbols out)) 3
      (atCells (if bit then 4 else 3) (none :: List.replicate k none)
        (symbols rest ++ none :: symbols out)) := by
    cases bit <;> refine .next (by rfl) (.next (by rfl)
      (.next (by rfl) (.refl _)))
  have hright : Runs duplicateMachine
      (atCells (if bit then 4 else 3) (none :: List.replicate k none)
        (symbols rest ++ none :: symbols out))
      (2 * rest.length + 2)
      (atCells (if bit then 15 else 7)
        (none :: (symbols rest).reverse ++ none :: List.replicate k none)
        (symbols out)) := by
    cases bit
    · simpa using sourceRightFalse rest out (none :: List.replicate k none)
    · simpa using sourceRightTrue rest out (none :: List.replicate k none)
  have happend : Runs duplicateMachine
      (atCells (if bit then 15 else 7)
        (none :: (symbols rest).reverse ++ none :: List.replicate k none)
        (symbols out))
      (2 * out.length + 5)
      ⟨21, (symbols out).reverse ++ none :: (symbols rest).reverse ++
        none :: List.replicate k none, some bit, [some bit]⟩ := by
    cases bit
    · convert appendFalse out
        (none :: (symbols rest).reverse ++ none :: List.replicate k none)
        using 1 <;> simp
    · convert appendTrue out
        (none :: (symbols rest).reverse ++ none :: List.replicate k none)
        using 1 <;> simp
  have houtput := returnAcrossOutput out.reverse bit
    ((symbols rest).reverse ++ none :: List.replicate k none) [some bit]
  have houtput' : Runs duplicateMachine
      ⟨21, (symbols out).reverse ++ none :: (symbols rest).reverse ++
        none :: List.replicate k none, some bit, [some bit]⟩
      (2 * (out.length + 1))
      ⟨21, (symbols rest).reverse ++ none :: List.replicate k none,
        none, symbols out ++ [some bit, some bit]⟩ := by
    simpa [symbols, List.append_assoc] using houtput
  have hcross : Runs duplicateMachine
      ⟨21, (symbols rest).reverse ++ none :: List.replicate k none,
        none, symbols out ++ [some bit, some bit]⟩ 2
      (leftCells 24 (List.replicate k none)
        (none :: symbols (out ++ [bit, bit])) rest.reverse) := by
    refine .next (by rfl) (.next (by
      rw [show (symbols rest).reverse = symbols rest.reverse by simp [symbols]]
      cases rest.reverse <;>
        simp [leftCells, symbols, step, duplicateMachine, moveLeft]) (.refl _))
  have hsource := returnAcrossSource rest.reverse (List.replicate k none)
    (none :: symbols (out ++ [bit, bit]))
  have hall := hstart.trans (hright.trans
    (happend.trans (houtput'.trans (hcross.trans hsource))))
  convert hall using 1
  all_goals
    simp [symbols, List.append_assoc, List.replicate_succ] <;> try ring

private theorem duplicateCycleInitial (bit : Bool) (rest : Bitstring) :
    Runs duplicateMachine (initial (bit :: rest))
      (4 * rest.length + 16)
      (atCells 0 [none]
        (symbols rest ++ none :: symbols [bit, bit])) := by
  have hstart : Runs duplicateMachine (initial (bit :: rest)) 3
      (atCells (if bit then 4 else 3) [none] (symbols rest)) := by
    cases bit <;> refine .next (by rfl) (.next (by rfl)
      (.next (by rfl) (.refl _)))
  have hright : Runs duplicateMachine
      (atCells (if bit then 4 else 3) [none] (symbols rest))
      (2 * rest.length + 2)
      (atCells (if bit then 15 else 7)
        (none :: (symbols rest).reverse ++ [none]) []) := by
    cases bit
    · simpa using sourceRightFalseInitialAux rest [none]
    · simpa using sourceRightTrueInitialAux rest [none]
  have happend : Runs duplicateMachine
      (atCells (if bit then 15 else 7)
        (none :: (symbols rest).reverse ++ [none]) []) 5
      ⟨21, none :: (symbols rest).reverse ++ [none],
        some bit, [some bit]⟩ := by
    cases bit
    · convert appendFalse [] (none :: (symbols rest).reverse ++ [none])
        using 1 <;> simp [symbols]
    · convert appendTrue [] (none :: (symbols rest).reverse ++ [none])
        using 1 <;> simp [symbols]
  have houtput := returnAcrossOutput ([] : Bitstring) bit
    ((symbols rest).reverse ++ [none]) [some bit]
  have houtput' : Runs duplicateMachine
      ⟨21, none :: (symbols rest).reverse ++ [none],
        some bit, [some bit]⟩ 2
      ⟨21, (symbols rest).reverse ++ [none], none, [some bit, some bit]⟩ := by
    simpa [symbols] using houtput
  have hcross : Runs duplicateMachine
      ⟨21, (symbols rest).reverse ++ [none], none, [some bit, some bit]⟩ 2
      (leftCells 24 [] (none :: symbols [bit, bit]) rest.reverse) := by
    refine .next (by rfl) (.next (by
      rw [show (symbols rest).reverse = symbols rest.reverse by simp [symbols]]
      cases rest.reverse <;>
        simp [leftCells, symbols, step, duplicateMachine, moveLeft]) (.refl _))
  have hsource := returnAcrossSource rest.reverse []
    (none :: symbols [bit, bit])
  have hall := hstart.trans (hright.trans
    (happend.trans (houtput'.trans (hcross.trans hsource))))
  convert hall using 1
  all_goals
    simp [symbols, List.append_assoc, List.replicate_succ] <;> try ring

private theorem duplicateLoop (k : Nat) (bits out : Bitstring)
    (hout : out.length = 2 * k) :
    Runs duplicateMachine
      (atCells 0 (List.replicate k none)
        (symbols bits ++ none :: symbols out))
      (6 * bits.length * bits.length + 8 * k * bits.length +
        10 * bits.length + 1)
      ⟨18, List.replicate (k + bits.length) none, none,
        symbols (out ++ duplicateEncoding bits)⟩ := by
  induction bits generalizing k out with
  | nil =>
      simpa [atCells, symbols] using
        (Runs.next (M := duplicateMachine) (c' :=
          ⟨18, List.replicate k none, none, symbols out⟩)
          (by rfl) (.refl _))
  | cons bit rest ih =>
      have hcycle := duplicateCycle k bit rest out
      have hout' : (out ++ [bit, bit]).length = 2 * (k + 1) := by
        simp [hout]
        omega
      have htail := ih (k + 1) (out ++ [bit, bit]) hout'
      have hrun := hcycle.trans htail
      convert hrun using 1
      all_goals
        simp [duplicateEncoding_cons, List.append_assoc, symbols,
          List.replicate_succ, Nat.add_comm, hout] <;> try ring

/-- The fixed 27-instruction machine duplicates every runtime input exactly. -/
theorem duplicateContract : DuplicateContract := by
  intro bits
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      have hfirst := duplicateCycleInitial bit rest
      have hloop := duplicateLoop 1 rest [bit, bit] (by simp)
      have hrun := hfirst.trans hloop
      have hhalt : step duplicateMachine
          ⟨18, List.replicate (1 + rest.length) none, none,
            symbols ([bit, bit] ++ duplicateEncoding rest)⟩ =
          .error ⟨true, [bit, bit] ++ duplicateEncoding rest, 0⟩ := by
        simp [step, duplicateMachine, tapeOutput, symbols]
      have heval := hrun.halt hhalt (elapsed := 0)
      convert heval using 1
      all_goals
        simp [eval, duplicateTime, duplicateEncoding_cons] <;> try ring

end AvgCaseMls.Foundation.TapeMacros
