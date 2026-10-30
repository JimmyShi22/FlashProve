-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/Reading.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Proof/Reading.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

/-- A reading within a session that names the step at which it refuses, over a monad m in which the
hash is asked. -/
abbrev Reading (m : Type → Type) : Type → Type := StateT Session (ExceptT String m)

section

variable {m : Type → Type} [Monad m]

/-- The value of x, or a refusal under the name `why`. -/
def need {α : Type} (why : String) (x : Option α) : Reading m α := fun s =>
  ExceptT.mk (pure (match x with
    | none => .error why
    | some a => .ok (a, s)))

/-- The value that the computation x returns, or a refusal under the name `why`. -/
def needM {α : Type} (why : String) (x : m (Option α)) : Reading m α := fun s =>
  ExceptT.mk do
    match ← x with
    | none => pure (.error why)
    | some a => pure (.ok (a, s))

/-- Runs a reading from the empty record of vertices. -/
def Reading.fromStart {α : Type} (w : Reading m α) : m (Except String α) := do
  let r ← (w Session.start).run
  pure (r.map (·.1))

/-- The name of a refusal by the strict reader. -/
def readerName (hh : HashM m) (front : String) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : Nat) : m String := do
  match ← whyRefused hh S seen b i with
  | some (k, _) => pure (front ++ "reader-" ++ k.name)
  | none => pure (front ++ "reader")

/-- Reads the chain with the description S that begins at byte i of b. A refusal says which chain
it was and which kind of check fails first in a second pass over the chain. -/
def readNamed (hh : HashM m) (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    Reading m ChainRead := fun s =>
  ExceptT.mk do
    match ← (readIn hh S b i s).run with
    | some y => pure (.ok y)
    | none => do
      let n ← readerName hh front S s.seen b i
      pure (.error n)

end

end OnBytes.TwoPort.M.Proof
