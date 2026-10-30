-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/Session.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Chain/Session.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader

namespace OnBytes.TwoPort.M

/-- A reading within a session over a monad m, in which the hash is asked. -/
abbrev InSessionM (m : Type → Type) : Type → Type := StateT Session (OptionT m)

/-- Reads the chain with the description S that begins at byte i of b. No decision is taken. -/
def readIn {m : Type → Type} [Monad m] (hh : HashM m) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    InSessionM m ChainRead := fun s => OptionT.mk do
  match ← readChain hh S s.seen b i with
  | none => pure none
  | some (o, j) => pure (some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩))

/-- Reads the chain c that begins at byte i of b and decides on it for the statement y. -/
def acceptIn {Y : Type} {m : Type → Type} [Monad m] (hh : HashM m) (c : Chain Y) (y : Y)
    (b : ByteArray) (i : Nat) :
    InSessionM m ChainRead := fun s => OptionT.mk do
  match ← readChain hh c.spec s.seen b i with
  | none => pure none
  | some (o, j) =>
    pure (if c.dec y (viewOf c.spec o) then some (⟨o, viewOf c.spec o, j⟩, ⟨o.seen⟩) else none)

end OnBytes.TwoPort.M
