-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/Reader.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Chain/Reader.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.
The step of a chain is no argument here: it is `Fmt.Chain.queryW` at the hash (Fmt/Rules5.lean),
which hashes a round's message anew in each of the round's calls. The port's step `queryH` hashes
once what the calls share; at `formatHashFastForm` the two are equal (`step_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean). Where the root's `main` is `programFront`
(OnBytes/Shell/Front.lean), it runs this text at the identity monad and `formatHashFastForm`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM

namespace OnBytes.TwoPort.M

/-- Reads the chain that begins at byte i of b, as `Fmt.readChainX` does. S is the chain's
description. `seen` is the record of tree vertices met so far in this verdict (format page, R7.14).
Returns what was read and the place after the chain. Returns nothing if the description is not in
order (`Fmt.SpecX.ok`), whatever the bytes, or if the bytes break a rule of the format. -/
def readChain {m : Type → Type} [Monad m] (hh : HashM m) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) : m (Option (Fmt.ChainOut × Nat)) :=
  readChainM Keeper.indexed hh S seen b i

end OnBytes.TwoPort.M
