-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Reader.lean: the strict reader of a chain, in the form that `program`
(OnBytes/Shell/Checks.lean) calls.

The directory Fmt/ states the strict reader as `Fmt.readChainX`. `program` calls the text of
OnBytes/Chain/Engine.lean: with the hash and the step of a chain of OnBytes/Hash/, which work on
machine words, and with a map for the record of vertices (OnBytes/Chain/Index.lean). So does `main`
(OnBytes/Main.lean) in the calls on the files of the test protocols (OnBytes/Shell/Toys.lean). In
the calls verify, verify -key and verify -leaf on a model's files `main` runs a second text, written
over a monad (OnBytes/ChecksWithHashAsArgument/M/Chain/), at the identity monad and `formatHashFastForm`; there its `readChain`
returns what this one returns, for all arguments (`readChain_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean): an equation between terms, which says nothing of compiled
code.
OnBytes/Chain/ReaderLaws.lean proves that this file's `readChain` returns what `Fmt.readChainX`
returns at the identity monad and `Fmt.formatHash`, for every description, every record and all bytes
(`readChain_eq`).
The C++ counterparts are named in OnBytes/Chain/Engine.lean.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `readChain`, `viewOf`.
Not claimed: how fast the reader is.
-/
import OnBytes.Base
import OnBytes.Chain.Engine
import OnBytes.Chain.Index
import OnBytes.Hash.H
import OnBytes.Hash.Query

namespace OnBytes

/-- Reads the chain that begins at byte i of b, as `Fmt.readChainX` does. S is the chain's
description. `seen` is the record of tree vertices met so far in this verdict (format page, R7.14).
Returns what was read and the place after the chain. Returns nothing if the description is not in
order (`Fmt.SpecX.ok`), whatever the bytes, or if the bytes break a rule of the format. -/
def readChain (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    Option (Fmt.ChainOut × Nat) :=
  readChainK Keeper.indexed queryH formatHashFastForm S seen b i

/-- What a decision sees of a chain that was read, as `Fmt.viewX` gives it. -/
def viewOf (S : Fmt.SpecX) (o : Fmt.ChainOut) : Fmt.View := viewF S o

end OnBytes
