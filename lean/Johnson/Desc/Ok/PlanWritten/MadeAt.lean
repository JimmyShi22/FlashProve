-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/MadeAt.lean: what is made of the three public files, with the digest of
the files and the second hash function as arguments: `madeOfAtO o pol lay KL c`.

This file holds one definition and no theorem. It is a tool: no description of the protocol is
named. The definition is a copy of `madeOfAt` (Johnson/Desc/Ok/NumberPrices/AtDigest.lean), with
`plannedAtO o` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) where `plannedAt` stands; `sendsFrom` and
`packMade`, of the same file as `madeOfAt`, are called as they are. It was made by a program from
that file's text.

What of OnBytes/Model/ is used: what `plannedAtO` calls.

Limits. It imports a file that holds laws: `sendsFrom` and `packMade` are defined beside theorems on
the rounds' prices. What ties the copy to the text that it was made from is one equation, at
`secondHashFunction` (Johnson/Desc/Ok/PlanWritten/MadeAtLaws.lean). Whether its term reaches a hash by name is a
matter of a walk through the constants that it uses, which is not made here. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.PublicAt
import Johnson.Desc.Ok.NumberPrices.AtDigest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open VerifiableInference.Number
open Johnson.G Johnson.G.OfPlan OnBytes OnBytes.Params OnBytes.Maker
variable (o : Nat → ByteArray → ByteArray)

/-- `madeOfAt` (Johnson/Desc/Ok/NumberPrices/AtDigest.lean) with the second hash function as the
argument o. -/
def madeOfAtO (pol lay KL c : ByteArray) : Except String Made :=
  plannedAtO o pol KL (some lay) c >>= fun p => sendsFrom p.chains.made >>= packMade p

end

end VerifiableInference.PlanWritten
