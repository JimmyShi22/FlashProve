-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/PubReq.lean: what is public about the two big files, where the instances are the
requests that the program's reader takes.

Definitions, and two equations. `pubOf p P hV` (Johnson/Flat/PubOf.lean) is typed at all instances.
Johnson/Flat/LedgerClaim.lean cuts the instances at the reference sizes to `Req`: those with r < e,
and y = 0 if e is before the window's end. `pubReq p : Pub Req` is `pubOf p ppref` read at a
request's instance: the first query binds the request with the reply's word 0 (`early` :=
`reqWithoutReply`), no later query holds it (`late` := none), and the reply is a plain message of
the prover in the round REPLY, which the decision compares with the request's. The dry runs are made
at the same instance as there.

Limits: those of Johnson/Flat/PubOf.lean, with the condition that its section "The two typings of
the reply" keeps in sight. The reference sizes alone.

-/
import Johnson.Flat.PubOf
import Johnson.Flat.LedgerClaim

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model VerifiableInference.OnPublicFiles.Flat

/-- The vocabulary of the reference sizes has a token. -/
theorem ppref_V_pos : 0 < ppref.V := by decide

/-- The instance at which the dry runs are made, as a request. -/
def firstReq : Req :=
  ⟨firstInstance ppref ppref_V_pos, by decide, fun h => absurd h (by decide)⟩

/-- A request with the reply 0. -/
def reqWithoutReply (x : Req) : Req :=
  ⟨withoutReply ppref_V_pos x.val, x.property.1, fun _ => rfl⟩

/-- **What is public about the two big files**, at the requests that the reader takes. -/
def pubReq (p : Verify.Planned) : Pub Req where
  k := keyChains p
  c := proofChains p
  table := blankTable p
  links := fun x => linksOf p x.val
  reply := fun x => replyOf x.val
  x₀ := firstReq
  key₀ := zeroKey p
  maxRt := 2
  N := slots p
  early := reqWithoutReply
  late := none

/-- The two fields on the reply are those of `pubOf`. -/
theorem pubReq_early (p : Verify.Planned) (x : Req) :
    (pubReq p).late = (pubOf p ppref ppref_V_pos).late ∧
      ((pubReq p).early x).val = (pubOf p ppref ppref_V_pos).early x.val := ⟨rfl, rfl⟩

/-- The first chain's block at a request is that of `pubOf` at its instance. -/
theorem pubReq_block (p : Verify.Planned) (x : Req) :
    (pubReq p).block x = (pubOf p ppref ppref_V_pos).block x.val := rfl

end OnBytes.Flat
