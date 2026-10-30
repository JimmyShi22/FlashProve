-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K13End.lean: a third lot for a proof file's description: the first
chain's last block, at the seal's place: the one text for the three chains' ends
(Johnson/Desc/ChainEnd.lean) with the first chain's clauses (Johnson/Desc/K13/FirstEnd.lean:
endAsks), made of public values (Johnson/Desc/ProofFile/LotCore.lean: Lot).

This file holds definitions only; no theorem is stated.

The rounds in front. A lot is no maker of the chain: it is handed the public part alone, not the
blocks that stand in front. So here they are the first chain's declared rounds but the last
(Z.D.1.dropLast). What ties that list to the blocks that really stand in front is a clause of the
description's own test on the plan (FileDescription.planOk: the blocks' rounds in a row are the declared
rounds, whole), at the very field that the description is made with (plans := Z.D): this block's one
round is the row's last, so the rounds in front are the declared ones but the last. Of a round in
front the end's test reads its entry's count of claims alone. A chain's maker calls firstEnd with
its list of blocks instead.

`verify-on-bytes`'s step at this place also asks, in front, what the file's last test asks again
behind the chains (no mark; W was sent): that is not asked here.

letters := false: no block of this lot reads a token of the request.

What it imports: of the description's maker LotCore alone, and the first chain's end's text; no
stand-in for a step of `verify-on-bytes`, no control, no copy of a text with a test struck.

Main names: inFrontOf, lotEnd.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K13.FirstEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open VerifiableInference.Desc.First (S endAsks)
open ProofFile (Pub Lot)

/-- The first chain's declared rounds but the last. -/
def inFrontOf (Z : Pub) : List Fmt.DeclaredRound := Z.D.1.dropLast

/-- **The third lot.** -/
def lotEnd (Z : Pub) : Lot :=
  let e : Block S Unit := ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks
  { name := "the end of the first chain"
    letters := false
    own := fun _ => [e] }

end VerifiableInference.Desc.K13
