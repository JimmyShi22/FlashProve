-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K13At4.lean: a second lot of the kind K13 for a proof file's description:
the place "M:4" of the first chain, whole: W's commitment, then the request's own group and the row
(Eval), made of public values (Johnson/Desc/ProofFile/LotCore.lean: Lot).

This file holds definitions only; no theorem is stated.

The place's block is two kinds' blocks joined. W's commitment is the kind K1's own block, by import
and unturned: K1.wAt (Johnson/Desc/K1/Places.lean) at the first chain's parameters. Behind it the
kind K13's rowsB (Johnson/Desc/K13/Kind.lean) is laid by atM4 (Johnson/Desc/K13/AtS.lean). Where the
shape has no message W, the lot has no block.

The kind K1's lot (Johnson/Desc/ProofFile/Lot/K1.lean) leaves this place out.

letters := false: no block of this lot reads a token of the request.

What it imports: of the description's maker LotCore alone, the kind K1's places and the kind K13's
first lot; no stand-in for a step of `verify-on-bytes`, no control, no copy of a text with a test
struck.

Main names: wBlock, lot4.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K1.Places
import Johnson.Desc.ProofFile.Lot.K13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S MemOwn)
open ProofFile (Pub Lot)

/-- Kind K1's own block of W's commitment, at "M:4". Nothing where the shape has no such message. -/
def wBlock (Z : Pub) : Option (Block S Unit) :=
  K1.wAt Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4

/-- **The second lot.** -/
def lot4 (Z : Pub) : Lot :=
  let p := whereOf Z
  { name := "K1 and K13: W's commitment, the request's own group and the row (Eval)"
    letters := false
    own := fun _ => (wBlock Z).toList.map (atM4 p) }

end VerifiableInference.Desc.K13
