-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K13.lean: the kind K13's lot for a proof file's description: its own
block at the place "M:3" of the first chain, behind the links: the members' batching
(Johnson/Desc/K13/AtS.lean: atM3), made of public values (Johnson/Desc/ProofFile/LotCore.lean: Lot).

This file holds definitions only; no theorem is stated.

whereOf Z gives the kind's numbers off the public part: rows and lin are the first chain's
parameters'; sent is counted off the declared rounds in front of the stretch; work is read off the
plan's stretch itself, so the test of the block's rounds against the plan's says nothing of that
word (it is 0 at both stored plans). The stretch is found by the name of its first drawing step,
"M.0.call", in the public part's table of stretches (fromOf?). Where that name is not found there is
no number to read: the lot's block then fails its own test on the plan, so the description is
refused at "M:3"; no default stands in for the number.

letters := false: no block of this lot reads a token of the request.

What it imports: of the description's maker LotCore alone, and the kind's text at the carried
record; no stand-in for a step of `verify-on-bytes`, no control, no copy of the text with a test
struck.

Main names: fromOf?, fromOf, whereOf, lot.

What is not claimed. That the place is the kind's only place on a plan. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K13.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S)
open ProofFile (Pub Lot)

/-- The number of the round "BAT-sigma" of the members' batching on the first chain, from 0; none
where the table of stretches has no step of that name. -/
def fromOf? (Z : Pub) : Option Nat := Z.roundsBefore? "M.0.call"

/-- The same; 0 where there is none: the lot's block then fails its test on the plan (lot). -/
def fromOf (Z : Pub) : Nat := (fromOf? Z).getD 0

/-- The kind's numbers. -/
def whereOf (Z : Pub) : Where :=
  let w := fun (i : Nat) => ((Z.plans.1[fromOf Z + i]?).map (·.work)).getD 0
  { chain := 1, piece := 3, pieceRows := 4, rows := Z.first.pendingRows, lin := Z.first.lin,
    work := (w 0, w 1, w 2), sent := ((Z.D.1.take (fromOf Z)).map (·.entry.roots)).sum }

/-- **The lot.** Where the table of stretches has no step "M.0.call" the block's numbers cannot be
read off the public part: the block then fails its test on the plan. -/
def lot (Z : Pub) : Lot :=
  let b : Block S Unit := atM3 (whereOf Z)
  { name := "K13: the members' batching"
    letters := false
    own := fun _ => [{ b with planOk := b.planOk && (fromOf? Z).isSome }] }

end VerifiableInference.Desc.K13
