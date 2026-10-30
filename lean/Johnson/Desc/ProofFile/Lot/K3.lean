-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K3.lean: the blocks of the kind "lookup" (K3) in the first chain of a
proof file's description. Definitions with code. No theorem.

Every link of the first chain has two lookups: one on the calls, one on the digits of the smallness
test. This file lists their places and gives the block that stands at each. The block is made by the
kind's own text, `K3.theStated` (Johnson/Desc/First/Look/K3Stated.lean): the kind's rounds, the step
without a round behind them where the protocol has one, and every list of claims that the protocol's
order names at that place, under the order's own names: "objects" and "guests" at every lookup, and
"planes" at the lookup on the calls of an attention link and of the head's link.

The claims under "planes" read the planes' matrix through forms that the calling kind makes.
`readersAt` says which: at the head's link those of the kind K6 (Johnson/Desc/Kinds/HeadCaller.lean,
Johnson/Stored/HeadSeatAt.lean), at an attention link those of the kind K5
(Johnson/Desc/First/Att/SeatO.lean). At a layers' link it gives nothing: there the order names no
"planes".

Main names:
  `addresses Z`: the places of all lookups, link by link.
  `ofForm a`: a linear form, claimed to be 0, as a claim.
  `readersAt X i`: the calling kind's readers at link i.
  `hear Z`: the blocks.
  `lot Z`: the blocks as a lot. They take no part of an instance as a letter, and state no run
    behind the batching.

Limits: where the public record gives no place for a lookup, no block is made for it, and the maker
of the description refuses for want of a block. That the callers' forms read what they are meant to
read is not shown here. Nothing is proved. Nothing on soundness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.Att.SeatO
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace K3Lot
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc

/-- The places of all lookups: link by link, the one on the calls, then the one on the digits. -/
def addresses (Z : ProofFile.Pub) : List (Nat × Bool × Place) :=
  (List.range Z.first.shape.link.length).flatMap fun i => [false, true].map fun dg =>
    (i, dg, (⟨1, some i, K3.pieceAt Z.p.X i dg, .K3⟩ : Place))

/-- A linear form, claimed to be 0, as a claim under its own number's weight. -/
def ofForm (a : Aff) : Claim := { form := a }

/-- The calling kind's readers of the planes' matrix at link i: at the head's link the kind K6's, at
an attention link the kind K5's, at a layers' link none. -/
def readersAt (X : Verify.Public) (i : Nat) : Option (K3.Readers S) :=
  let step := if X.p4 then 2 else 1
  if K3.isHead X i then
    (X.H.tl.ix.U.getD 2 none).map fun iU3 => Kinds.Head.callerReaders (Kinds.Head.planesAt iU3)
  else if i % step == 0 then none
  else X.A[i / step]?.map fun A => First.Att.P.readersOfO A

/-- The blocks: at each place the kind's own whole block, with its listed runs of claims stated. -/
def hear (Z : ProofFile.Pub) : List (Block S Claim) :=
  (addresses Z).filterMap fun x =>
    K3.theStated ofForm (readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape x.2.2

def lot (Z : ProofFile.Pub) : ProofFile.Lot :=
  { name := "K3: the lookups on the calls and on the digits"
    letters := false
    own := fun _ => []
    hearC := fun _ => hear Z
    controls := [] }

end K3Lot
