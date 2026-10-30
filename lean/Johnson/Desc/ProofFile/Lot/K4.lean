-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K4.lean: the lot of K4, the layers' own rounds. A lot (`Lot`,
LotCore.lean) is the named table in which a module hands its blocks to the proof file's description.
Code alone: no theorem. A segment is a `Link` of Johnson/Desc/Block.lean (the code says "link"). A
step is one of `verify-on-bytes`'s named steps; `Pub.cuts` cuts the first chain's rounds into them.

The places. One in each layers' segment of the first chain (but see Limits), named after the
segment, «G‹i›:3»: chain 1, the segment's number, piece 3.

The blocks. `blockAtC` (Johnson/Desc/First/K4/AtC.lean): K4's block at the carried record `S`, its
claims at the type `Cl`. The blocks stand in `hearC`, not in `own`, because they state lists under
the names of the driver's order (`orderCuts`, Johnson/Desc/First/Driver/Chain.lean, fixes in which
order a segment's lists are added): the lists of claims "front" and "back", and "free-slot" after
the batching.

The parameters. Of the segments' records G this file reads `built` and `W`, not `cov`, which holds
the request's tokens; the block takes the tokens from the state (`S.tokv`). So what the lot makes
does not depend on the request's tokens: `letters := false`. A place gets the layers' public record,
the plan of the segment's group of layers, the group's number, and `before`: the oracle messages
(chain 1; number of sending, from 0) that the segment's own first place sends, and, from the second
layers' segment on, those that the layers' segment before sends at its first place. By the format's
page (cited in Johnson/Desc/First/K4/Block.lean) this is everything that a segment commits at its
start (the format's moment 0), whether or not K4's claims use it; of the segment before it is a
superset of the one message that holds its outgoing stream.

Where the plan is refused. A place gets K4's block with its test on the plan false if, for the
segment itself or for the layers' segment before, `Pub.cuts` has no step «‹segment›.0.call», or the
segment's first place sends no oracle message. Leaving the place empty would not do: in a
description over stand-ins (blocks that wrap `verify-on-bytes`'s steps), whose lists bear the names
of K4's lists and hold no claims, the test that some block states each list that the order names
(LotCore.lean) would pass with none of K4's claims added.

Limits.
Still no block is laid where the segments' records have no plan for the segment's group
(`G.W.G[X.g]?` is none): K4's parameters cannot be made without one. The place is then left empty,
with the danger just named, and this file refuses nothing there.
`k3Runs := true` at every place: in the driver's order of a layers' segment K3's block states the
lookup's own claims (the format's group 1) as its list "objects"; K4's "front" then begins at group
2 and does not mark them as added. K4's text (Johnson/Desc/First/K4/Block.lean) says that K3's list
must stand right in front of "front"; the driver's order (`orderCuts`) has K3's list "guests"
between the two. If that list holds any claim in a layers' segment, the numbers of all claims after
it move, and if it holds K4's group 10, that group is added twice. Nothing here tests that it is
empty. `theOwn` (Johnson/Desc/First/Look/K3Own.lean) makes K3's blocks with an empty list of guests.
The lot brings no controls (`controls := []`). No theorem or test of this library shows a place of
this lot refused on account of the layers' segment before it.
`still` is left at its default, the empty list: by LotCore.lean the lot thereby says that its blocks
run none of `verify-on-bytes`'s steps, and nothing tests that.
No command or evaluation of this library runs the decisions of this lot's blocks. Nothing on
soundness.
-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.First.K4.AtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- How many roots a list of declared rounds sends. -/
def k4Roots (l : List Fmt.DeclaredRound) : Nat := l.foldl (fun a r => a + r.entry.roots) 0

/-- The oracle messages that the first place of the segment of that name sends: chain 1; the number
of sending, from 0. k: the rounds before the step «‹link›.0.call»; n: the rounds of all steps
«‹link›.0.…»; the n rounds are taken from k on, which is right only if these steps stand in a row
that begins with «‹link›.0.call». `none`: `Z.cuts` has no step «‹link›.0.call». -/
def k4Sent (Z : Pub) (link : String) : Option (List (Nat × Nat)) :=
  (Z.roundsBefore? (link ++ ".0.call")).map fun k =>
    let n := (Z.cuts.filter fun c => c.look.startsWith (link ++ ".0.")).foldl (· + ·.take) 0
    (List.range (k4Roots ((Z.D.1.drop k).take n))).map fun i => (1, k4Roots (Z.D.1.take k) + i)

/-- The parameters of K4's places in the segments from number l on, each with a Bool: false where
the plan is refused at the place (see the head). last: the name of the layers' segment before, if
there is one. -/
def k4From (Z : Pub) (G : Ground) : List LinkH → Nat → Option String →
    List (Bool × OnBytes.Desc.First.K4.Par)
  | [], _, _ => []
  | X :: rest, l, last =>
    if X.kind == 0 then
      (match G.W.G[X.g]? with
       | some hp =>
         let here := k4Sent Z X.name
         let prev := last.elim (some []) (k4Sent Z)
         [((here.any fun m => !m.isEmpty) && (last.all fun _ => prev.any fun m => !m.isEmpty),
           { name := s!"{X.name}:3", link := l, piece := 3,
             before := here.getD [] ++ prev.getD [],
             P := G.W.layers, hp := hp, g := X.g })]
       | none => []) ++ k4From Z G rest (l + 1) (some X.name)
    else k4From Z G rest (l + 1) last

/-- The parameters of K4's places, at the places whose Bool is true. A refused place is left out: a
caller that lays blocks from this list must refuse there itself. -/
def k4Pars (Z : Pub) (G : Ground) : List OnBytes.Desc.First.K4.Par :=
  ((k4From Z G G.built.toList 0 none).filter (·.1)).map (·.2)

/-- K4's block at a place, with its lists, at the type `Cl`. Where the place's Bool is false the
block's test on the plan is false: the plan is refused at that place. -/
def k4Block (x : Bool × OnBytes.Desc.First.K4.Par) : Block S Cl :=
  let b := OnBytes.Desc.First.K4.blockAtC { x.2 with k3Runs := true }
  { b with planOk := b.planOk && x.1 }

/-- K4's lot, from the public part. -/
def k4Lot (Z : Pub) : Lot :=
  { name := "K4"
    letters := false
    own := fun _ => []
    hearC := fun G => (k4From Z G G.built.toList 0 none).map k4Block
    controls := [] }

end ProofFile
