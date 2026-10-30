-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Look.lean: what the lookup in front of the layers' own rounds (K4)
has sampled, as the verifier program's structure has it, made of the challenges heard. It fills the
parameter `look` that Honest/K4/Part.lean leaves open. Definitions with code. No theorem.

NOT SHOWN HERE. No theorem says that this structure's fields are those of the verifier's hearing of
the same rounds. THE POINTS ARE MADE BY ANOTHER FILE, Honest/K3/Heard.lean, AND ITS LIMITS ARE THIS
FILE's: that its points are the hearing's is shown there by no theorem; at a lookup with one part of
keys, where the hearing returns, `pointsAgree_of_hearV` (Honest/K3/HeardLaw.lean) has six equations
on the fields that the hearing hands back, and of the points between the levels nothing; beyond that
it is only held by tests at synthetic lookups; that `base` is the number of rounds in front of the
lookup is the caller's to see to. Of the other fields e is made by the verifier's own public
function as `toHeard` calls it (Johnson/Desc/First/Look/K3LookupGeneral.lean); a by the function that the
hearing itself calls: `toHeard` copies what the hearing has. THE VERIFIER's FUNCTIONS YIELD OPTIONS,
THESE ARE TOTAL: where the hearing or `toHeard` yields nothing, these definitions still yield a
structure. Tests beside this file (Honest/K4/LookToy.lean (no part of the library yet)) hold the
fields that are laid, but shape, against the structure that `toHeard` makes of the verifier's
hearing, at synthetic rounds.

WHICH FIELDS ARE LAID. shape, theta, alpha, a, zx, zy, e, zb0, zb1, zk: public numbers and sampled
values, and what follows from these alone. K4's parts read three of them: zx, zk and e. Whoever
makes the reads' tables on the lookup's planes also reads shape, zb0 and zb1. WHICH ARE NOT.
tT, the calls' tables at the leaves' point: it follows from sampled values too, but costs a pass
over every call's table, the structure is made anew at every move of every part, and nothing of K4's
reads it: `k4LookTables` lays it for whoever wants it. leavesA follows from sampled values alone
too, and NEITHER DEFINITION LAYS IT: it stays 0. rows, leaves, sBit, cEnd and the three numbers of
owed claims belong to the verifier's ledger and claims: leaves, which has no default, is laid empty;
the others keep their defaults.

  `k4LookOf`       THE STRUCTURE, made from: the lookup's shape, the number of rounds in front of
                   it, the challenges
  `k4LookTables`   the same with tT
  `k4LookRounds`, `k4LookAt`   the lookup's number of rounds; the structure at one of K4's places

Limits. A round that is not yet heard counts as zeros (Honest/K3/Heard.lean): nothing returns an
error. `k4LookAt` STANDS ON TWO HYPOTHESES. One: the lookup's rounds are the last ones in front of
K4's first: so the format's table of a feed-forward segment has them
(docs/format/11-2-feed-forward-segment.md, steps 1 and 2); nothing here holds that against a
description, and at the small plan's own place (Johnson/Desc/K4/Honest/ToyPlan.lean: six rounds in
front) it is false. Two: the layout's Q.P.y.fo IS the shape at which the lookup is heard: the
verifier makes that shape anew and holds seven of its numbers against the layout's (`shapeFits`,
OnBytes/Desc/First/K4/Hear.lean), not its calls, their number, or the number of bits of a call's
number, all of which `k4LookAt` reads; by reading, the two are one at a layout that `layout` has
made.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.K4.Honest.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (Forest.Shape Forest.Heard Forest.callWeight Forest.tableAt)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc.K3 (faceOf)

/-- **What the lookup of shape h has sampled.** base: how many rounds of the chain stand in front of
the lookup. heard: the chain's challenges from its first round on. -/
def k4LookOf (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) : Forest.Heard :=
  let f := faceOf h
  let q := K3.ptsOf f base heard
  let k := K3.keyPtsOf h (q.keyPt 0 h.v)
  { shape := h, theta := q.theta, alpha := q.alpha, a := f.factor q.theta q.alpha, leaves := {}
    zx := k.zx, zy := k.zy, e := (Array.range h.NC).map (Forest.callWeight h k.zy)
    zb0 := K3.leavesR f base heard, zb1 := K3.bitsR f base heard, zk := k.zk }

/-- The same with the calls' tables at the leaves' point, as `toHeard` lays them. -/
def k4LookTables (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) : Forest.Heard :=
  let H := k4LookOf h base heard
  { H with tT := h.calls.map fun c => Forest.tableAt c (H.zb0.extract (h.kT - c.k) h.kT) }

/-- How many rounds the lookup of shape h has. -/
def k4LookRounds (h : Forest.Shape) : Nat :=
  ((K3.stages (faceOf h)).map (K3.Stage.rounds (faceOf h))).sum

/-- **The structure at one of K4's places.** TWO HYPOTHESES (see the head): the lookup's rounds are
the last ones in front of K4's first round, so that the lookup begins `k4LookRounds` rounds in front
of it; and the layout's shape of the lookup is the one at which it is heard. Where fewer rounds
stand in front of K4 the subtraction stops at 0. -/
def k4LookAt (Q : K4Pub) (heard : List Fmt.Drawn) : Forest.Heard :=
  k4LookOf Q.P.y.fo (Q.r0 - k4LookRounds Q.P.y.fo) heard

end ProofFile.Honest.K4
