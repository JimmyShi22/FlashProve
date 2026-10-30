-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Front.lean: what is asked of the carried record at the front of a proximity test.

This file holds definitions only; no theorem is stated.

frontL is a list of named clauses, so that a refusal bears its clause's name. It is written after
the test TestIn.sched on the schedule as it lies (a form of it: Johnson/Desc/Shared/Dec.lean),
clause for clause. Every clause reads numbers, shapes, flags and counters of the record that the
verifier's own earlier steps have made; none reads a value that a prover sends. It reads: the
statement; the book of trees; the number of the group under test; the number of the message that
holds the first fold's mask, if one is handed in.
A clause on a thing that is not there counts as held (on, Johnson/Desc/First/Base/Ground.lean): the
clause "… is there" fails then. The mask's message may lawfully be missing: no mask is handed in
where the first fold sends its own. The clauses on it hold then.
The public places of a member's pad are made by padMade (Johnson/Desc/Own/Send.lean): the program's
maker Send.pad taken over under a name as a part of the description.
frontE asks frontL and then openClaimsE (Johnson/Desc/Ground/Ask.lean).

What is not claimed. That the list is TestIn.sched: no theorem ties the two. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.Ground.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open OnBytes OnBytes.Params VerifiableInference.Desc.Ground

/-- ASKS, at the front of the test on the group g. -/
def frontL (S : Statement) (B : TreeBook) (g : Nat) (mask : Option Nat) : Clauses :=
  let G := S.groups[g]?
  let each (f : Nat → Oracle → Bool) : Bool :=
    on G fun G => G.members.all fun o => on S.oracles[o]? (f o)
  let m := mask.bind fun m => S.oracles[m]?
  [("front: the group is there", G.isSome),
   ("front: no test of it has begun", on G (!·.inRun)),
   ("front: a member", on G (!·.members.isEmpty)),
   ("front: as many kept marks as members", on G fun G => G.kept.size == G.members.size),
   ("front: the members rise", on G fun G => (List.range (G.members.size - 1)).all fun i =>
     decide (G.members.getD i 0 < G.members.getD (i + 1) 0)),
   ("front: every member is there", on G fun G => G.members.all fun o => (S.oracles[o]?).isSome),
   ("front: every member is sampled", each fun _ y => y.sampled),
   ("front: every member knows the group", each fun _ y => y.groups.contains g),
   ("front: as many sample rows as answers", each fun _ y => y.sampleRows.size == y.shape.answers),
   ("front: every member's pad is the public one", each fun _ y =>
     match Own.padMade S.codes y.shape with
     | none => false
     | some l => y.pad == l.map fun p => (p.part, p.index)),
   ("front: no open claim is a sample row", on G fun G => G.rows.all fun r => r.kind != .sample),
   ("front: the mask's message is there", mask.isNone || m.isSome),
   ("front: the mask's message is not sampled", on m (!·.sampled)),
   ("front: the mask's message counts no answer", on m (·.shape.answers == 0)),
   ("front: the mask's message is not spent", on m (!·.spentAsMask)),
   ("front: the mask's message is no member",
     on G fun G => on mask fun m => !G.members.contains m),
   ("front: statement and book are in step", S.oracles.size == B.place.size),
   ("front: each tree is in the book", on G fun G => (G.members.toList ++ mask.toList).all fun o =>
     ((B.place[o]?).bind fun p => B.trees[p.1]?).isSome),
   ("front: a tree that is opened at one list only has not been opened", on G fun G =>
     (G.members.toList ++ mask.toList).all fun o =>
       on ((B.place[o]?).bind fun p => B.trees[p.1]?) fun t => !t.oneList || t.lists == 0)]

/-- **The front of a proximity test**: the schedule as it lies; then every open claim. -/
def frontE (S : Statement) (B : TreeBook) (g : Nat) (mask : Option Nat) : Except String Unit := do
  refuse (frontL S B g mask)
  openClaimsE S g

end VerifiableInference.Desc.K12
