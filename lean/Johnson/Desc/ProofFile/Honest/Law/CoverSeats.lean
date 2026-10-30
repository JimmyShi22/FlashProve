-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSeats.lean: where the first chain's falls and marks may be:
two tests on a place. The chain's list of falls and the marks are gathered from the authors of
several sub-protocols. The lemmas on the number of falls (Honest/Law/CoverSparse.lean,
Honest/Law/CoverGroup.lean; neither is in the sealed library) take them as parameters and ask of
them only where they are. This file has the two tests (`fallSeat`, `markSeat`), and counts what they
select among the written places at the full size. A place at which a test returns true is called a
seat. A mark (`Mark`, Honest/Law/Marks.lean) is a test on the challenges alone, at one
sub-protocol's place, with a stated share, which is to bound the probability that it fires. It names
an event at which the verifier rejects nothing and the prover is not stopped, but which has to be
counted all the same: a fall after it can be bounded only where the mark has not fired.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What this is. Two definitions that fix two parameters; lemmas that unfold them; tests (`#guard`)
that count, each of which makes the file fail if its number is off. None of the library's goals.

  1  `fallSeat`, `markSeat`
  2  `fallSeat_out`, `fallSeat_frame`, `markSeat_frame`
  3  the counts at the full size (358 places): 62 seats of falls (12 of the kind K4, 25 batchings,
     25 sub-protocols after a batching); 101 seats of marks (50 of K3, 12 of K4, 12 of K5, 1 of K6,
     25 of K8, 1 of K11); 12 are both (the kind K4); 207 places are neither

Read from the library's `kindsBeforeBatching` and `linkPlaces` (Johnson/Desc/First/Driver/Chain.lean), a
segment's pieces are: 0, the kind frame; the hearing sub-protocols; the batching (K9); the kind
frame; the closing (K9, K10, K9); the kind frame. Which fall or mark is where is stated by its
author: nothing here compares what an author supplies with the tests.

Limits.
  * The counts in this file are evaluations (`#guard`), not theorems.
    Honest/Law/Rule/SeatsFacts.lean proves such counts (`seats_counts`, `seats_control`,
    `seat_front`).
  * This folder's own marks (for the fit and for the stops) are at other places too; they are
    treated in other files of this folder.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.P5J.LettersAt
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.LinkJoin (hearN)

/-! ## 1 The two tests -/

/-- **Where a fall of the first chain may be.** `links`: the types of the chain's segments. Only
inside a segment l, at a place of one of three forms (the library's `linkPlaces`,
Johnson/Desc/First/Driver/Chain.lean): a place of the kind K4 (a feed-forward segment's own rounds);
the batching (the kind K9 at the piece right after the hearing sub-protocols); the sub-protocol
without a round right after the batching (the kind frame, one piece on). -/
def fallSeat (links : List ModelPart) (p : Place) : Bool :=
  match p.link with
  | none => false
  | some l => p.kind == KindName.K4 ||
      (p.kind == KindName.K9 && p.piece == hearN links l + 1) ||
      (p.kind == KindName.frame && p.piece == hearN links l + 2)

/-- **Where a mark of the first chain that a sub-protocol's author supplies may be**: at a place of
one of six kinds: the lookups (K3), a feed-forward segment's own rounds (K4), an attention segment's
(K5), the head's (K6), the smallness test's draw (K8), the merge (K11). A place of the kind K4 is a
fall's seat too. -/
def markSeat (p : Place) : Bool :=
  [KindName.K3, KindName.K4, KindName.K5, KindName.K6, KindName.K8, KindName.K11].contains p.kind

/-! ## 2 Unfolded -/

/-- Outside the segments there is no seat of a fall. -/
theorem fallSeat_out (links : List ModelPart) {p : Place} (hp : p.link = none) :
    fallSeat links p = false := by
  unfold fallSeat
  rw [hp]

/-- A place of the kind frame inside a segment is a fall's seat exactly if it is the piece right
after the batching. -/
theorem fallSeat_frame (links : List ModelPart) {p : Place} {l : Nat} (hp : p.link = some l)
    (hk : p.kind = KindName.frame) :
    fallSeat links p = true ↔ p.piece = hearN links l + 2 := by
  unfold fallSeat
  rw [hp]
  simp [hk]

/-- No place of the kind frame is a mark's seat. -/
theorem markSeat_frame {p : Place} (hk : p.kind = KindName.frame) : markSeat p = false := by
  unfold markSeat
  rw [hk]
  rfl

/-! ## 3 The counts at the full size -/

#guard P5J.At.ps.length == 358
#guard (P5J.At.ps.filter (fallSeat P5J.At.links)).length == 62
#guard (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.K4).length == 12
#guard (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.K9).length == 25
#guard (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.frame).length == 25
#guard (P5J.At.ps.filter markSeat).length == 101
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K3).length == 50
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K4).length == 12
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K5).length == 12
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K6).length == 1
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K8).length == 25
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K11).length == 1
#guard (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && markSeat p).length == 12
#guard (P5J.At.ps.filter fun p => !fallSeat P5J.At.links p && !markSeat p).length == 207
-- a control: of the 75 places of the kind K9 the test takes the batchings alone
#guard (P5J.At.ps.filter fun p => p.kind == KindName.K9).length == 75
-- right before each seat of the kind frame there is a batching
#guard (P5J.At.ps.zip (P5J.At.ps.drop 1)).all fun x =>
  !(fallSeat P5J.At.links x.2 && x.2.kind == KindName.frame) ||
    (fallSeat P5J.At.links x.1 && x.1.kind == KindName.K9)

end ProofFile.Honest

#print axioms ProofFile.Honest.fallSeat_out
#print axioms ProofFile.Honest.fallSeat_frame
#print axioms ProofFile.Honest.markSeat_frame
