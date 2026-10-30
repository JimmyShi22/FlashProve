-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/BorneAt.lean: which oracle messages the part of the closing of a
segment (K10) carries at the proof file's description: the list of Honest/K10/Carried.lean with its
four parameters read off the public part. This file defines part of the honest prover. Definitions
with code, and tests at made-up data; no theorem.

  `partStarts`   the number of the first round of each part, of a place's cut
  `sendersIn`    the parts of a segment that hold a sending, in order: at each place of the segment,
                 each part, by the book's own cut of the place's rounds (`cutOfNames`,
                 Honest/BookOf.lean), whose first round is named "SEND seed". xs: the places with
                 their stretches of the declared rounds, as the lots read them (`k9Stretches`,
                 Johnson/Desc/ProofFile/Lot/K9.lean)
  `sendersFit`   a test: each segment has as many such parts as its shape has moments
  `borneAtOf`    the list at segment l, of a request's shape, the codes and such a list of places
  `borneAt`      the same off the public part: what `closeHalves`, `closings`, `seatClosings` and
                 `foldDueAll` take as `borne`
  `borneDue`     one test at a public part on what `borneAt` supposes

Limits. The sending of moment t is taken to be the segment's part number t among those that begin with "SEND seed":
right if a segment has no other sending; `sendersFit` counts them and asks no more. Beyond the list the address is a
default one, which no book made of a description knows; at a number that the codes lack the count is ⟨0, 0⟩; nothing
refuses at either. Two sources for one thing: `borneAt` counts an earlier closing's fresh mask at the k and h of the
groups that the first chain's shape gives (`reqGroups`), while the places' own k and h (`closePars`,
Honest/K10/AtLot.lean) are read off the frame in the state before the first segment. `borneAt` asks none of this:
`borneDue` asks all of it but that the link is below the number of segments, for whoever lists the halves. `borneAt` and
`borneDue` are tried by no line: they want a real public part. Honest/K10/Carried.lean's limits hold here too. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Carried
import Johnson.Desc.ProofFile.Honest.BookOf
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Codes reqMoments)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.First.Close (Par)

/-- The number of the first round of each part. -/
def partStarts (cut : List Nat) : List Nat :=
  (cut.foldl (fun (s : List Nat × Nat) n => (s.1 ++ [s.2], s.2 + n)) ([], 0)).1

/-- **The parts of segment j that hold a sending**, in order. -/
def sendersIn (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (j : Nat) : List Addr :=
  (xs.filter fun x => x.1.place.link == some j).flatMap fun x =>
    let names := x.2.1.map (·.entry.name)
    (partStarts (cutOfNames x.1.place.kind names)).zipIdx.filterMap fun y =>
      if names[y.1]? == some "SEND seed" then some ⟨x.1.place, y.2⟩ else none

/-- Each segment has as many such parts as its shape has moments. -/
def sendersFit (s : ReqShape) (xs : List (Spot × List Fmt.DeclaredRound × Nat)) : Bool :=
  s.link.zipIdx.all fun y => (sendersIn xs y.2).length == reqMoments y.1

/-- **What the part at segment l carries**, of the shape, the codes and the places. -/
def borneAtOf (s : ReqShape) (codes : Codes) (xs : List (Spot × List Fmt.DeclaredRound × Nat))
    (l : Nat) : List Borne :=
  borneOf s codes (fun j t => (sendersIn xs j).getD t default) l

/-- **The same off the public part.** -/
def borneAt (Z : Pub) (P : Par) : List Borne :=
  borneAtOf Z.first.shape Z.first.codes (k9Stretches Z) P.link

/-- **What `borneAt` supposes**: each segment has as many parts that hold a sending as its shape has
moments; the codes have the shape's two numbers; `msgDue` yields a count for every message that the
last segment's closing carries (so for every message of every segment but that closing's
own fresh mask); the groups that the shape gives have the k and h of the frame's groups in the
state before the first segment. -/
def borneDue (Z : Pub) : Bool :=
  sendersFit Z.first.shape (k9Stretches Z) &&
    (Z.first.codes.base[Z.first.shape.code]?).isSome &&
    (Z.first.codes.mask[Z.first.shape.maskCode]?).isSome &&
    borneKnown Z.first.shape Z.first.codes (Z.first.shape.link.length - 1) &&
    (OnBytes.reqGroups Z.first.shape).toList.map (fun G => (G.k, G.h)) ==
      Z.s₀.check.frame.groups.toList.map fun G => (G.k, G.h)

/-! ### Tests at made-up data -/

namespace Toy.Borne
open VerifiableInference.Desc (Place KindName)

def decl (n : String) : Fmt.DeclaredRound := { (default : Fmt.DeclaredRound) with entry := { name := n } }
def spot (link piece : Nat) (kind : KindName) (ns : List String) :
    Spot × List Fmt.DeclaredRound × Nat :=
  (⟨"", ⟨1, some link, piece, kind⟩, []⟩, ns.map decl, 0)

/-- Two segments, as Honest/K10/Carried.lean's made-up shape has them: the first with two moments,
the second with one, which a switch sends. Between the sendings stand places of other kinds. The
switch's place with a round "REPLY" in front is made up, to try a part other than number 0: in a
proof file's description that round has a place of its own, and every sender is its place's part 0.
-/
def xs : List (Spot × List Fmt.DeclaredRound × Nat) :=
  [spot 0 1 .K1 ["SEND seed", "SEND answer"], spot 0 2 .K4 ["PSC epsilon", "PSC round"],
   spot 0 3 .K1 ["SEND seed", "SEND answer"], spot 0 4 .K9 ["BAT-sigma"],
   spot 0 5 .K10 ["BAT", "FOLD epsilon", "FOLD round"],
   spot 1 1 .K2 ["REPLY", "SEND seed", "LOC"], spot 1 2 .K9 ["BAT-sigma"]]

def codes : Codes := Toy.Carried.codes

#guard partStarts [2, 1, 3] == [0, 2, 3]
#guard partStarts [] == []
-- the first segment's two sendings are part 0 of their places; the second's is part 1 of its place
#guard sendersIn xs 0 == [⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨⟨1, some 0, 3, .K1⟩, 0⟩]
#guard sendersIn xs 1 == [⟨⟨1, some 1, 1, .K2⟩, 1⟩]
#guard sendersIn xs 2 == []
#guard sendersFit Toy.Carried.shape xs
#guard !sendersFit Toy.Carried.shape (xs.drop 1)
-- the list at the first segment: its three messages, without its own fresh mask
#guard (borneAtOf Toy.Carried.shape codes xs 0).map (fun m => (m.sender.place.piece, m.msg)) ==
  [(1, 0), (1, 1), (3, 0)]
-- with the second sending's place taken away the message of moment 1 gets the default address
#guard ((borneAtOf Toy.Carried.shape codes (xs.take 2) 0).map (·.sender)).getLast? == some default
-- the list at the second segment: the counts are Honest/K10/Carried.lean's; the senders are these
#guard (borneAtOf Toy.Carried.shape codes xs 1).map (fun m => (m.sender.place.link,
    m.sender.place.piece, m.sender.part, m.msg, m.count)) ==
  [(some 0, 1, 0, 0, ⟨9, 11⟩), (some 0, 1, 0, 1, ⟨9, 0⟩), (some 0, 1, 0, 2, ⟨0, 10⟩),
   (some 0, 3, 0, 0, ⟨0, 4⟩), (some 1, 1, 1, 0, ⟨0, 7⟩), (some 1, 1, 1, 1, ⟨9, 0⟩),
   (some 1, 1, 1, 2, ⟨3, 11⟩)]

end Toy.Borne

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.partStarts
#print axioms ProofFile.Honest.K10.sendersIn
#print axioms ProofFile.Honest.K10.sendersFit
#print axioms ProofFile.Honest.K10.borneAtOf
#print axioms ProofFile.Honest.K10.borneAt
#print axioms ProofFile.Honest.K10.borneDue
#print axioms ProofFile.Honest.K10.Toy.Borne.decl
#print axioms ProofFile.Honest.K10.Toy.Borne.spot
#print axioms ProofFile.Honest.K10.Toy.Borne.xs
#print axioms ProofFile.Honest.K10.Toy.Borne.codes
