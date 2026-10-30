-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Ask.lean: the honest side of the sub-protocol "the output head's
own rounds" (Johnson/Desc/Kinds/Head.lean): what its parts are handed, and how they find their
letters among the challenges heard. Definitions with code; no theorem.

  `HeadAsk`       the small input at which all parts of the sub-protocol are typed: what they need
                  of the prover's input
  `headCut`       how many rounds each of the eight parts has
  `headInFront`   how many of the sub-protocol's rounds stand in front of a part
  `headOwn`, `headFront`   the challenges heard, cut in two: those of the sub-protocol's own rounds
                  in front of a part, and all that were heard before the sub-protocol began
  `elemsOf`, `elemOf`   a challenge's drawn elements
  `headPV`, `headGam`, `headOm`   the three letters that the sub-protocol's own rounds draw and
                  later parts read: the point on the positions and the two batching elements
  `HeadAsk.given` the letters that the verifier's text reads in classes, made as its own `given`
                  makes them (Johnson/Desc/Kinds/HeadFrame.lean), without that function's tests

How a part finds a challenge. A part's functions are handed all challenges heard in front of the
part. The number of the sub-protocol's own rounds in front of the part is public, so its own
challenges are counted from the end of that list, and what is left in front is what was heard before
the sub-protocol began.

What comes in from the lookup. The verifier's text takes two things off its state: the lookup's
point and each call's key point. Both are made of challenges that were drawn in the lookup's rounds.
Here they are a field of the small input: a function of the challenges heard before the
sub-protocol began. Nothing here says which challenges they are.

Limits. Nothing holds `lookup` against the lookup's own text, `cells` against a model's forward
pass, or `request` and `y` against an instance. Where one element of a challenge is read and the
challenge has none, it counts as 0. Where the point on the positions is read, a challenge with fewer
elements gives a shorter point; so does a `lookup` whose point has fewer coordinates than there are
bits of a position: the sums that are made at such a point have fewer variables than the shape of
their sumcheck, and nothing here refuses. Where fewer challenges were heard than the sub-protocol
has rounds in front of the part, all count as the sub-protocol's own and none as heard before it.
The clauses on challenges are not met where the rounds are played in order at the verifier's own
counts; the clause on `lookup` hangs on what is laid there. `HeadAsk.given` is held against the
verifier's own `given` by no line but those of Honest/K6/Toy.lean, where both are at work.
Nothing on any property.

-/
import Johnson.Desc.Kinds.HeadFrame
import Johnson.Desc.Kinds.HeadNormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Request Head.Given Head.Law.NCells)

/-- **What the parts of the output head's own rounds need of the prover's input.** -/
structure HeadAsk where
  /-- the request as far as it is public: its tokens and the two positions between which it is
  checked -/
  request : Head.Request
  /-- the next token -/
  y : Nat
  /-- the committed cells that the rounds read, as integers, and the head's weights -/
  cells : Head.Law.NCells
  /-- of the challenges heard before the sub-protocol began: the lookup's point, and for each call
  of the lookup its key point -/
  lookup : List Fmt.Drawn → Point × (Nat → Point)

/-- The logarithm of the number of positions. -/
def headLt (p : Head.Par) : Nat := p.sizes.lt

/-- The logarithm of the number of features, with padding. -/
def headLPd (p : Head.Par) : Nat :=
  let _ := p.sizes
  VerifiableInference.Desc.Kinds.Norm.lPd

/-- **The cut**: how many rounds each of the eight parts has: the point on the positions · nine
hidden scalars · the sumcheck on the squares · the round that ends it · seven hidden scalars · the
sumcheck on the products · the one on the stream times the reciprocal · the head's own. -/
def headCut (p : Head.Par) : List Nat :=
  [1, 1, headLPd p + headLt p + 3, 1, 1, headLt p + 3, headLt p + 3, headLt p + headLPd p + 3]

/-- How many of the sub-protocol's rounds stand in front of its part number i. -/
def headInFront (p : Head.Par) (i : Nat) : Nat := ((headCut p).take i).foldl (· + ·) 0

/-- Of the challenges heard in front of part number i: those of the sub-protocol's own rounds. -/
def headOwn (p : Head.Par) (i : Nat) (heard : List Fmt.Drawn) : List Fmt.Drawn :=
  heard.drop (heard.length - headInFront p i)

/-- Of the same: those heard before the sub-protocol began. -/
def headFront (p : Head.Par) (i : Nat) (heard : List Fmt.Drawn) : List Fmt.Drawn :=
  heard.take (heard.length - headInFront p i)

/-- All elements that a challenge drew. -/
def elemsOf (d : Fmt.Drawn) : List E := d.elems.map E.ofTriple

/-- The first element that challenge number n of a list drew; 0 where there is none. -/
def elemOf (ds : List Fmt.Drawn) (n : Nat) : E :=
  ((ds[n]?).bind fun d => (elemsOf d).head?).getD zeroE

/-- The point on the positions: what the sub-protocol's first round drew. own: the sub-protocol's
own challenges so far. -/
def headPV (own : List Fmt.Drawn) : Point := ((own.head?.map elemsOf).getD []).toArray

/-- The element that batches the nine sums of limb products: the second round's. -/
def headGam (own : List Fmt.Drawn) : E := elemOf own 1

/-- The element that batches the seven products: the round's in which they are sent. -/
def headOm (p : Head.Par) (own : List Fmt.Drawn) : E := elemOf own (headInFront p 4)

/-- **The letters in front of the hearing**, as the verifier's own `given` makes them of its state:
here of the small input and the challenges heard before the sub-protocol began. -/
@[reducible] def HeadAsk.given (a : HeadAsk) (p : Head.Par) (front : List Fmt.Drawn) : Head.Given :=
  let _ := p.sizes
  let z := a.lookup front
  let i := VerifiableInference.Desc.Kinds.Head.fromLookup p.floor z.1 z.2
  { sizes := p.sizes, policy := p.policy, request := a.request, token := ⟨a.y⟩
    normIn := i.norm, headIn := i.head, calls := i.calls }

end ProofFile.Honest.K6
