-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Heard.lean: the honest side of the sub-protocol "the output head's
own rounds": what the verifier's state holds as heard at the head, as far as later sub-protocols'
honest sides read it, made of the challenges heard, each found by its round's number. Definitions
with code, and tests; no theorem.

Why. Behind the sub-protocol's rounds the verifier's text lays what it has heard into its state
(`heardOf`, Johnson/Stored/HeadSeat.lean). The claim on the committed weights, which the head's
merge takes up, names four fields of it (`weightsClaim`, Johnson/Desc/First/Look/LookQuiet.lean):
the lookup's key points; the last sumcheck's challenges over the positions; its challenges over the
features; the token that is checked at each position. A part of the honest side is handed no state
of the verifier's: it is handed the list of all challenges in front of it, one entry a round of the
chain, also for a round in which nothing is drawn. So the last three are made here of that list,
the request and the next token. The first is the lookup's own matter (Honest/K3/Heard.lean).

  `headLogitsAt`   inside the sub-protocol, the number of the round of the last sumcheck's first
                   variable
  `headLogitsR`    that sumcheck's challenges, one for each variable, in the order of the rounds
  `headHeardOf`    the verifier program's structure of what was heard at the head, by the verifier's
                   own `heardOf`, on a hearing that is blank but for these challenges
  `headNoLookup`   a lookup's structure of what was heard, blank
  `headTHr`        the challenges over the positions: the first drawn at index 0
  `headRs`         the challenges over the features: THE LAST DRAWN AT INDEX 0
  `headWin`        for each position the token that is checked there; 0 where none is

Which rounds are read. The last sumcheck is the sub-protocol's part number 7. Its first round draws
an element that is no coordinate; the lt + lPd rounds behind it draw one challenge each: first the
lt variables of the position, then the lPd of the feature. With base := the number of the chain's
rounds in front of the sub-protocol these are the rounds base + headLogitsAt p + j, j < lt + lPd.
No other round is read. `headWin` reads no challenge.

Why by number. The sub-protocol's own parts find their challenges from the END of the list that they
are handed (Honest/K6/Ask.lean): that list ends right in front of the part. A later sub-protocol's
part is handed a longer list, which ends in front of itself: so here a round is found by its number,
from the chain's first round on.

No line of `heardOf` is written a second time: which stretch of the challenges belongs to the
positions, that the other is reversed, and which token is checked where, are that function's text.

Limits. A round that is not yet heard, or draws nothing, counts as 0; further elements of a round
are dropped: nothing refuses. That `base` is the number of the chain's rounds in front of the
sub-protocol is the caller's. In `headHeardOf` every field but `win`, `g1`, `Zl`, `tH.r`, `rs` and
the two constants `qN` and `qH`
is made of a blank hearing and means nothing. THAT THESE VALUES ARE THOSE OF THE VERIFIER'S STATE
BEHIND A SESSION'S ROUNDS IS NOT SHOWN HERE: Honest/K6/HeardTie.lean (`logits_tie`) and
Honest/K6/HeardAtYes.lean (`logits_at_yes`) state it, CONDITIONALLY and field by field: where the
hearing returns from a well laid ledger; at the state behind an accepting step of the member from
such a ledger. (Beside these the first asks that the lookup's point on the positions has lt
coordinates, the second the member's form and two premises on its address and its guard.)
Honest/K6/HeardGuards.lean holds the rounds'
numbers against the sub-protocol's own list of rounds at three sizes. Honest/K6/HeardToy.lean
tries the tie to the state at one small size, behind the two sub-protocols' own steps. The
request and the next token are arguments here: `headHeardFor` (Honest/K6/HeardAt.lean) makes them
of the instance as the verifier's text reads them. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Ask
import Johnson.Stored.HeadSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Request)

/-- Inside the sub-protocol: the number of the round of the last sumcheck's first variable: behind
all rounds of the seven parts in front and that sumcheck's own first round. -/
def headLogitsAt (p : Head.Par) : Nat := headInFront p 7 + 1

/-- **The last sumcheck's challenges**, one for each variable, in the order of the rounds. base: how
many rounds of the chain stand in front of the sub-protocol. heard: the chain's challenges from its
first round on. -/
def headLogitsR (p : Head.Par) (base : Nat) (heard : List Fmt.Drawn) : Point :=
  ((List.range (headLt p + headLPd p)).map fun j =>
    elemOf heard (base + headLogitsAt p + j)).toArray

/-- **What was heard at the head, as the verifier's text lays it into its state**: its own function,
on a hearing in which all but the last sumcheck's challenges is blank. g1: what the lookup on the
head's calls left; it is handed through. -/
def headHeardOf (p : Head.Par) (request : Head.Request) (y : Nat) (g1 : OnBytes.Model.Forest.Heard)
    (base : Nat) (heard : List Fmt.Drawn) : OnBytes.Model.Head.Heard :=
  let _ := p.sizes
  let _ := request
  let _ : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  VerifiableInference.Desc.Kinds.Head.heardOf g1
    ({ pV := #[], W := #[], gam := zeroE, rhoI := #[], squares := {}, P := #[], om := zeroE,
       products := {} }, { normed := {} }, { logits := { r := headLogitsR p base heard } })

/-- A lookup's structure of what was heard, blank. -/
def headNoLookup : OnBytes.Model.Forest.Heard := { shape := {}, leaves := {} }

/-- **The challenges over the positions**: the first drawn at index 0. -/
def headTHr (p : Head.Par) (base : Nat) (heard : List Fmt.Drawn) : Point :=
  (headHeardOf p ⟨fun _ => 0, 0, 0⟩ 0 headNoLookup base heard).tH.r

/-- **The challenges over the features**: the last drawn at index 0: entry v belongs to bit v of a
feature's number. -/
def headRs (p : Head.Par) (base : Nat) (heard : List Fmt.Drawn) : Point :=
  (headHeardOf p ⟨fun _ => 0, 0, 0⟩ 0 headNoLookup base heard).rs

/-- **The token that is checked at each position**; 0 where none is. y: the next token. -/
def headWin (p : Head.Par) (request : Head.Request) (y : Nat) : Array Nat :=
  (headHeardOf p request y headNoLookup 0 []).win

/-! ## Tests at small made-up numbers

Four positions (lt = 2), six features (lPd = 3). In front of the last sumcheck's first variable
stand 1 + 1 + 8 + 1 + 1 + 5 + 5 rounds and one more: 23. -/

/-- The made-up public numbers. -/
def headHeardToyPar : Head.Par :=
  { sizes := { lt := 2, ls := 1, d := 6, MF := 0, KF := 0, epsF := 0, V := 5, sh := 7, F := 24 }
    policy := ⟨0, 0, 0⟩, sT := 0, floor := 0, work := 0, before := [] }

/-- A number as an element. -/
def headHeardToyE (n : Nat) : E := E.ofTriple (n.toUInt64, 0, 0)

/-- A list of challenges: round number i draws the elements i + 100 and 7. -/
def headHeardToyList (rounds : Nat) : List Fmt.Drawn :=
  (List.range rounds).map fun i => ⟨[((i + 100).toUInt64, 0, 0), (7, 0, 0)], [], [], none⟩

#guard headLogitsAt headHeardToyPar == 23
-- five rounds in front of the sub-protocol: the rounds 28 to 32
#guard headLogitsR headHeardToyPar 5 (headHeardToyList 40) ==
  #[128, 129, 130, 131, 132].map headHeardToyE
#guard headTHr headHeardToyPar 5 (headHeardToyList 40) == #[128, 129].map headHeardToyE
#guard headRs headHeardToyPar 5 (headHeardToyList 40) == #[132, 131, 130].map headHeardToyE
-- it moves with the number of rounds in front
#guard headTHr headHeardToyPar 6 (headHeardToyList 40) == #[129, 130].map headHeardToyE
-- rounds that are not yet heard count as 0
#guard headRs headHeardToyPar 5 (headHeardToyList 31) == #[0, 0, 130].map headHeardToyE
-- tokens 40, 41, 42, 43; the positions 1 to 3 are checked; the next token is 3: position t is about
-- token t + 1, the last position about the next token
#guard headWin headHeardToyPar ⟨fun i => i + 40, 1, 4⟩ 3 == #[0, 42, 43, 3]
-- the last position is not checked: the next token is not read
#guard headWin headHeardToyPar ⟨fun i => i + 40, 0, 3⟩ 3 == #[41, 42, 43, 0]
-- NEAR IDLE: what the lookup left is handed through
#guard (headHeardOf headHeardToyPar ⟨fun _ => 0, 0, 0⟩ 0
  { headNoLookup with zx := #[headHeardToyE 9] } 0 []).g1.zx == #[headHeardToyE 9]

end ProofFile.Honest.K6
