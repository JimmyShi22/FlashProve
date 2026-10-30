-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MakerStatement.lean: THE STATEMENTS, AND NO PROOF: "BEHIND A YES OF THE QUIET
STEP THAT OPENS A LINK
THE TESTS OF THE TWO PUBLIC ITEMS frame.sentIs AND ledger.treesAre SAY YES"
(Johnson/Desc/First/FillSent.lean). Definitions alone (`def … : Prop`), and one test with code.

THE STEP. A link's part of the carried record is laid by the second half of the link's first place:
`openLay`, `openAtt` (Johnson/Desc/First/Walk/Frame.lean) and, at link 0, `openLayZero`
(Johnson/Desc/First/Walk/FrameZero.lean). By their texts: the link's context is
{ check := the chain's own state of the calls, link := l, arrayOf, list := the plan's }, behind the
test "the chain's frame stands at link l" (`front`, Johnson/Desc/First/Walk/Quiet.lean); the ledger
is `startFork X ns` (Johnson/Desc/First/Walk/FirstQuiet.lean): the plan's planned ledger with every
virtual row's weights laid at 0 and ns free slots.

  `checkSentB d m c`: the four clauses of "frame.sentIs" that the step does not test itself, ON THE
    CHAIN's OWN STATE OF THE CALLS c in front of the step: next, the group's born, own, keptBefore.
  `OpenLayTrees`, `OpenLayZeroTrees`, `OpenAttTrees`: a yes of the step; the plan's looks at m are
    those of `startFork`'s arrays: then `treesAreB d m` says yes behind.
  `OpenLaySent`, `OpenLayZeroSent`, `OpenAttSent`: a yes of the step; `checkSentB` in front, at the
    step's own link's number: then `sentIsB` says yes behind, at that number.

OBJECT: the three steps' texts. USER: none yet; meant: the law of the block at a link's first place.
LETTERS: the steps' own (P, fvs, kCol), d, m.

Limits. SENTENCES: NOTHING IS PROVED HERE. HALF OF THE MAKER's DEBT: `checkSentB` IN FRONT OF THE
STEP IS A PREMISE: it stands between the two halves of one block: that the first half (the link's
first sending, or the switch) leaves it is not said here. THE HEAD's LINK IS OPENED BY ANOTHER TEXT:
not here. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness.

-/
import Johnson.Desc.First.Walk.FrameZero
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LayPar AttPar openLay openLayZero openAtt startFork)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillSent (SentData treeLook sentIsB treesAreB)

/-- The four clauses that the opening step does not test itself, on the chain's own state of the
calls. -/
def checkSentB (d : SentData) (m : Nat) (c : ChainCheck) : Bool :=
  decide (c.frame.next = .laterOrClose) && decide ((c.frame.groups.getD m {}).born = d.born m) &&
    decide (c.frame.own = d.own m) && decide (c.frame.keptBefore = d.kept m)

/-- A layers' link behind link 0: the ledger's arrays. -/
def OpenLayTrees : Prop :=
  ∀ (P : LayPar) (s s' : S) (d : SentData) (m : Nat), openLay P s = .ok s' →
    d.trees m = (startFork P.X P.ns).trees.toList.map treeLook → treesAreB d m s' = true

/-- Link 0: the ledger's arrays. -/
def OpenLayZeroTrees : Prop :=
  ∀ (P : LayPar) (fvs : List Bool) (kCol : Nat) (s s' : S) (d : SentData) (m : Nat),
    openLayZero P fvs kCol s = .ok s' →
    d.trees m = (startFork P.X P.ns).trees.toList.map treeLook → treesAreB d m s' = true

/-- An attention link: the ledger's arrays. -/
def OpenAttTrees : Prop :=
  ∀ (P : AttPar) (s s' : S) (d : SentData) (m : Nat), openAtt P s = .ok s' →
    d.trees m = (startFork P.X P.ns).trees.toList.map treeLook → treesAreB d m s' = true

/-- A layers' link behind link 0: the frame. -/
def OpenLaySent : Prop :=
  ∀ (P : LayPar) (s s' : S) (d : SentData), openLay P s = .ok s' →
    checkSentB d P.l s.check = true → sentIsB d P.l s' = true

/-- Link 0: the frame. -/
def OpenLayZeroSent : Prop :=
  ∀ (P : LayPar) (fvs : List Bool) (kCol : Nat) (s s' : S) (d : SentData),
    openLayZero P fvs kCol s = .ok s' → checkSentB d 0 s.check = true → sentIsB d 0 s' = true

/-- An attention link: the frame. -/
def OpenAttSent : Prop :=
  ∀ (P : AttPar) (s s' : S) (d : SentData), openAtt P s = .ok s' →
    checkSentB d P.l s.check = true → sentIsB d P.l s' = true

end OnBytes.Road.K4.Rec
