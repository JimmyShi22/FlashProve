-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/SentAtMoment.lean: THE OPEN SEGMENT's FRAME's TWO LISTS OF MESSAGES' NUMBERS, AS
TERMS WITH CODE OFF THE PUBLIC PARAMETERS, MOMENT BY MOMENT: what fills the letters ownAt and keptAt
of the structure of facts along the verifier's run (Johnson/Desc/First/FoldFacts.lean, the field
frameIs). Small; no Mathlib. A file BESIDE Johnson/Desc/First/SentTerms.lean and
Johnson/Desc/First/FillSentLater.lean: it turns nothing of them.

  `thirdNos shape base2 m`: the numbers of the third sending's messages: base2 m, base2 m + 1, …, as
    many as the segment has messages of moment 2. base2 m: how many oracle messages are sent in
    front of that sending. The rule of secondNos (FillSentLater.lean), one moment on.
  `base2At N links ps m`: the table of joints' own number N.msgsAt at the place of that sending:
    piece 6 + o of the segment; o: the shift of the segment's sort.
  `ownAt shape N links ps built m j`: the list own of the open segment's frame where the frame's
    field moment is j: at j ≤ 1 the first sending's numbers; at 2 these and the second sending's;
    from 3 on these and the third's.
  `keptAt shape N links ps built m`: the list keptBefore: at every moment the same.
  `ownAt_one`, `ownAt_two`, `ownAt_three`, `keptAt_is`: what these are in the two elder files' terms
    (by the definition).
BY A READING of ReqFrame.beginLink (moment := 1, own := #[]), ReqFrame.later (it sends the messages
whose moment is the frame's field moment, appends their numbers to own and raises the field by 1)
and ReqFrame.joinOwn (OnBytes/Iop/Req.lean).

Limits. NOTHING IS PROVED HERE OF ANY STATE OF THE VERIFIER. That a sending's numbers run on from
the number of messages sent in front of it is read, not shown. WHAT HAS RUN: THE VERIFIER's OWN
LISTS, printed along one honest walk at the small size (and, with the same keys, at the full size):
own behind the first, the second and the third sending: at the layers' segment 0: 0, 1, 2 · 0, 1, 2,
5 · 0, 1, 2, 5, 6; at the attention's segment 1: 10 · 10, 12 · 10, 12, 13; at the layers' segment 2:
16, 17, 18 · 16, 17, 18, 20 · 16, 17, 18, 20, 21; at the output head's: 31 · 31, 33 · 31, 33, 34;
keptBefore does not turn inside a segment; each later sending appended one number, the statement's
count of oracle messages in front of it: AS THE RULE HERE SAYS. ownAt ITSELF HAS BEEN EVALUATED
NOWHERE (sentDataAt's own at segment 0 once, at letters picked by hand: 0, 1, 2); the frame's field
moment and N.msgsAt were not printed. A segment with more than three moments is not treated: from 3
on the list stays. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on
soundness.


-/
import Johnson.Desc.First.FillSentLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillSent
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)

/-- The numbers of the third sending's messages. base2 m: how many oracle messages are sent in front
of it. BY A READING. -/
def thirdNos (shape : Params.ReqShape) (base2 : Nat → Nat) (m : Nat) : Array Nat :=
  (Array.range (((shape.link[m]?.map (·.messages)).getD []).filter fun x =>
    x.moment == 2).length).map (· + base2 m)

/-- How many oracle messages are sent in front of segment m's third sending. -/
def base2At (N : Numbers) (links : List ModelPart) (ps : List Place) (m : Nat) : Nat :=
  N.msgsAt (ps.find? fun p => p.link == some m && p.piece == 6 + ((links[m]?).map shift).getD 0)

section
variable (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
  (built : Array Stages.LinkH)

/-- **The frame's list own, where the frame's field moment is j.** -/
def ownAt (m j : Nat) : Array Nat :=
  if j ≤ 1 then (sentDataAt shape N links ps built).own m
  else if j = 2 then (sentData1At shape N links ps built).own m
  else (sentData1At shape N links ps built).own m ++ thirdNos shape (base2At N links ps) m

/-- **The frame's list keptBefore.** -/
def keptAt (m : Nat) : Array Nat := (sentDataAt shape N links ps built).kept m

theorem ownAt_one (m : Nat) :
    ownAt shape N links ps built m 1 = (sentDataAt shape N links ps built).own m := rfl

theorem ownAt_two (m : Nat) :
    ownAt shape N links ps built m 2 = (sentData1At shape N links ps built).own m := rfl

theorem ownAt_three (m : Nat) :
    ownAt shape N links ps built m 3 =
      (sentData1At shape N links ps built).own m ++ thirdNos shape (base2At N links ps) m := rfl

theorem keptAt_is (m : Nat) :
    keptAt shape N links ps built m = (sentData1At shape N links ps built).kept m := rfl

end

end VerifiableInference.Desc.First.FillSent

#print axioms VerifiableInference.Desc.First.FillSent.ownAt_one
#print axioms VerifiableInference.Desc.First.FillSent.ownAt_two
#print axioms VerifiableInference.Desc.First.FillSent.ownAt_three
#print axioms VerifiableInference.Desc.First.FillSent.keptAt_is
