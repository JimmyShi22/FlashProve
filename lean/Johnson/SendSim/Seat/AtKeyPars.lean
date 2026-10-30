-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtKeyPars.lean: the public numbers, and which table is sent along, at the three
sub-protocols of the kind K1 in the first chain of a key file's description. The file holds
definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource, and a link is a lookup's. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  msgFold x     the first fold of the ranges' proximity test, whose fresh mask is sent along with
                the lookups' own message: its number in the sending and its shape, as Wf.messageOf
                (OnBytes/Iop/Wf.lean) writes them. It is none where masks are not sent along or the
                test has no stage.
  keyPars Xs    for a source Xs of a key file's description (Key.descriptionFromSource, Johnson/Desc/Key/Desc.lean):
                the public numbers and the tables sent along at the index-mask message's sending, at
                the lookups' own message's, and at the sending of the table W where the shape has
                such a message. The numbers are the library's K1.parIdx, K1.parMsg and K1.parWKey
                (Johnson/Desc/K1/Law/SitsKey.lean) at the arguments with which the description
                itself makes these three sub-protocols (two where the shape has no message for W;
                it has one wherever the description passes its tests on the plan: key_w_there,
                Johnson/SendSim/Seat/RideTies.lean).

How it fits. Johnson/SendSim/Seat/AtKeyStands.lean proves that the description has a member at each
of these places, and that every side that Side.seated returns there for the sender's row, at a job
with these public numbers, is Seated. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits.
msgFold is written after Wf.messageOf's text. msg_rideOwn (AtKeyStands.lean) proves that the message
at msgFold's number is announced as the fresh mask of msgFold's fold. The announcement holds the
mask's number of rows (2 ^ h), its code and its leaf class, but not the fold's k. That msgFold's k
is the one that messageOf uses is by inspection, not proved. Where no table is sent along, the lemma
holds trivially.
msgFold and wFold read the fold's k and h off the one-time chain's own values. The proximity tests
that later spend these masks take their stages from N (the ranges' test) and from Q (the own test in
the third chain). Nothing in this file asks that the two agree. The description's test on the file
(fileOk) asks it. For the ranges' test that is the clause "stages.rng" of fileClauses. For W it is
the clause "stages.own" together with the clause "chains 1 and 2 hold the same codes and the same
shape, by value" of shapeClauses (both in Johnson/Desc/Key/FileOk.lean). The agreement is derived
from these clauses in Johnson/SendSim/Seat/RideTies.lean (key_stages_tie, key_member_tie).
These three are not all sendings of new tables. By a count over the written lists of sendings in
Johnson/G/SendsLit.lean (by inspection, not proved), a key file's first chain has six sendings of
new tables at both the full-size and the small example: these three, and three inside the one
sub-protocol of the kind K12 (the ranges' proximity test). The whole key file has 19 at the
full-size example and 14 at the small one.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.Desc.K1.Law.SitsKey

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open VerifiableInference.Desc.Key (groupsTold rootsAt rootsBefore lastSendRound)

/-- The first fold of the ranges' proximity test, whose fresh mask is sent along with the lookups'
own message: its number in the sending and its shape, as Wf.messageOf writes them. It is none where
masks are not sent along or the test has no stage. -/
def msgFold (x : WfPublic) : Option (Nat × FoldShape) :=
  match x.stages.head? with
  | some t =>
    if x.choice.masksRide then
      some (1, { ioppFoldShape t {} with maskLeafClass := x.message.leafClass })
    else none
  | none => none

/-- The public numbers, and which table is sent along, at the three sub-protocols of the kind K1 in
a key file's first chain (two where the shape has no message for W): the description's own terms. -/
def keyPars (Xs : Key.Source) : List (K1.Par × (Nat → Option Ride)) :=
  let one := Xs.Y.k.oneTime
  let D := Xs.Y.D.1
  let told := Xs.Y.told.1
  [(K1.parIdx one (groupsTold told 0 (rootsAt D 0)), rideOf none),
   (K1.parMsg one (groupsTold told (rootsBefore D 2) (rootsAt D 2)),
     rideOf (msgFold one.ranges))] ++
    ((linMessageW one.lin).map fun msg =>
      (K1.parWKey one msg
          (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))),
        rideOf (wFold one.lin))).toList

end OnBytes.SendSim.Seat
