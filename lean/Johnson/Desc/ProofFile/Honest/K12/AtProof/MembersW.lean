-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/MembersW.lean

What it holds. Who sent the oracle messages of the group that the request's own proximity test tests
(the place W: the last chain's test), and who sent its first fold's fresh table: the fields members
and fresh of a job (TestJob, Test.lean in the folder above) at that place; and the bare job there.
Definitions with code; no theorem. It goes on where Members.lean in this folder ends.

Names.
  senderI, senderW   the addresses of the two senders in the first chain: the first segment's
      opening; W's sending ("M:4").
  msgK1              one message of a sending of the kind K1, with its count by the kind's own
      reckoning.
  parI, parWAt       the two sendings' parameters.
  membersW, freshW   the group, in the order of the book's maker; the fresh table.
  bareW              the bare job (Doors.lean) at the place.

Whose hand. No count is typed here, and none is read off the book of random values or off the list
of sendings of which the book is made (Johnson.G.sendsOf). The index-mask message's and W's counts
are the kind K1's own (K1.dueMsg, Honest/K1/Coins.lean), at the parameters of which the sender's own
job (K1.firstJob, Honest/K1/PlaceFirst.lean) and the description's own block (K13.wBlock,
Johnson/Desc/ProofFile/Lot/K13At4.lean) are made; Omega's is its sender's (msgOf, Members.lean). So
a test that holds a job with these members against the book holds the senders' reckoning against the
book's.

Limits.
- Which messages make the group, and their order, are written here: read off the text of the book's
  maker (bookRaw, Honest/BookWhole.lean) and off one print at the small example.
- The maker picks by a property, this file by a position, three times: the maker takes every message
  of the first chain's sendings with mask rows alone and a sample (SentMsg.masks), this file the
  last message of the first sending; the maker takes W's sending's messages that are no fold's fresh
  table and the one that is (SentMsg.fresh), this file all but the last and the last; the maker
  takes Omega's sending's messages that are not of the kind masks, this file its message 0. Where
  the two part, the frame's laying refuses: nothing here shows that they agree.
- parI reads the ground's copy of the first chain's parameters, parWAt the public part's, each as
  its own house calls it: that the two are one is said by nobody here.
- All three senders stand in other chains than the test. At W's sender's address no filling of today
  is known to this file's writer to hold a half.
- A bare half is a stand-in of public numbers for a test of the laying: it is no honest prover's
  side, and it is not to be laid into a filling that is played or counted (Bare.lean's head).
- Nothing holds the group against the verifier's record of the groups. Nothing on completeness, on
  soundness or on what is hidden.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Members
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Doors
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst
import Johnson.Desc.ProofFile.Lot.K13At4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- The part that sends the first segment's opening; the index-mask message is its sending's last.
-/
def senderI : Addr := K1.firstAddr

/-- The address at which W and what is sent with it are sent: the first chain's "M:4". No filling of
today is known to this file's writer to hold a half there. -/
def senderW : Addr := ⟨⟨1, none, 4, .K1⟩, 0⟩

/-- **One message of a sending of the kind K1**: the sender's address, the message's number, and its
count of random values by the kind's own reckoning (K1.dueMsg, Honest/K1/Coins.lean) at the place's
parameters. ride: which message's table is a fold's fresh table. -/
def msgK1 (a : Addr) (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (k : Nat) :
    Addr × Nat × Due :=
  (a, k, K1.dueMsg P.codes (Johnson.Prover.Send.shapeAt P k) (ride k))

/-- The parameters of the first segment's opening, by the calls by which that part's own job makes
them (K1.firstJob, Honest/K1/PlaceFirst.lean). -/
def parI (Z : Pub) (G : Ground) : VerifiableInference.Desc.K1.Par :=
  VerifiableInference.Desc.K1.firstPar G.first (VerifiableInference.Desc.K1.gpOf Z)

/-- The parameters of W's sending, by the calls by which the description's own block is made
(K13.wBlock, Johnson/Desc/ProofFile/Lot/K13At4.lean). Nothing where the shape has no such message.
-/
def parWAt (Z : Pub) : Option VerifiableInference.Desc.K1.Par :=
  (OnBytes.linMessageW Z.first.lin).map fun msg =>
    VerifiableInference.Desc.K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree }
      4 msg

/-- **The group of the request's own test (the place W), in the order of the book's maker**: the
index-mask message; W's sending's messages but its last, which is the first fold's fresh table;
Omega. -/
def membersW (Z : Pub) (G : Ground) : Option (List (Addr × Nat × Due)) :=
  (parWAt Z).bind fun P => (sendPub Z).map fun A =>
    msgK1 senderI (parI Z G) (K1.firstRide G.first) ((parI Z G).sent.size - 1) ::
      ((List.range (P.sent.size - 1)).map fun k => msgK1 senderW P (fun _ => none) k) ++
      [msgOf senderO (K14.jobOmega A) 0]

/-- The first fresh table of the request's own test is the last message of W's sending. -/
def freshW (Z : Pub) : Option (Addr × Nat) := (parWAt Z).map fun P => (senderW, P.sent.size - 1)

/-- **The bare job at W.** -/
def bareW {W X : Type} (Z : Pub) (G : Ground) : Option (TestJob W X) :=
  (four Z).bind fun F => (membersW Z G).map fun ms => bareJob F.W ms (freshW Z)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.senderI
#print axioms ProofFile.Honest.K12.AtProof.senderW
#print axioms ProofFile.Honest.K12.AtProof.msgK1
#print axioms ProofFile.Honest.K12.AtProof.parI
#print axioms ProofFile.Honest.K12.AtProof.parWAt
#print axioms ProofFile.Honest.K12.AtProof.membersW
#print axioms ProofFile.Honest.K12.AtProof.freshW
#print axioms ProofFile.Honest.K12.AtProof.bareW
