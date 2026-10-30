-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/Members.lean: who sent the oracle messages of the groups
that the shared chain's two proximity tests test, and who sent the first fold's fresh table: the
fields `members` and `fresh` of a job (`TestJob`, Johnson/Desc/ProofFile/Honest/K12/Test.lean) at
the test on the folded row's group (U) and at the test on Omega's group (O). Definitions with code;
no theorem. The two lists are defined at every value A of the two sendings' public data
(`K14.SendPub`), and `sendPub` at every public part Z (`Pub`, Johnson/Desc/ProofFile/Pub.lean).

In the list: a job is what a caller supplies for its test. The docstrings call the folded row's
group G_u and Omega's group G_omega. A sending is a part of the prover (`Part`, in the frame,
Johnson/Desc/ProofFile/Honest/Frame.lean) that sends oracle messages, numbered from 0 in the order
of sending; its data are a `K14.SendJob` (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean). The
shared chain has two: "send o_u" (`K14.jobU A`) and "send o_omega" (`K14.jobOmega A`). An address
(`Addr`, the frame) is a place of the description and the number of a prover's part there. A count
of coins (`Due`, the frame) is f elements of the base field and e of the extension field.

  `membersU`, `freshU`: o_u, then the split's mask message o_sp; the fresh table is message 1 of
    "send o_u". By the definitions: `membersU A` is message 0 of "send o_u", then message 1 of
    "send o_omega"; `freshU` is `some (senderU, 1)`
  `membersO`, `freshO`: o_omega, then o_sp; the fold sends its own fresh table. By the
    definitions: `membersO A` is messages 0 and 1 of "send o_omega"; `freshO` is `none`
  `msgOf`: one message of a sending: the sender's address, the message's number, and its count of
    coins by the sender's own reckoning (`K14.dueOf` at the sender's own job,
    Johnson/Desc/ProofFile/Honest/K14/Sendings.lean). As a `Due`: f is 0, and e is that number
  `senderU`, `senderO`: the addresses of the two parts that send: "send o_u", "send o_omega": part
    0 at `K14.sendPlace 2` and part 0 at `K14.sendPlace 5`
  `sendPub`: the two sendings' public data at a public part Z: `p14At Z` (the shared chain's
    parameters) and `sharedInFront Z (K14.place 1)` (how many rounds of the shared chain come
    before "LIN point"). From the same two calls `nowShared`
    (Johnson/Desc/ProofFile/Honest/SharedChainProverSides.lean) builds the argument of `K14.proverSidesOfSharedSendings`, which
    places the two sendings' parts. `none` where one of the two calls gives `none`

Where the counts come from. No count is written out here, and none is read off the book of coins
(`ProverCoinCounts`, the frame) or off the list of sendings of which the book is made (`Johnson.G.sendsOf`,
Johnson/G/Sends.lean). Each is `K14.dueOf` at the codes and the shape in `A.P`; a sending's own
count of coins (`K14.takesOf`) adds up the same `dueOf` over its messages. So a test that compares
a job with these members with the book compares the senders' reckoning with the book's.

Limits.
- Which messages make a group, and their order, are written out here: read off the text of the
  definition that computes the book (`bookRaw`, Johnson/Desc/ProofFile/Honest/BookWhole.lean) and
  off the shared chain's text (Johnson/Desc/K14/Blocks.lean).
- Nothing here compares them with the groups as the verifier's state lists them (`Group.members`
  in `Statement.groups`, OnBytes/Iop/Ground.lean).
- One message is listed in two groups: message 1 of "send o_omega" is the second element of both
  `membersU A` and `membersO A`, by the same term `msgOf senderO (K14.jobOmega A) 1`. This is a fact
  on the two definitions. Nothing is stated here on what follows from it.
- A default value takes a count's place without a warning. `msgOf` reads the message's shape as
  `(J.Q.sent.getD k default).shape`: where the sending has no message number k, the count is
  `K14.dueOf` at the default shape. The list of messages of `K14.jobU A` is
  `(Desc.K14.withU A.P.S).getD #[]`: it is empty where `withU` (Johnson/Desc/K14/Text.lean) gives
  `none`. That of `K14.jobOmega A` has a message 1 only where `LinShape.sharedSplitNeeded` is true
  (`linMessageOmega`, OnBytes/Iop/Lin.lean). `K14.dueOf` itself reads the two arrays of codes by
  `getD`: at a number beyond an array it counts with the default code. No definition here tests for
  any of these cases. The public test `K14.sendingsFit`
  (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean) asks that `withU` gives a list; it is not
  called here, and it has no clause that a sending has a message 1.
- `freshU` and `freshO` are constants: they read no shape. "send o_u" has a message 1 only where
  `LinShape.masksAhead` is true (`linWithU`, OnBytes/Iop/Lin.lean). `TestJob.freshFits` (Test.lean)
  compares a job's field `fresh` with the test's parameters; it is not called here.
- The last chain's and the first chain's tests have no members here. (These are the tests at
  `placeW` and `placeL`, Places.lean in this folder.)
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.SharedChainProverSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- The part that sends o_u and the first mask. -/
def senderU : Addr := ⟨K14.sendPlace 2, 0⟩
/-- The part that sends o_omega and o_sp. -/
def senderO : Addr := ⟨K14.sendPlace 5, 0⟩

/-- One message of a sending: its sender, its number, its coins by the sender's reckoning. Where the
sending has no message number k, the count is `K14.dueOf` at the default shape, and nothing warns
of it. -/
def msgOf (a : Addr) (J : K14.SendJob) (k : Nat) : Addr × Nat × Due :=
  (a, k, ⟨0, K14.dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k)⟩)

/-- The group of the test on G_u. Its second element is also the second element of `membersO`. -/
def membersU (A : K14.SendPub) : List (Addr × Nat × Due) :=
  [msgOf senderU (K14.jobU A) 0, msgOf senderO (K14.jobOmega A) 1]

/-- The first fresh table of the test on G_u rides with o_u. By the definition: message 1 of
"send o_u", at every shape. -/
def freshU : Option (Addr × Nat) := some (senderU, 1)

/-- The group of the test on G_omega. Its second element is also the second element of
`membersU`. -/
def membersO (A : K14.SendPub) : List (Addr × Nat × Due) :=
  [msgOf senderO (K14.jobOmega A) 0, msgOf senderO (K14.jobOmega A) 1]

/-- The first fold of the test on G_omega sends its own fresh table. -/
def freshO : Option (Addr × Nat) := none

/-- The two sendings' public data at a public part. `none` where `p14At Z` or
`sharedInFront Z (K14.place 1)` is `none`. -/
def sendPub (Z : Pub) : Option K14.SendPub :=
  (p14At Z).bind fun P => (sharedInFront Z (K14.place 1)).map fun a => (⟨P, a⟩ : K14.SendPub)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.senderU
#print axioms ProofFile.Honest.K12.AtProof.senderO
#print axioms ProofFile.Honest.K12.AtProof.msgOf
#print axioms ProofFile.Honest.K12.AtProof.membersU
#print axioms ProofFile.Honest.K12.AtProof.freshU
#print axioms ProofFile.Honest.K12.AtProof.membersO
#print axioms ProofFile.Honest.K12.AtProof.freshO
#print axioms ProofFile.Honest.K12.AtProof.sendPub
