-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/MembersAtKey.lean: at the key file's book the row of the two parts
of the test on the ranges is lent its coins, at every family of a run's coins, for the job made of
the sending of the multiplicities. The frame's lending refuses a part that is typed at another count
of coins than the book's entry has. `jobOne` (JobOne.lean in this folder) states its one member at
the count that `K1.dueMsg` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) computes for the sending's
message number 0. `full_lays` (StepsAtKey.lean in this folder), the closed statement on the key
file's book, is at `jobKR`: the skeleton `jobRanges` (E2E/KeyTestSizes.lean), in which that count is
a literal, with `piKRFull` for its field `p`. Here the two counts are held against each other by the
kernel's own evaluation: so the laws that take "the row is lent its coins c" as a premise are not
empty on that account. One such theorem is `coinsTie_KR` (BookTiesAtKey.lean in this folder), in its
hypothesis h. Three theorems with their proofs. `due_KR` is on closed terms. `members_KR` holds at
every Q that meets four equations and at every `rec₀`; `lends_KR` besides at every block and list of
prover's sides that meet its hypotheses, and at all types S, Cl, V, W and X. All three are at one
written value of the sizes.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A book (`ProverCoinCounts`) is public data that
goes with a description: for each chain a table of the parts that have coins of their own, each with
its count (`ProverCoinCounts.rowsOf`: chain number 0 is the first chain); the entries; and for each place the
cut, that is how many rounds each of its parts has. An entry of it (`Ahead`) is a block of its
owner's coins that one other part, its spender, is given too, marked as spent or as carried. The key
file's book is `keyBook K` (E2E/KeyBook.lean). The written sizes are `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean); `fullPub` (E2E/KeyBookAtWritten.lean) is what
`KeyPub.of` returns at them, an `Option KeyPub`. `Coins B` is the type of the coins of one run at
the book B: a value of it is a family of a run's coins. `Coins.look` gives, by address, the coins
that a chain may be given. An address (`Addr`) is a place (`Place`, Johnson/Desc/Block.lean: where a
sub-protocol is in a description) and a part's number. A count (`Due`) is a number of coins of the
base field and one of the extension field. A part (`Part`) is the prover's side of some consecutive
rounds; it states its own count, and the names and counts of the blocks that it is given. The
lending is `lendRow`: from a book, a chain's table and coins, a place and a list of parts it
computes what each part is given, or an error. It goes through `lend`, which returns an error where
the name or the count that the part states for a block is not the entry's. The laying of the steps
is `chainSteps`: from a book, a chain's table and coins, a list of blocks (`Block`,
Johnson/Desc/Block.lean: a sub-protocol at its place) and a list of prover's sides (`Placed`: a
place with a list of parts) it computes the chain's rounds (`Step`), or an error. Either returns
where its value is `.ok`. A job (`TestJob`, Test.lean in this folder) is what a caller supplies for
its proximity test. Its field `p` (`P12`, Johnson/Desc/K12/Frame.lean) holds the test's parameters,
the place `p.place` among them. `members` lists the oracle messages of the test's group: for each
the sender's address, the message's number in that part's sending, and its count. `fresh` names the
first fold's fresh table by address and number in the same way. The half is `proverSideOfProximityTest J` (Parts.lean
in this folder): the prover's side at `J.p.place` with the two parts `firstPart J` and `restPart J`;
the row is the list of these two. Each of the two states every member's count among the blocks that
it carries (`memberRuns`, Parts.lean). A block b seats the test where `SeatOf b J enter leave` holds
(SaysYesSeat.lean in this folder): b has the place, the rounds and the oracle messages of the test's
own block `proximityTestKind guardedProximityTestParts J.p`, and its decision is `enter`, then that block's decision, then `leave`.
`piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) is a closed term of the type `P12`, meant
to be the place of the key file's proximity test on the ranges at the full size. A sending is a
sub-protocol of the kind K1, which sends oracle messages. `OneSent` (JobOne.lean) is what a job
takes of a sending: `P`, its public data (`K1.Par`, Johnson/Desc/K1/Send.lean), with the codes
(`codes`) and the messages in the order of sending (`sent`); `ride`, which gives for a message's
number its riding table (a fold's fresh table that goes out as a message of a sending), or `none`;
the caller's `data`; and `addr`, the sender's address. `jobOne p Q rec₀` is the job made of the
sending Q. The written sending, that of the multiplicities, is given by four closed terms: the codes
`keyFull.codes`; the messages `Wf.messageOf keyFull.ranges.x` (OnBytes/Iop/Wf.lean); `rideKR` for
`ride` (BookTiesAtKey.lean: ⟨4, 4⟩ at message number 1, `none` elsewhere); and the address `sMsg`
(E2E/KeyTestSizes.lean, which calls message number 0 the lookups' own message).

  `members_KR`: at every Q with the written codes and messages, `rideKR` and `sMsg`, and at every
    `rec₀`: the list `members` of `jobOne piKRFull Q rec₀` is that of the skeleton `jobRanges`. Both
    are the list of the one entry `(sMsg, 0, ⟨98, 36864 + 441⟩)`
  `lends_KR`: so, at the key file's book at the written sizes, at every block that seats the test,
    wherever the half is laid, at all coins: the row is lent its coins, and the laying of the
    member's steps returns (`steps_ranges`). In Lean, with J for `jobOne piKRFull Q rec₀`, under the
    hypotheses below, at every `k : Coins (keyBook K)` and `v : Option V`: there is a c such that
    `lendRow`, at the table `(keyBook K).rowsOf 0`, the coins `k.look 0`, the place `J.p.place` and
    the list `[firstPart J, restPart J]`, is `.ok c`, and `chainSteps`, at the same table and coins,
    v, the list of one block `[b]` and hl, is `.ok ((proverSideOfProximityTest J).steps b v c)`. In the Lean text the
    steps are those of the half, that is of both its parts
  `due_KR`: the count of message 0 of the written sending: 98 coins of the base field, 37,305 of the
    extension field: by the kernel. In Lean: `K1.dueMsg`, at `keyFull.codes`, the shape of entry
    number 0 of `Wf.messageOf keyFull.ranges.x` and `rideKR 0`, is `⟨98, 36864 + 441⟩`

By what. `due_KR`: `decide +kernel` on closed terms. `members_KR`: each of the two lists is by
definition a list of one entry (`show`); `shapeAt` (Johnson/Prover/Send/Core.lean) is unfolded, and
rewriting by ha, hc, hs, hr and `due_KR` makes the two entries one term. `lends_KR` is
`steps_ranges` (StepsAtKey.lean) at the job J. Of that theorem's hypotheses, `J.p = piKRFull` holds
by `rfl`; that the members are those of `jobRanges` is `members_KR`; that `fresh` is that of
`jobRanges`, `some (sMsg, 1)`, holds by `rfl` after rewriting by ha. `steps_ranges` in turn takes
`full_lays`. The option `maxRecDepth` is raised to 1000000 for the whole file.

Hypotheses of `lends_KR`. hK: `fullPub = some K`. hc: `Q.P.codes = keyFull.codes`. hs:
`Q.P.sent = Wf.messageOf keyFull.ranges.x`. hr: `Q.ride = rideKR`. ha: `Q.addr = sMsg`. hb:
`SeatOf b J enter leave`, at any `enter` and `leave`. hh: the first prover's side in hl whose place
is `J.p.place` is `proverSideOfProximityTest J`; hl is any list that meets this. `members_KR` has hc, hs, hr and ha
only. `rec₀` and `Q.data` are free parameters; of `Q.P` only `codes` and `sent` are bound.

Limits.
- At written values. `keyFull`, `piKRFull`, `jobRanges`, `rideKR` and `sMsg` are closed terms;
  nothing here says that `keyFull` holds the sizes at the public files. By the limits of
  E2E/KeyTestSizes.lean no theorem ties the members, the senders or the counts of `jobRanges` to the
  description.
- It says that the lending returns; nothing on what the coins are.
- hc, hs, hr and ha are hypotheses: no sending is built here, and nothing here says that the key
  file's description has a sending with these values.
- hK, hb and hh are hypotheses too: no block and no list of prover's sides is built here, and no
  value is given here that meets the three together.
- The first chain only: the table is `(keyBook K).rowsOf 0` and the coins are `k.look 0`.
- `chainSteps` is taken at the one block b: nothing is stated on a chain's whole list of blocks.
- The limits of StepsAtKey.lean hold of `lends_KR` as well. Among them: for some of `piKRFull`'s
  numbers the print of a run of Lean's evaluator is trusted; the book's carried entries are a
  proposal; that the part which sends the member message takes the book's row for it, and reads the
  message at that stretch, is not shown here either.
- This file has no negative test.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.BookTiesAtKey
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Send (shapeAt)
open H2K.Member (piKRFull)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (sMsg jobRanges)

variable {S Cl V W X : Type}

/-- The count of message 0 of the written sending: `K1.dueMsg`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean) there is 98 coins of the base field and 36864 + 441 of
the extension field. By an evaluation in Lean's kernel. -/
theorem due_KR : K1.dueMsg keyFull.codes ((Wf.messageOf keyFull.ranges.x).getD 0 default).shape
    (rideKR 0) = ⟨98, 36864 + 441⟩ := by decide +kernel

/-- **The job's list of members is the skeleton's.** The job is `jobOne piKRFull Q rec₀`, the
skeleton `jobRanges` (E2E/KeyTestSizes.lean). hc, hs, hr, ha: Q has the codes, the messages, the
riding tables and the address of the written sending. -/
theorem members_KR (Q : OneSent W) (hc : Q.P.codes = keyFull.codes)
    (hs : Q.P.sent = Wf.messageOf keyFull.ranges.x) (hr : Q.ride = rideKR) (ha : Q.addr = sMsg)
    (rec₀ : W → Front X → T12) : (jobOne piKRFull Q rec₀).members = jobRanges.members := by
  show [(Q.addr, 0, K1.dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0))] =
    [(sMsg, 0, ⟨98, 36864 + 441⟩)]
  unfold shapeAt
  rw [ha, hc, hs, hr, due_KR]

/-- **At the key file's book the row is lent its coins, at all coins.** In Lean: `lendRow` at the
list of the two parts and `chainSteps` at the one block b (both: the frame) are `.ok`, at every
`k : Coins (keyBook K)`. The head explains the terms and lists the hypotheses. -/
theorem lends_KR (K : KeyPub) (hK : fullPub = some K) (Q : OneSent W)
    (hc : Q.P.codes = keyFull.codes) (hs : Q.P.sent = Wf.messageOf keyFull.ranges.x)
    (hr : Q.ride = rideKR) (ha : Q.addr = sMsg) (rec₀ : W → Front X → T12) (b : Block S Cl)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hb : SeatOf b (jobOne piKRFull Q rec₀) enter leave) (hl : List (Placed V W X))
    (hh : (hl.find? fun g => g.place == (jobOne piKRFull Q rec₀).p.place) =
      some (proverSideOfProximityTest (jobOne piKRFull Q rec₀))) (k : Coins (keyBook K)) (v : Option V) :
    ∃ c, lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0) (jobOne piKRFull Q rec₀).p.place
        [(firstPart (jobOne piKRFull Q rec₀) : Part V W X), restPart (jobOne piKRFull Q rec₀)]
        0 = .ok c ∧
      chainSteps (keyBook K) ((keyBook K).rowsOf 0) (k.look 0) v [b] hl =
        .ok ((proverSideOfProximityTest (jobOne piKRFull Q rec₀)).steps b v c) :=
  steps_ranges K hK (jobOne piKRFull Q rec₀) rfl (members_KR Q hc hs hr ha rec₀)
    (by rw [show (jobOne piKRFull Q rec₀).fresh = some (Q.addr, 1) from rfl, ha]; rfl) b enter
    leave hb hl hh k v

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.due_KR
#print axioms ProofFile.Honest.K12.members_KR
#print axioms ProofFile.Honest.K12.lends_KR
