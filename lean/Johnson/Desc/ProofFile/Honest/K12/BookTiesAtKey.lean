-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/BookTiesAtKey.lean: the hypothesis `BookTies` (CoinsTieBook.lean
in this folder) as an executable test, `bookTiesB`, and that test at the key file's book of coins
(`keyBook`, E2E/KeyBook.lean) at the library's written sizes `keyFull`, at the key file's proximity
test on the ranges and the sending of the multiplicities: it is true there, by the kernel's own
evaluation (`decide +kernel`). So at that book the coins that the test's term reads are the sender's
(`CoinsTie`), whatever coins the run has. This is proved of the second part's reader only
(`restCoins`, Parts.lean in this folder), for its fields `hide`, `tails` and `mem 0`, each within
the bounds in `CoinsTie`; its field `rest` has the second part's own coins, and on what the first
part's moves read nothing is stated. Two executable definitions and five theorems. `bookTiesB` and
its two lemmas are general; the rest is at one book, at one written value of the sizes.

In the list: a book (`ProverCoinCounts`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is public data.
An entry of it (`Ahead`) is a block of its owner's coins that one other part, its spender, is given
too, marked as spent or as carried. A part (`Part`, the frame) is the prover's side of some rounds
in a row; a proximity test has two (`firstPart`, `restPart`: Parts.lean in this folder), with the
numbers 0 and 1 at the test's place (`Place`: where a sub-protocol is in a description). An address
(`Addr`, the frame) is a place and a part's number. A sending is a sub-protocol of the kind K1,
which sends oracle messages; its public data are a `K1.Par` (Johnson/Desc/K1/Send.lean), with the
codes (`codes`) and the list of messages (`sent`). A riding table (`Ride`,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean) is a fold's fresh table that goes out as a message of a
sending: the fold's rounds k, and 2 ^ h rows. `OneSent` (JobOne.lean in this folder) is what a job
takes of a sending: `P`, its public data; `ride`, which gives for a message's number its riding
table, or `none`; the caller's `data`; and `addr`, the address of the part that sends, the sender. A
job (`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test;
`jobOne p Q rec₀` (JobOne.lean) is the job made of the sending Q. A stage (`Fmt.M1.Stage`) holds the
numbers of one stage of a test; `stA p` (PlanB.lean in this folder) is the first stage of p.
`piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) is the written parameters (`P12`), the
place among them, of the key file's test on the ranges at the full size. `CoinsTie Q w a c C`
(SameAtOne.lean in this folder) is a structure of four equations between c, of the type of the coins
of the sender's count `dueR Q.P Q.ride`, and C, a `TestCoins` (Test.lean: the coins that `testAll`,
the test's term, reads, by number). `fullPub` (E2E/KeyBookAtWritten.lean) is `KeyPub.of` at
`keyFull`: an `Option` of the data of which the book is made (`KeyPub`, E2E/KeyBook.lean).
`atFull f` (E2E/KeyBookAtWritten.lean) is `(fullPub.map f).getD false`.

  `full_bookTies`: `bookTiesB` is true at the key file's book at the written sizes, the place of
    `piKRFull` and its first stage, the written sending `parKR` (FrontPlainAtKey.lean in this
    folder), the riding table ⟨4, 4⟩ (`rideKR`) and the sender's address `sMsg`
    (E2E/KeyTestSizes.lean): by the kernel. `atFull` is false where `fullPub` is `none`: the theorem
    is not true for lack of a book
  `coinsTie_KR`: so `CoinsTie` at `jobOne piKRFull Q rec₀`, at every sending with the written codes
    and messages, that riding table and that address, at whatever coins are lent
  `bookTies_of_B`: at every book, place, stage and Q: where `bookTiesB` is true at `Q.P`, `Q.ride`
    and `Q.addr`, there are two entries e₀ and e₁ at which `BookTies` holds
  `full_bookTies_no`: negative tests: false at another sender's address; with no riding table; at
    the book without its carried entries. In the Lean text these are `⟨sMsg.place, 1⟩` for `sMsg`,
    `fun _ => none` for `rideKR`, and `keyBook K false`; all else is as in `full_bookTies`. By the
    kernel too
  `bookTiesB_congr`: of the sending's public data `bookTiesB` reads only the codes and the list of
    messages: it has one value at two `K1.Par` that agree in `codes` and `sent`
  `bookTiesB Bk pl a P ride addr`: a definition, a `Bool`: all clauses of `BookTies`, on the book,
    the place, the stage, the sending's public data, `ride` and the sender's address. It takes the
    entries number 0 and 1 of `carryE Bk ⟨pl, 0 + 1⟩`
    (Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean): the book's entries whose spender is part
    number 1 at pl and which are marked as carried. It is false where one of the two is lacking
  `rideKR`: a definition: `ride` for the sending of the multiplicities: the riding table ⟨4, 4⟩,
    that is k = 4 and h = 4, at message number 1; `none` at every other number

By what. `full_bookTies` and `full_bookTies_no` are proved by `decide +kernel`: Lean's kernel
evaluates `atFull` at the test, and with it `KeyPub.of`, `keyBook` and `carryE`. `bookTiesB_congr`
unfolds `bookTiesB`, `dueR` and `startR` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) and `shapeAt`
(Johnson/Prover/Send/Core.lean), and rewrites by its two hypotheses. `bookTies_of_B` splits the
test's `match` and reads off each `decide`. `coinsTie_KR` unfolds `atFull` in `full_bookTies`,
rewrites by hK, hr and ha, passes from `parKR` to `Q.P` by `bookTiesB_congr`, takes the two entries
from `bookTies_of_B` and calls `coinsTie_of_book` (CoinsTieBook.lean).

Hypotheses of `coinsTie_KR`. hK: `fullPub = some K`. hc: `Q.P.codes = keyFull.codes`. hs:
`Q.P.sent = Wf.messageOf keyFull.ranges.x`. hr: `Q.ride = rideKR`. ha: `Q.addr = sMsg`. h: `lendRow`
(the frame) at `keyBook K`, at any `rows` and `look`, at the place of `piKRFull` and the job's two
parts, from part number 0 on, returns c. hown:
`(look Q.addr).2.cut ⟨0, 0⟩ (dueR Q.P Q.ride) = some c₁`. The conclusion is `CoinsTie` at Q, any
input w, `stA piKRFull`, c₁ and `restCoins` (Parts.lean) of `c.2.1`, which is what `lendRow` returns
for the second part. `rec₀` and `Q.data` are free parameters.

Limits.
- At written values: the book is the key file's at the library's written sizes `keyFull`. Nothing
  here says that these are the sizes at the public files.
- `piKRFull` was written off a print, the text that a run of Lean's evaluator printed (the limits of
  Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean); in scope (`InScope Z = true`) it is compared with
  the description's own numbers (`place_sourced`, E2E/KeyRangesK12.lean (not in the library yet)).
  That theorem has a further hypothesis (`KeySourced`), and it is not called here.
- That the sender's own coins are its purse cut at the start is asked in `coinsTie_KR`. It is the
  hypothesis hown; in the Lean text the purse is `(look Q.addr).2`. It is proved at no value in this
  file.
- That `lendRow` returns is a hypothesis of `coinsTie_KR` too (h): it is not shown here.
- `coinsTie_KR` concludes on `restCoins` of what the second part is given. Of what the first part is
  given nothing is stated here.
- The three negative tests of `full_bookTies_no` change the sender's address, which the clauses
  `own0` and `own1` read (the clauses' names are the fields of `BookTies`); `ride`; and the book's
  carried entries. None of them changes only what one of the clauses `start0`, `start1`, `in0f`,
  `in0e`, `in1`, `k`, `tail` or `rows` reads: so no evaluation here has the test false by one of
  these clauses alone.
- The book's carried entries are a proposal: see the limits of E2E/KeyBook.lean. In Lean they are
  `K.carried`, which `keyBook K false` leaves out.
- Nothing on how a coin is sampled.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.CoinsTieBook
import Johnson.Desc.ProofFile.Honest.K12.FrontPlainAtKey
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (Ride dueR dueMsg startR)
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyBook (atFull keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (sMsg)

variable {V W X : Type}

/-- `BookTies` (CoinsTieBook.lean) as a test that returns a `Bool`. pl: the test's place. a: its
first stage. P, ride, addr: what `BookTies` reads as `Q.P`, `Q.ride`, `Q.addr`. False where `carryE`
at part number 1 of pl has no entry number 0 or no entry number 1. -/
def bookTiesB (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (a : Fmt.M1.Stage) (P : K1.Par)
    (ride : ℕ → Option Ride) (addr : Addr) : Bool :=
  match (carryE Bk ⟨pl, 0 + 1⟩)[0]?, (carryE Bk ⟨pl, 0 + 1⟩)[1]? with
  | some e₀, some e₁ =>
    decide (e₀.owner = addr) && decide (e₁.owner = addr) && decide (e₀.start = ⟨0, 0⟩) &&
    decide (e₁.start.e = (startR P ride 1).e +
      (if (shapeAt P 1).mainDeg == 3 then (K1.stepsOf P.codes (shapeAt P 1) (ride 1)).main
        else 0)) &&
    decide ((dueMsg P.codes (shapeAt P 0) (ride 0)).f ≤ (dueR P ride).f) &&
    decide ((dueMsg P.codes (shapeAt P 0) (ride 0)).e ≤ (dueR P ride).e) &&
    decide (e₁.start.e + dueFresh a ≤ (dueR P ride).e) && decide (ride 1 = some ⟨a.k, a.h⟩) &&
    decide (a.k = (sgOf a).h + (sgOf a).g) &&
    decide ((P.codes.mask.getD (shapeAt P 1).maskCode default).r = a.Z.r) &&
    decide ((shapeAt P 1).maskRows = 2 ^ a.h)
  | _, _ => false

/-- Of the sending's public data the test reads only its codes and its list of messages. -/
theorem bookTiesB_congr (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (a : Fmt.M1.Stage)
    (P P' : K1.Par) (ride : ℕ → Option Ride) (addr : Addr) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : bookTiesB Bk pl a P ride addr = bookTiesB Bk pl a P' ride addr := by
  unfold bookTiesB dueR startR shapeAt
  rw [hc, hs]

/-- **Where the test is true, there are two entries at which `BookTies` holds.** -/
theorem bookTies_of_B (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (a : Fmt.M1.Stage)
    (Q : OneSent W) (h : bookTiesB Bk pl a Q.P Q.ride Q.addr = true) :
    ∃ e₀ e₁, BookTies Bk pl a Q e₀ e₁ := by
  unfold bookTiesB at h
  split at h
  · rename_i e₀ e₁ h0 h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩ := h
    exact ⟨e₀, e₁, h0, h1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  · cases h

/-- The riding table of the sending of the multiplicities, by the message's number: message number 1
is a fold's fresh table with k = 4 and h = 4; no other message is one. -/
def rideKR (i : ℕ) : Option Ride := if i == 1 then some ⟨4, 4⟩ else none

/-- **The test is true at the key file's book, at the written sizes.** At the place of `piKRFull`
and its first stage, the sending `parKR`, `rideKR` and the sender's address `sMsg`. -/
theorem full_bookTies : atFull (fun K =>
    bookTiesB (keyBook K) piKRFull.place (stA piKRFull) parKR rideKR sMsg) = true := by
  decide +kernel

/-- Negative tests: the test is false at `⟨sMsg.place, 1⟩` for `sMsg`; at `fun _ => none` for
`rideKR`; at `keyBook K false`, the book without its carried entries. -/
theorem full_bookTies_no :
    atFull (fun K => !bookTiesB (keyBook K) piKRFull.place (stA piKRFull) parKR rideKR
        ⟨sMsg.place, 1⟩) = true ∧
      atFull (fun K => !bookTiesB (keyBook K) piKRFull.place (stA piKRFull) parKR
        (fun _ => none) sMsg) = true ∧
      atFull (fun K => !bookTiesB (keyBook K false) piKRFull.place (stA piKRFull) parKR rideKR
        sMsg) = true := by
  decide +kernel

/-- **The coins that the term reads are the sender's, at the key file's book.** Concluded at the
second part's reader `restCoins` only, for its fields `hide`, `tails` and `mem 0`, within the bounds
in `CoinsTie`. The hypotheses, one by one, and the limits are in the file's head. -/
theorem coinsTie_KR (K : KeyPub) (hK : fullPub = some K) (Q : OneSent W)
    (hc : Q.P.codes = keyFull.codes) (hs : Q.P.sent = Wf.messageOf keyFull.ranges.x)
    (hr : Q.ride = rideKR) (ha : Q.addr = sMsg) (rec₀ : W → Front X → T12) (w : W)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart (jobOne piKRFull Q rec₀) : Part V W X),
      restPart (jobOne piKRFull Q rec₀)])
    (h : lendRow (keyBook K) rows look piKRFull.place
      [(firstPart (jobOne piKRFull Q rec₀) : Part V W X), restPart (jobOne piKRFull Q rec₀)] 0 =
        .ok c)
    (c₁ : Cs (dueR Q.P Q.ride))
    (hown : (look Q.addr).2.cut ⟨0, 0⟩ (dueR Q.P Q.ride) = some c₁) :
    CoinsTie Q w (stA piKRFull) c₁ (restCoins (jobOne piKRFull Q rec₀) c.2.1) := by
  have hB : bookTiesB (keyBook K) piKRFull.place (stA piKRFull) Q.P Q.ride Q.addr = true := by
    have k := full_bookTies
    unfold atFull at k
    rw [hK] at k
    rw [hr, ha, bookTiesB_congr _ _ _ Q.P parKR _ _ hc (hs.trans (by
      show _ = ([("", Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray
      simp))]
    exact k
  obtain ⟨e₀, e₁, B⟩ := bookTies_of_B _ _ _ Q hB
  exact coinsTie_of_book piKRFull Q rec₀ w (keyBook K) rows look c h c₁ hown e₀ e₁ B

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bookTiesB_congr
#print axioms ProofFile.Honest.K12.bookTies_of_B
#print axioms ProofFile.Honest.K12.full_bookTies
#print axioms ProofFile.Honest.K12.full_bookTies_no
#print axioms ProofFile.Honest.K12.coinsTie_KR
#print axioms ProofFile.Honest.K12.bookTiesB
#print axioms ProofFile.Honest.K12.rideKR
