-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SameAtOne.lean: the rows that a job made of a sending makes anew
are the sender's own, inside the messages' tables, where the test's coins are the sender's. The
second premise of `old_of_table` (TreesSentBeforeTestFromSentTable.lean in this folder) at `jobOne` (JobOne.lean), from four
equations between the sender's purse and the coins that the test's term reads. In Lean it is the
hypothesis hV of `old_of_table`: two families of rows meet `SameRows` (TreesSentBeforeTestFromSentTable.lean) at every
message of the sending. `same_one` proves it for the sender's rows and the job's rows, under the
hypotheses below; `old_KR` (TreesSentBeforeTestAtKey.lean in this folder) and `old_KR_same` (TreesSentBeforeTestFromSameColumns.lean) call it.
General in the test's parameters p, in what is taken of the sending, Q, in the job's state on entry
`rec₀`, in the prover's input w, in the front fr and in the coins c and C. A definition, a statement
and its proof.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A sending is a sub-protocol of
the kind K1, and Q (`OneSent`, JobOne.lean) is what is taken of one: its public data `P`, what rides
`ride`, the caller's data `data` and the sender's address `addr`. `shapeAt Q.P k` is the shape of
its message number k, and a `Rows` holds one message's main rows, its mask rows and the tails of
both (Johnson/Prover/Send/Core.lean). A part (`Part`, the frame) is the prover's side of a stretch
of a sub-protocol's rounds. Coins (`Cs d`, the frame) are elements of the base field and of the
extension field, as many as the count d states (`Due`: fields `f` and `e`). The sender's purse is c,
coins of the whole sending's count `dueR Q.P Q.ride`; the word does not mean the frame's type
`Purse`. `cf c i` and `ce c i` are its coins number i in the two fields, 0 beyond the count. Message
number k has the count `dueMsg` at its shape, and its coins begin at `startR Q.P Q.ride k`. The
sender's rows are `rowsR Q.P Q.ride (Q.data w) c`: a `Rows` for each message's number. A table rides
in a message where `Q.ride` gives, at the message's number, the table's two numbers (`K1.Ride`: k
rounds, 2 ^ h rows); `rowsR` then makes that message's mask rows of 2 k + 1 coins. `dueR`, `cf`,
`ce`, `dueMsg`, `startR`, `rowsR` and `K1.Ride` are in Johnson/Desc/ProofFile/Honest/K1/Coins.lean.
A job (`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test; w is
the prover's input and fr a front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes
the test). `jobOne p Q rec₀` has one member (an oracle message of the group under test), the
sending's message 0, and names the sending's message 1 as the first fold's fresh table. The term is
`testAll` (Test.lean), and the coins that it reads are C (`TestCoins`, Test.lean: fields `hide`,
`tails`, `mem`, `rest`). `C.mem 0` is the member's stretch (`Stretch`, Coins.lean in this folder: a
run of coins, read by number). The job's rows are `Q.rows w (C.mem 0) Pst` (`OneSent.rows`,
JobOne.lean), where Pst is the first stage's state `(jobOne p Q rec₀).first w fr C`. At message 0
they are `rowsR` at coins made of the stretch. At every other number the main rows and their tails
are 0, the mask rows are `Pst.fM` and their tails `Pst.fT`; `TestJob.first` (Test.lean) sets these
two to the packing `packedN` (Johnson/Prover/Link/BodyPack.lean) of `hideAt` (Coins.lean) at
`C.hide`, and to `C.tails`. The stage is `stA p` (PlanB.lean in this folder), the test's first
stage, or the default stage where the test has none; h, g and `Z` are the fields of `sgOf`
(Johnson/Desc/K12/Law/ChainOf.lean) at it: the stage's h, its k - h and its mask code.

  `same_one`: `CoinsTie` · the sending has two messages · the fresh table rides as message 1, which
    has no main row · the stage has room for the packing ⟹ `SameRows` at both messages. In Lean: at
    every k below `Q.P.sent.size`, `SameRows Q.P` of the sender's rows and the job's rows at k
  `CoinsTie Q w a c C`: the four equations: the member's stretch holds the purse's coins of message
    0, of each field · the hiding polynomial's coefficients are the purse's coins of message 1's
    riding table · the fresh table's tails are that message's mask rows' tails. A definition, a
    structure of four propositions; h and g are here those of `sgOf a`. Field by field. `memF`,
    `memE`: in each field, at i below message 0's count, coin number i of c is coin number i of
    `C.mem 0`. `hide`: at i below 2 (h + g) + 1, `ce c (m + i)` is `C.hide i`, where m is
    `(startR Q.P Q.ride 1).e` plus, where message 1's `mainDeg` is 3 (main rows over the extension
    field), the count of its main rows' coins (`Steps.main` of `K1.stepsOf`): from number m on
    `rowsR` takes the coins of that message's mask rows. `tails`: at r below message 1's number of
    mask rows and q below `r` of its mask code, `maskTl r q` of the sender's rows of message 1 is
    `C.tails r q`

By what. Message 0: `mem_is_sent` (RowsCongr.lean). Message 1, the first fold's fresh table: the two
packings are one (`packing_sent`, PackingAt.lean; `hideAt_congr`, AgreeBook.lean). Step by step: at
message 0 `mem_is_sent`, from `memF` and `memE`, gives that the two `Rows` are equal, so all six
fields of `SameRows` hold. At message 1 the four fields on main rows are vacuous by hm. The field
`mask` is rewritten by `packing_sent`, whose right side is `packedN` at `hideAt` of the purse's
coins from number m on, cut at 2 (h + g) + 1, and by `hideAt_congr` with `hide`. The field `maskTl`
is `tails`. The three files are in this folder.

Hypotheses of `same_one`. T: `CoinsTie Q w (stA p) c C`. h2: `Q.P.sent.size` is 2. hR: `Q.ride 1` is
`some ⟨h + g, h⟩`: h + g rounds, 2 ^ h rows. hm: `mainRows` of `shapeAt Q.P 1` is 0. hl:
h + 2 g + 1 ≤ `Z.l`: a mask row's message has room for the packing.

Limits.
- `CoinsTie` is asked: a matter of the book's carried entries. That is, it is a hypothesis of
  `same_one` and is proved nowhere in this file. The book is `ProverCoinCounts` (the frame); an entry of it
  (`Ahead`) is a block of its owner's coins that one other part is given too, marked as spent or as
  carried. `coinsTie_of_book` (CoinsTieBook.lean in this folder) derives `CoinsTie` from a clause on
  the book and the plan, `BookTies`, under further hypotheses, and only at the C that `restCoins`
  (Parts.lean in this folder) makes of what the test's second part is given.
- c, C and `rec₀` are free parameters. That a sender's part is given c, or that a part of the test
  is given C, is not stated here, and nothing compares `rec₀` with the verifier's state.
- `CoinsTie` has no equation on `C.rest`, which `testAll` reads too, on `C.mem` at a number other
  than 0, or beyond the bounds in its four fields.
- `CoinsTie` has no clause that the numbers at which it reads c are below the count. Beyond the
  count `cf` and `ce` give 0, and the equation then says that the value of C is 0: a 0 is read in a
  coin's place. `BookTies` (CoinsTieBook.lean) has bounds of this kind (`in0f`, `in0e`, `in1`).
- The bound in `hide` is counted by the stage a, not by `Q.ride 1`; the two agree under hR.
- w enters `CoinsTie` through `Q.data w` in `tails` only, and by the text of `rowsR` its `maskTl`
  does not read the data.
- `SameRows` compares the rows inside the messages' tables only: below the shape's numbers of rows,
  the codes' message lengths and the tails' lengths. Outside them nothing is stated.
- `same_one` is stated at `jobOne` only, for a sending of two messages whose message 1 has no main
  row.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable
import Johnson.Desc.ProofFile.Honest.K12.RowsCongr
import Johnson.Desc.ProofFile.Honest.K12.PackingAt
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (rowsR dueR dueMsg startR cf ce)
open H2K.Pub (sgOf)

variable {W X : Type}

/-- The four equations between the sender's purse and the coins that the term reads. Q: what is
taken of the sending. w: the prover's input. a: the test's first stage (`stA p` in `same_one`). c:
the purse. C: the term's coins. -/
structure CoinsTie (Q : OneSent W) (w : W) (a : Fmt.M1.Stage) (c : Cs (dueR Q.P Q.ride))
    (C : TestCoins) : Prop where
  memF : ∀ i, i < (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).f → cf c i = (C.mem 0).f i
  memE : ∀ i, i < (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).e → ce c i = (C.mem 0).e i
  hide : ∀ i, i < 2 * ((sgOf a).h + (sgOf a).g) + 1 →
    ce c ((startR Q.P Q.ride 1).e +
      (if (shapeAt Q.P 1).mainDeg == 3 then
        (K1.stepsOf Q.P.codes (shapeAt Q.P 1) (Q.ride 1)).main else 0) + i) = C.hide i
  tails : ∀ r q, r < (shapeAt Q.P 1).maskRows →
    q < (codeOf (Q.P.codes.mask.getD (shapeAt Q.P 1).maskCode default)).r →
    (rowsR Q.P Q.ride (Q.data w) c 1).maskTl r q = C.tails r q

/-- **The sender's rows and the job's agree inside the messages' tables.** T: the four equations.
h2: the sending has two messages. hR: the fresh table rides as message 1, with h + g rounds and
2 ^ h rows. hm: message 1 has no main row. hl: the stage has room for the packing. -/
theorem same_one (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (C : TestCoins) (c : Cs (dueR Q.P Q.ride)) (T : CoinsTie Q w (stA p) c C)
    (h2 : Q.P.sent.size = 2)
    (hR : Q.ride 1 = some ⟨(sgOf (stA p)).h + (sgOf (stA p)).g, (sgOf (stA p)).h⟩)
    (hm : (shapeAt Q.P 1).mainRows = 0)
    (hl : (sgOf (stA p)).h + 2 * (sgOf (stA p)).g + 1 ≤ (sgOf (stA p)).Z.l) :
    ∀ k, k < Q.P.sent.size → SameRows Q.P (rowsR Q.P Q.ride (Q.data w) c)
      (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) k := by
  intro k hk
  rw [h2] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · obtain rfl := Nat.lt_one_iff.1 hk
    have e : rowsR Q.P Q.ride (Q.data w) c 0 =
        Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C) 0 :=
      mem_is_sent Q w (C.mem 0) c T.memF T.memE
    exact ⟨fun _ _ _ _ => by rw [e], fun _ _ _ _ => by rw [e], fun _ _ _ _ => by rw [e],
      fun _ _ _ _ => by rw [e], fun _ _ _ _ => by rw [e], fun _ _ _ _ => by rw [e]⟩
  · refine ⟨fun r _ hr _ => ?_, fun r _ hr _ => ?_, fun r _ hr _ => ?_, fun r _ hr _ => ?_,
      fun r j hr hj => ?_, fun r q hr hq => T.tails r q hr hq⟩
    · rw [hm] at hr
      cases hr
    · rw [hm] at hr
      cases hr
    · rw [hm] at hr
      cases hr
    · rw [hm] at hr
      cases hr
    · rw [packing_sent (sgOf (stA p)) hl Q.P Q.ride (Q.data w) c 1 r j hR hr hj]
      show _ = packedN (sgOf (stA p)) (hideAt ((sgOf (stA p)).h + (sgOf (stA p)).g) C.hide) r j
      rw [hideAt_congr _ _ C.hide fun i hi => by rw [if_pos hi]; exact T.hide i hi]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.same_one
#print axioms ProofFile.Honest.K12.CoinsTie
