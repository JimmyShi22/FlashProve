-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesSentBeforeTestAtKey.lean: `OldAt` (ColsTerm.lean in this folder) at the key
file's proximity test on the ranges, from one clause on the table at hand and the further hypotheses
that are listed below. `OldAt` is a hypothesis of `cols_term` (ColsTerm.lean), a theorem on a
proximity test: it ties the tables that are at hand before the test to the job's trees. At the job
made of the sending of the multiplicities (`jobOne piKRFull Q rec₀`), at the key file's book at the
written sizes and at whatever coins that book lends the test's two parts: if the table at hand
behind the chain's own tree number 1 is the table that the sending's part makes at the sender's own
coins, the tree at hand holds the job's tree's columns. That is `old_KR`. It is stated at one
written place and one book; the sending's data `Q.data`, `rec₀`, the input, the front and the tables
at hand are free parameters. Eight theorems with their proofs; no definition.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A sending is a sub-protocol of
the kind K1, which sends oracle messages; its public data are a `K1.Par`
(Johnson/Desc/K1/Send.lean), with the codes (`codes`) and the messages in the order of sending
(`sent`). `keyFull` (Johnson/Goal/PlanValues/KeySizedReturns.lean) is the library's written sizes of
a key. The written sending is `parKR` (FrontPlainAtKey.lean in this folder): a `K1.Par` for the
sending of the multiplicities, with the codes `keyFull.codes` and the messages
`Wf.messageOf keyFull.ranges.x` (OnBytes/Iop/Wf.lean). A riding table (`Ride`,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean) is a fold's fresh table that goes out as a message of a
sending: the fold's rounds k, and 2 ^ h rows. `OneSent` (JobOne.lean in this folder) is what a job
takes of a sending: `P`, its public data; `ride`, which gives for a message's number its riding
table, or `none`; `data`, the caller's data as a function of the input only; and `addr`, the address
(`Addr`, the frame: a place and a part's number) of the part that sends, the sender. A job
(`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test.
`jobOne p Q rec₀` (JobOne.lean) is the job made of the sending Q. It has one tree (`Tree`,
Johnson/Desc/K12/Honest/Stages.lean: a depth a and a column for every position; its length is
2 ^ a), whose column is the sending's written column `col Q.P` (Johnson/Prover/Send/Core.lean) of
tree number 0, at rows that the job computes anew. `rec₀` is the job's state on entry to the test. w
is the prover's input, fr a front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what the job's
functions are given of the run before the test). A part (`Part`, the frame) is the prover's side of
some rounds in a row; a proximity test has two (`firstPart`, `restPart`: Parts.lean in this folder).
The sending's part is `sendPart` (Johnson/Desc/ProofFile/Honest/K1/Part.lean): its first move, where
it returns, sends `treeTables` (same file: a table for each tree of the sending) at the part's rows,
which are `rowsR` (K1/Coins.lean) at the part's own coins. A table (`Table`, the frame) has two
numbers, `logLength` and `words`, and a symbol at every natural number. A book (`ProverCoinCounts`, the frame)
is the book of coins: public data that goes with a description. `keyBook K` (E2E/KeyBook.lean) is
the key file's book, made of the data K (`KeyPub`, same file); `fullPub` (E2E/KeyBookAtWritten.lean)
is `KeyPub.of` at `keyFull`, an `Option` of such data. `lendRow` (the frame) returns the coins that
the parts of a list at one place are given, part by part, or an error; it reads the book, a list
`rows` of addresses with counts, and a function `look`, which gives for an address a count (`Due`)
and coins of that count (`Cs`). The sender's purse is `(look Q.addr).2`; the sender's count is
`dueR Q.P Q.ride` (K1/Coins.lean). `piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) is the
written parameters (`P12`), the place among them, of the key file's test on the ranges at the full
size. A stage (`Fmt.M1.Stage`) holds the numbers of one stage of a test; `stA p` (PlanB.lean in this
folder) is the first stage of p. `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean) gives a stage's numbers
as an `Sg` (Cb/Ent/CdStage.lean): among them h, g = k - h, and Z, the code of a mask row, with its
message length `Z.l`. The tables at hand are a structure E (`Env`,
Johnson/Desc/ProofFile/Honest/Side.lean); ColsTerm.lean calls them the available tables. The table
at hand behind a source is the table that `E.tree` gives for it, with a place, or `none`; `E.sent`
is how many trees the chain has sent so far. The source `own n` (`Fmt.TreeSource`, Decl/Declared.lean)
names tree number n of those that the chain sends.

  `old_KR`: under the hypotheses below: `OldAt E T₀ src₀`. T₀ is the list of trees of
    `jobOne piKRFull Q rec₀` at w, fr and C: one tree. C is `restCoins` (Parts.lean) of `c.2.1`,
    which is what `lendRow` returns for the second part. src₀ is `own 1` at number 0. By the two
    fields of `OldAt`: 1 is below `E.sent`; and at every position x below the tree's length,
    `colAt E.tree (own 1) x` (PlanOpens.lean in this folder: the column at x of the table for that
    source) is the tree's column at x
  `planOwn_KR`: the written sending `parKR` passes its own test on the plan, `K1.planOkOwn`
    (Johnson/Desc/K1/Own.lean)
  `size_KR`: `Wf.messageOf keyFull.ranges.x` has two messages
  `noMain_KR`: message number 1 of it has no main row: `shape.mainRows` is 0
  `ride_KR`: the riding table's two numbers are the first stage's: `rideKR 1` (BookTiesAtKey.lean in
    this folder) is `some ⟨h + g, h⟩`, at the h and g of `sgOf (stA piKRFull)`
  `room_KR`: the stage has room for the packing: h + 2 g + 1 ≤ `Z.l`, at `sgOf (stA piKRFull)`. The
    packing is `packedN`; see `packing_sent` (PackingAt.lean in this folder), which has this
    hypothesis
  `planOwn_congr`: of a sending's public data `K1.planOkOwn` reads only the codes and the list of
    messages: it has one value at two `K1.Par` that agree in `codes` and `sent`
  `sent_parKR`: `parKR.sent` is `Wf.messageOf keyFull.ranges.x`

By what. `old_KR` is `old_of_table` (TreesSentBeforeTestFromSentTable.lean in this folder) at n = 1 and at the rows
`rowsR Q.P Q.ride (Q.data w) c₁`. That `Q.P` passes `K1.planOkOwn` follows from `planOwn_KR` by
`planOwn_congr` and `sent_parKR`. That these rows and the job's agree inside the messages' tables
(`SameRows`, TreesSentBeforeTestFromSentTable.lean) is `same_one` (SameAtOne.lean in this folder). Its hypothesis `CoinsTie`
is `coinsTie_KR` (BookTiesAtKey.lean); its four others are `size_KR`, `ride_KR`, `noMain_KR` and
`room_KR`, after rewriting by hs and hr. The five public facts `planOwn_KR`, `size_KR`, `noMain_KR`,
`ride_KR` and `room_KR` have no variable and are proved by the kernel's own evaluation
(`decide +kernel`). `planOwn_congr` unfolds `K1.planOkOwn`, `K1.planOk` and `K1.Par.tuple`
(Send.lean) and rewrites by its two hypotheses; `sent_parKR` is by `simp`.

Hypotheses of `old_KR`. hK: `fullPub = some K`. hc: `Q.P.codes = keyFull.codes`. hs:
`Q.P.sent = Wf.messageOf keyFull.ranges.x`. hr: `Q.ride = rideKR`. ha: `Q.addr = sMsg`
(E2E/KeyTestSizes.lean). h: `lendRow` at `keyBook K`, at any `rows` and `look`, at the place of
`piKRFull` and the job's two parts, from part number 0 on, returns c. hown:
`(look Q.addr).2.cut ⟨0, 0⟩ (dueR Q.P Q.ride) = some c₁`. hn: `1 < E.sent`. hE:
`E.tree (.own 1) = some (pl, T)`; nothing reads the place pl. hT: T is entry number 0 of
`K1.treeTables Q.P` at the rows `rowsR Q.P Q.ride (Q.data w) c₁`. `Q.data`, `rec₀`, w, fr, `rows`,
`look`, E, pl and T are free parameters.

Limits.
- The one clause is asked: that the table at hand behind "own 1" is the sending's part's, at the
  sender's purse cut at its start. In the Lean text it is hE with hT, at the c₁ of hown.
- That clause can be derived from no thread of the frame (`Thread`,
  Johnson/Desc/ProofFile/Honest/Thread/Thr.lean; its statement at a border of a chain is `Thr`) at
  all the states of a run and tables at hand at which that statement holds. A thread compares the
  table at hand with its own by `Table.same` only (`Thread.handAt`; both in that file): the two
  numbers, and the columns below the length; a table has a symbol at every natural number. So
  `old_KR` is a theorem at one family of tables at hand. The form whose hypothesis on the table can
  be proved from a thread is `old_KR_same` (TreesSentBeforeTestFromSameColumns.lean in this folder): there that hypothesis is
  `Table.same` between the two tables. That the second of the two is the table of hT is a hypothesis
  there too.
- `1 < E.sent` (hn) is a second hypothesis on the tables at hand, next to that clause.
- No `SendJob` (K1/Part.lean: what a caller supplies for `sendPart`) occurs in this file: that the
  table of hT is what a `sendPart` sends is not stated in Lean here. `Q.data` reads the input only,
  while the data of a `SendJob` may read the front too.
- That the sender's purse can be cut at its start to the sender's count is a hypothesis (hown): it
  is not shown here.
- That `lendRow` returns is a hypothesis (h): it is not shown here. `lends_KR` (MembersAtKey.lean in
  this folder) shows it at `(keyBook K).rowsOf 0` for `rows` and `k.look 0` for `look`, for every k
  of the type `Coins (keyBook K)`, under hypotheses of its own; it is not called here.
- The job's tree is taken at `restCoins` of what the second part is given. Of what the first part is
  given nothing is stated here.
- `rec₀` is a free parameter. Its values have the type of the verifier's state inside a test (`T12`,
  Johnson/Desc/K12/Join.lean); nothing here shows that they are the verifier's state.
- At written values: the book is the key file's at the library's written sizes `keyFull`, and
  `piKRFull`, `parKR`, `rideKR` and `sMsg` are written values. Nothing here says that these are the
  sizes at the public files. See the limits of BookTiesAtKey.lean and of PlaceKeyRangesFull.lean.
- The option `maxRecDepth` is raised to 1000000 for the whole file.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.BookTiesAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (rowsR dueR)
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (sMsg)

variable {V W X : Type}

theorem planOwn_congr (P P' : K1.Par) (hc : P.codes = P'.codes) (hs : P.sent = P'.sent) :
    K1.planOkOwn P = K1.planOkOwn P' := by
  unfold K1.planOkOwn K1.planOk K1.Par.tuple
  rw [hc, hs]

theorem sent_parKR : parKR.sent = Wf.messageOf keyFull.ranges.x := by
  show ([("", Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray = _
  simp

theorem planOwn_KR : K1.planOkOwn parKR = true := by decide +kernel

theorem size_KR : (Wf.messageOf keyFull.ranges.x).size = 2 := by decide +kernel

theorem noMain_KR : ((Wf.messageOf keyFull.ranges.x).getD 1 default).shape.mainRows = 0 := by
  decide +kernel

theorem ride_KR : rideKR 1 = some ⟨(sgOf (stA piKRFull)).h + (sgOf (stA piKRFull)).g,
    (sgOf (stA piKRFull)).h⟩ := by decide +kernel

theorem room_KR : (sgOf (stA piKRFull)).h + 2 * (sgOf (stA piKRFull)).g + 1 ≤
    (sgOf (stA piKRFull)).Z.l := by decide +kernel

/-- **`OldAt` at the key file's test on the ranges, from a hypothesis on the table at hand.** The
hypotheses, one by one, and the limits are in the file's head. -/
theorem old_KR (K : KeyPub) (hK : fullPub = some K) (Q : OneSent W)
    (hc : Q.P.codes = keyFull.codes) (hs : Q.P.sent = Wf.messageOf keyFull.ranges.x)
    (hr : Q.ride = rideKR) (ha : Q.addr = sMsg) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart (jobOne piKRFull Q rec₀) : Part V W X),
      restPart (jobOne piKRFull Q rec₀)])
    (h : lendRow (keyBook K) rows look piKRFull.place
      [(firstPart (jobOne piKRFull Q rec₀) : Part V W X), restPart (jobOne piKRFull Q rec₀)] 0 =
        .ok c)
    (c₁ : Cs (dueR Q.P Q.ride))
    (hown : (look Q.addr).2.cut ⟨0, 0⟩ (dueR Q.P Q.ride) = some c₁) (E : Env)
    (pl : VerifiableInference.Desc.Place) (T : Table) (hn : 1 < E.sent)
    (hE : E.tree (.own 1) = some (pl, T))
    (hT : (K1.treeTables Q.P (rowsR Q.P Q.ride (Q.data w) c₁))[0]? = some T) :
    OldAt E
      ((jobOne piKRFull Q rec₀).trees₀ w fr (restCoins (jobOne piKRFull Q rec₀) c.2.1).mem
        ((jobOne piKRFull Q rec₀).first w fr (restCoins (jobOne piKRFull Q rec₀) c.2.1)))
      (fun k => [Fmt.TreeSource.own 1].getD k (.own 0)) := by
  have hP : K1.planOkOwn Q.P = true :=
    (planOwn_congr Q.P parKR hc (hs.trans sent_parKR.symm)).trans planOwn_KR
  refine old_of_table piKRFull Q rec₀ w fr _ E 1 _ pl T hP hn hE hT
    (same_one piKRFull Q rec₀ w fr _ c₁
      (coinsTie_KR K hK Q hc hs hr ha rec₀ w rows look c h c₁ hown) (by rw [hs]; exact size_KR)
      (by rw [hr]; exact ride_KR) ?_ room_KR)
  unfold shapeAt
  rw [hs]
  exact noMain_KR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.planOwn_congr
#print axioms ProofFile.Honest.K12.sent_parKR
#print axioms ProofFile.Honest.K12.planOwn_KR
#print axioms ProofFile.Honest.K12.size_KR
#print axioms ProofFile.Honest.K12.noMain_KR
#print axioms ProofFile.Honest.K12.ride_KR
#print axioms ProofFile.Honest.K12.room_KR
#print axioms ProofFile.Honest.K12.old_KR
