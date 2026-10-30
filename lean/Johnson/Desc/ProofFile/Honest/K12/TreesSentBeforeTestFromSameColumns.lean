-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesSentBeforeTestFromSameColumns.lean: `OldAt` (ColsTerm.lean in this folder) from a table
at hand that shows what the sending's table shows. `OldAt` is a hypothesis of `cols_term`
(ColsTerm.lean), a theorem on a proximity test: it ties the tables that are available before the
test to the job's trees. The theorems `old_of_table` (TreesSentBeforeTestFromSentTable.lean in this folder) and `old_KR`
(TreesSentBeforeTestAtKey.lean in this folder) prove `OldAt` at a job made of one sending (`jobOne`, JobOne.lean in
this folder), and they take the table at hand to be the sending's part's table. A thread (`Thread`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) of the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean) compares the table at hand with the thread's own table by
`Table.same` only (`Thread.handAt`; both in Thr.lean): the two numbers, and the columns below the
length. A table's symbols are a function on all natural numbers, so equality of the two tables
cannot be derived at every state of a run and every family of available tables at which a thread's
statement (`Thr`, Thr.lean) holds. That is by reading: no theorem states it. `OldAt` asks the
columns below 2 ^ depth alone, and the job's tree's depth is the sending's table's own log-length:
so "shows the same" is enough. `oldAt_of_same` is general in the test's place p, in what is taken of
the sending, Q, in the job's state on entry `rec₀`, in the input, the front, the coins and the
available tables. `old_KR_same` is at the values that the library writes out for the key file's test
on the ranges. Three theorems with their proofs; no definition.

In the list: a sending is a sub-protocol of the kind K1 (Johnson/Desc/K1/Own.lean). Its place P
(`K1.Par`, Johnson/Desc/K1/Send.lean) has its public numbers; `P.trees` lists the shapes of its
trees, and `logN` of a shape is the tree's log-length. A table (`Table`, the frame) has two numbers,
`logLength` and `words`, and a symbol at every natural number; `Table.col` writes the symbol at a
position as words. The sending's tables are `treeTables P V`
(Johnson/Desc/ProofFile/Honest/K1/Part.lean; K1/Part.lean below): a table for each tree of the
place, at a family of rows V, which gives a `Rows` (Johnson/Prover/Send/Core.lean) for each
message's number. A part (`Part`, the frame) is the prover's side of a stretch of a sub-protocol's
rounds. The sending's part is `sendPart` (K1/Part.lean): its first move, where it returns, sends
`treeTables` at the part's own rows. "T shows what T' shows" is `T.same T' = true`: the two tables
have the same `logLength`, the same `words`, and the same `Table.col` at every position below
2 ^ `T.logLength`. The available tables are a structure E (`Env`,
Johnson/Desc/ProofFile/Honest/Side.lean): `E.tree` gives, for a source, a place and a table, or
nothing; `E.sent` is how many trees the chain has sent so far. The source `own n` (`Fmt.TreeSource`,
Decl/Declared.lean) names tree number n of those that the chain sends. The table at hand is the
table T that `E.tree` gives for the source. A job (`TestJob`, Test.lean in this folder) is what a
caller supplies for its proximity test. w is the prover's input, fr a front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean: what the job's functions are given of the run before the
test), C a family of coins (`TestCoins`, Test.lean). Q (`OneSent`, JobOne.lean) is what is taken of
the sending: its place `P`; `ride`, which gives for a message's number the two numbers of a fold's
fresh table, or none; the caller's data `data`; the sender's address `addr`. The job's rows are
`Q.rows w (C.mem 0) Pst` (`OneSent.rows`, JobOne.lean), where Pst is the first stage's state
`(jobOne p Q rec₀).first w fr C`. The job's trees, T₀ below, are
`(jobOne p Q rec₀).trees₀ w fr C.mem Pst`: one tree, whose depth is `logN` of the place's tree
number 0 and whose column is `col Q.P` (Core.lean) of tree number 0 at the job's rows.
`OldAt E T₀ src₀` has two fields, each at every k below the length of T₀. `inFront`: if `src₀ k` is
`own n`, then n is below `E.sent`. `cols`: at every position x below 2 ^ depth of tree number k,
`colAt E.tree (src₀ k) x` is that tree's column at x. `colAt` (PlanOpens.lean in this folder) is the
column at x of the table for the source, and the empty list where there is no table.

For `old_KR_same`: the key file's test on the ranges is the proximity test at the place `piKRFull`
(Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean). `keyBook K` (E2E/KeyBook.lean) is the key file's
book of coins (`ProverCoinCounts`, the frame: public data that goes with a description). Coins (`Cs d`, the
frame) are elements of the base field and of the extension field, as many as the count d states
(`Due`). A cut (`Cs.cut`) is the n coins from number a on, in each field; it is `none` if they are
not all there. look gives the coins at an address (`Addr`, the frame). The sender is the part at
`Q.addr`, and its purse is `(look Q.addr).2`; the word does not mean the frame's type `Purse`. The
test's two parts are `firstPart` and `restPart` of the job (Parts.lean in this folder). c
(`RowCoins`, the frame) is what `lendRow` (the frame) returns for the list of the two, c.2.1 is what
the second part is given, and `restCoins` (Parts.lean) makes a `TestCoins` of it.

  `oldAt_of_same`: `old_of_table` with "the table at hand shows what the sending's table shows". In
    Lean, under the hypotheses below: `OldAt E T₀ src₀`, where src₀ is `own n` at number 0. The
    hypotheses are those of `old_of_table`, but for the table: the table at hand is T, the sending's
    table is T', and `T.same T' = true`
  `old_KR_same`: `old_KR` in that form. In Lean, under the hypotheses below: `OldAt E T₀ src₀` at
    the job `jobOne piKRFull Q rec₀`, with `restCoins` of c.2.1 for C, where src₀ is `own 1` at
    number 0
  `depth_treeTable`: the sending's table number 0 has the log-length of the place's tree number 0.
    In Lean: where T is entry number 0 of `treeTables P Vr`, `T.logLength` is
    `(P.trees.getD 0 {}).logN`. At every place P and every family of rows Vr

By what. `depth_treeTable` unfolds `treeTables`. `oldAt_of_same` follows the proof of `old_of_table`
and does not call it. The field `inFront` of `OldAt` is hn. For the field `cols`: `Table.same_elim`
(Johnson/Desc/ProofFile/Honest/Thread/ThrRow.lean) turns hs into `T.logLength = T'.logLength` and
`T.col x = T'.col x` at every x below 2 ^ `T.logLength`; by `depth_treeTable` the positions that
`cols` reads are below that bound; `colAt` is unfolded and rewritten by hE; `col_treeTable` at tree
number 0 and `sentCol_congr` (both TreesSentBeforeTestFromSentTable.lean) give the job's column. `old_KR_same` follows the
proof of `old_KR`, with `oldAt_of_same` in the place of `old_of_table`: hP is proved by
`planOwn_congr`, `sent_parKR` and `planOwn_KR`, and hV by `same_one` (SameAtOne.lean in this folder)
at `coinsTie_KR` (BookTiesAtKey.lean in this folder), `size_KR`, `ride_KR`, `noMain_KR` and
`room_KR`. The seven names without a file are in TreesSentBeforeTestAtKey.lean.

Hypotheses of `oldAt_of_same`. hP: `K1.planOkOwn Q.P` passes (Johnson/Desc/K1/Own.lean: a test on
the place's public numbers). hn: n is below `E.sent`: more than n trees are sent so far. hE:
`E.tree (own n)` is `some (pl, T)`; nothing reads the place pl. hs: `T.same T' = true`, with the
table at hand as the first argument, as in `Thread.handAt`. hT: T' is entry number 0 of
`treeTables Q.P V₁`. hV: `SameRows Q.P V₁ V' k` (TreesSentBeforeTestFromSentTable.lean), with V' the job's rows, at every k
below `Q.P.sent.size`.

Hypotheses of `old_KR_same`. hK: `fullPub` (E2E/KeyBookAtWritten.lean) is `some K`; K (`KeyPub`,
E2E/KeyBook.lean) is what the key file's book is made of. hc: the codes of `Q.P` are `keyFull.codes`
(`keyFull`: Johnson/Goal/PlanValues/KeySizedReturns.lean). hs: `Q.P.sent` is
`Wf.messageOf keyFull.ranges.x` (OnBytes/Iop/Wf.lean). hr: `Q.ride` is `rideKR`
(BookTiesAtKey.lean). ha: `Q.addr` is `sMsg` (E2E/KeyTestSizes.lean). h:
`lendRow (keyBook K) rows look piKRFull.place` at the list of the two parts, from part number 0 on,
returns c. hown: the cut of `(look Q.addr).2` at `⟨0, 0⟩` and the count `dueR Q.P Q.ride`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean; K1/Coins.lean below) is c₁. hn: 1 is below `E.sent`.
hE: `E.tree (own 1)` is `some (pl, T)`. hsame: `T.same T' = true`. hT: T' is entry number 0 of
`treeTables Q.P` at the rows `rowsR Q.P Q.ride (Q.data w) c₁` (`rowsR`: K1/Coins.lean).

Limits.
- That the table at hand shows what the sending's part's table shows, at the sender's purse cut at
  its start, is asked: a matter of the thread's tables and of the frame's play. In Lean these are
  hypotheses: hE, hs and hT in `oldAt_of_same`; hE, hsame, hT and hown in `old_KR_same`. They are
  proved at no value here.
- No thread and no play occurs in a statement of this file. T' is the sending's table: that a
  thread's own table (`Thread.tableAt`, Thr.lean) is T' is not stated. So `OldAt` is derived here
  from no thread's statement.
- That the two families of rows agree (hV) is a hypothesis of `oldAt_of_same`, and so is hP.
- h and hown are hypotheses of `old_KR_same`. hown has the form in which `lendPart` (the frame) cuts
  a part's own coins, but no part at `Q.addr` occurs in this file: that the frame gives the sender
  c₁, and that the part at that address takes the count `dueR Q.P Q.ride`, is not stated. hown is
  shown at no value here. `lends_KR` (MembersAtKey.lean in this folder) concludes h with
  `(keyBook K).rowsOf 0` for rows and `k.look 0` for look, under hypotheses of its own.
- `Q.data` is a function of the input only, while the data of a sending's job (`SendJob.data`,
  K1/Part.lean) are given a front too. That the rows at which `sendPart` makes its tables
  (`SendJob.rows`, K1/Part.lean) are the rows in hT of `old_KR_same` is not stated.
- The conclusion of `old_KR_same` is at the second part's `restCoins` only. Nothing is stated on
  what the first part is given.
- `rec₀` is a free parameter; nothing here shows that its values are the verifier's state.
- Both main theorems are stated at `jobOne` only: a job with one entry in `members` and one tree.
- `old_KR_same` is at written values, constants of the library: the place `piKRFull`, the codes and
  messages of `keyFull`, `rideKR`, `sMsg`, and the book `keyBook K` at the value of `fullPub`. This
  file compares none of them with a description of the key file.
- The option `maxRecDepth` is raised to 1000000 for the whole file; no proof in it calls `decide`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestAtKey
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Send (col shapeAt)
open ProofFile.Honest.K1 (rowsR dueR)
open H2K.Member (piKRFull)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (sMsg)

variable {V W X : Type}

/-- The sending's table number 0 has the log-length of the place's tree number 0. hT: T is entry
number 0 of `treeTables P Vr`. -/
theorem depth_treeTable (P : K1.Par) (Vr : ℕ → Johnson.Prover.Send.Rows) (T : Table)
    (hT : (K1.treeTables P Vr)[0]? = some T) : T.logLength = (P.trees.getD 0 {}).logN := by
  unfold K1.treeTables at hT
  rw [List.getElem?_map, List.getElem?_zipIdx] at hT
  cases ht : P.trees[0]? with
  | none =>
    rw [ht] at hT
    cases hT
  | some t =>
    rw [ht] at hT
    obtain rfl := Option.some.inj hT
    rw [List.getD_eq_getElem?_getD, ht]
    rfl

/-- **`OldAt` at the job made of a sending, from a table that shows the same.** n: the tree's number
among the chain's own. hE: the table at hand for the source `own n` is T. hs: `T.same T' = true`.
hT: T' is the sending's table of tree number 0 at the rows V₁. hV: V₁ and the job's rows agree at
every message of the place. hn: more than n trees are sent so far. hP: the place passes
`K1.planOkOwn`. -/
theorem oldAt_of_same (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (C : TestCoins) (E : Env) (n : ℕ) (V₁ : ℕ → Johnson.Prover.Send.Rows)
    (pl : VerifiableInference.Desc.Place)
    (T T' : Table) (hP : K1.planOkOwn Q.P = true) (hn : n < E.sent)
    (hE : E.tree (.own n) = some (pl, T)) (hs : T.same T' = true)
    (hT : (K1.treeTables Q.P V₁)[0]? = some T')
    (hV : ∀ k, k < Q.P.sent.size →
      SameRows Q.P V₁ (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) k) :
    OldAt E ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C))
      (fun k => [Fmt.TreeSource.own n].getD k (.own 0)) := by
  obtain ⟨hlen, hcol⟩ := Table.same_elim hs
  refine ⟨fun k hk m hm => ?_, fun k hk x hx => ?_⟩
  · have k0 : k = 0 := Nat.lt_one_iff.1 hk
    subst k0
    have e : Fmt.TreeSource.own n = .own m := hm
    injection e with e'
    exact e' ▸ hn
  · have k0 : k = 0 := Nat.lt_one_iff.1 hk
    subst k0
    have hx' : x < 2 ^ (Q.P.trees.getD 0 {}).logN := hx
    show colAt E.tree (.own n) x =
      col Q.P (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) 0 x
    unfold colAt
    rw [hE]
    show T.col x = _
    rw [hcol x (by rw [hlen, depth_treeTable Q.P V₁ T' hT]; exact hx'),
      col_treeTable Q.P V₁ hP 0 x T' hT, sentCol_congr Q.P _ _ 0 x hV]

/-- **At the key file's test on the ranges.** `old_KR` (TreesSentBeforeTestAtKey.lean in this folder) with two
tables: T is the table at hand for the source `own 1` (hE), T' is the sending's table of tree number
0 at the rows `rowsR Q.P Q.ride (Q.data w) c₁` (hT), and `T.same T' = true` (hsame). The other
hypotheses are those of `old_KR`. -/
theorem old_KR_same (K : KeyPub) (hK : fullPub = some K) (Q : OneSent W)
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
    (pl : VerifiableInference.Desc.Place) (T T' : Table) (hn : 1 < E.sent)
    (hE : E.tree (.own 1) = some (pl, T)) (hsame : T.same T' = true)
    (hT : (K1.treeTables Q.P (rowsR Q.P Q.ride (Q.data w) c₁))[0]? = some T') :
    OldAt E
      ((jobOne piKRFull Q rec₀).trees₀ w fr (restCoins (jobOne piKRFull Q rec₀) c.2.1).mem
        ((jobOne piKRFull Q rec₀).first w fr (restCoins (jobOne piKRFull Q rec₀) c.2.1)))
      (fun k => [Fmt.TreeSource.own 1].getD k (.own 0)) := by
  have hP : K1.planOkOwn Q.P = true :=
    (planOwn_congr Q.P parKR hc (hs.trans sent_parKR.symm)).trans planOwn_KR
  refine oldAt_of_same piKRFull Q rec₀ w fr _ E 1 _ pl T T' hP hn hE hsame hT
    (same_one piKRFull Q rec₀ w fr _ c₁
      (coinsTie_KR K hK Q hc hs hr ha rec₀ w rows look c h c₁ hown) (by rw [hs]; exact size_KR)
      (by rw [hr]; exact ride_KR) ?_ room_KR)
  unfold shapeAt
  rw [hs]
  exact noMain_KR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.depth_treeTable
#print axioms ProofFile.Honest.K12.oldAt_of_same
#print axioms ProofFile.Honest.K12.old_KR_same
