-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Defs.lean: the front page of the folder Johnson/SendSim/, and a general model of a
step in which a prover sends encoded rows and answers linear queries on them.
Terms: "Words of this page" and "Terms of the model" below; in full, "Terms" in At/Sim.lean and in
Seat/AtDescLots.lean, and "Terms of the book" in At/Fresh.lean. Paths in this head are relative to
Johnson/SendSim/ unless they begin with Johnson/.

What the folder is about. In a sending the prover sends new tables as oracle messages, the verifier
samples out-of-domain (OOD) seeds, and the prover then sends its answers to the OOD samples in the
clear. Later sub-protocols query the tables at some positions. A sub-protocol of the kind K1 is one
sending and nothing else. Two other kinds send tables too, K2 (a code switch) and K12 (a proximity
test); this folder does not cover them. The library defines the honest prover's algorithm for a
sending in Lean: the honest sender, sendPart. This folder defines a simulator for it, sendSim, and
proves, under public premises, two equations between distributions, which the library's framework
for honest provers calls exact and fresh (fields of its structure Good). They are meant as steps
toward index privacy. No property of the protocol is claimed here: not hiding, not zero knowledge.

Words of this page.
  table         an oracle message: rows, each encoded by a code together with a tail of random
                entries.
  coin          a uniformly random field element that the honest prover samples.
  job, data     A job is what the sender is given: the public parameters of its place, which table
                is sent along for a later step (ride), and the data, the entries of the rows that
                are not coins.
  description   the protocol behind one of the prover's files (key file, a copy's file, proof file)
                as a Lean value: three chains of sub-protocols, each at its place. The maker
                (ProofFile.onlineDescription) computes the proof file's description from three public files.
  gate, scope   The gate is FlashProve.protocolDataWellFormed, a test on the three public files that is part of the
                library's verifier: the three makers of the verifier's description (the plan's, the
                key file's, the proof file's) succeed, and their data fit the verifier's frame. That
                it accepts is no sign that the verifier accepts any proof. The goals' scope is
                VerifierAndGoals.InScope, another test on the public files: the library's reader accepts them;
                the layout file is the stored full-size one; the parameter file is the stored one
                but for eight numbers, with 2^8 ≤ theta; the scale file is free.
  side, Seated  A side is a sub-protocol of a description with the honest part and its simulator. It
                is Seated if these are sendPart and sendSim at one job, the sub-protocol has two
                rounds that agree with a sending's in what the framework's function play reads of
                them, and every list of challenges that these rounds can sample consists of exactly
                the seeds, with no factor 0. That they can sample one is not part of Seated
                (At/Sim.lean, Limits).
  state, front  where an execution is before the sender's rounds, with the prover's input; and what
                a simulator is given of it.
  book          a public table that says which later parts of the honest prover are given which of a
                part's coins, to mask a value with (they spend them) or to compute on (they carry
                them).

The results. The equations are equalities: there is no error term. They hold for all parameters that
satisfy the stated premises; where each premise is proved for the proof file's description is in the
table after the results.
  (1) exact. The sender discloses the columns of its tables at the queried positions, and its
      answers. rowsExact: for all public parameters, challenges and queried positions, if the job
      fits its place (sendFits), the challenge consists of exactly the seeds (seedsFit), no seed's
      factor is 0, and the positions are within the bound (budAt: of each oracle message at most r
      distinct positions modulo the code's length, for the main code and for the mask code, each
      with the length r of its rows' tails), then the distribution of what the sender discloses,
      over uniform coins, is the same for any two data. sendExactAt: at every Seated side ExactAt
      holds with the bound budAt (ExactAt: the field exact of Good without its premise on the opened
      columns; At/Sim.lean). That is, at every state, for all challenges that the side's
      rounds can sample, all positions within the bound, and every front that agrees with the state
      and has every column that the rounds read, what the sender discloses has the distribution of
      the output of sendSim. (ExactAt's premise "no abort" always holds: the sender never aborts.)
      At a side the data are what the job computes from the prover's input and the earlier state.
      sendSim runs the sender's own two rounds on a job without data, on coins of its own, and reads
      neither the input nor the front.
  (2) fresh. rowsFresh: under the four premises of rowsExact, if also the entries of the book that
      concern one later part are within the sender's number of coins (WithinAt) and that part is
      clear (SpenderClear: a condition on which coins it may spend, and on which coins it and
      earlier parts are not given), then the coins that it spends are uniform, and independent of
      what the sender discloses together with the sender's other coins that it or an earlier part is
      given. rowsFreshAny: the same where that part spends the coefficients of a table of any number
      of rows that is sent along, if no spent coin and no tail coin of the table is known.
      sendFreshAtWide: at every Seated side, if the book is clear at the sender (BookClearAny), the
      field fresh holds with the bound budAt.
  (3) At the descriptions. Wherever the maker succeeds, at every job of the lists lotJobs and wJobs
      the proof file's first chain has a sub-protocol at the job's place, and the side there is
      Seated (stands_at_job, seatedAt_job). fieldsAtLots: that side has the field fits and ExactAt,
      and the field fresh if the book is clear (BookClearAny). The two lists hold the honest
      sender's jobs at places of the kind K1 on that chain: those of K1's own lot, and the request's
      own table. The statements are for all data and for every way to read the input.
      How many: for public files in the goals' scope, at the format's second hash function
      OnBytes.secondHashFunction, at which the library's verifier makes its description (pseat_name,
      Johnson/Goal/Description/ProofSeat.lean), they are 52 jobs (jobs_52_in_scope), at different
      places (jobPlaces_nodup).
      Fit: if the description also passes its tests on the plan, each of these jobs fits its place
      (fits_at_lots_plan).
      Key file: the same holds (Seated; fits and exact; fresh if BookClearAny holds) at the two or
      three sub-protocols (two where the shape has no message for W) of the kind K1 in the first
      chain of the term Key.descriptionFromSource, a key file's description (seatedAt_key, fieldsAtKey_all;
      fits_at_key). In the goals' scope, where the gate accepts, the key file's maker returns such a
      term, at OnBytes.secondHashFunction and at a constant in the place of the public files' digest
      (Key.fixedDigest), as the library's verifier runs it; the term passes its tests on the plan,
      and the three jobs fit (keyAt_of_live, Seat/KeyReadsAtLive.lean). Among the files that this
      folder imports there is no honest prover of a key file in the framework of
      Johnson/Desc/ProofFile/Honest/ (parts at the description's places): the three jobs are tied to
      the description's numbers alone.
      exact is not to be quoted without fresh.
  (4) In general. Both equations are first proved in the model of this file, for every finite field
      (sendExact, sendFresh). At/Bridge.lean makes the honest sender an instance of the model.
  (5) Two senders. No statement of this folder says that the runs of two senders together are
      uniform (At/Fresh.lean, Limits).
  (6) Tests. At small examples an equation is false where a premise is violated or the sender is
      modified (said here without a theorem). Lines under #guard: At/SmallPlaces.lean,
      At/SmallPlaceBase.lean, At/FilledBooks.lean; a #guard leaves no theorem.

The premises of results (1) to (3), and where each is proved for the proof file's description. For
the key file's three places see Seat/AtKey.lean and Seat/KeyReadsAtLive.lean. Every row that names
the gate is at the format's second hash function OnBytes.secondHashFunction alone, at which the gate is defined
and the library's verifier makes its description; the first paragraph of result (3) and "Fit" hold
at every hash function at which the maker succeeds.
  Seated                proved at the places of result (3), wherever the maker succeeds. It includes
                        seedsFit and "no factor is 0".
  the maker succeeds    proved at all public files at which the gate accepts (returns_of_live,
                        Seat/AtDesc.lean). This unfolds the gate's definition.
  sendFits              proved wherever the maker succeeds and the description passes its tests on
                        the plan (fits_at_lots_plan). It passes them where the gate accepts
                        (plan_of_live, Seat/ReadsAtLive.lean).
  budAt                 proved for the 52 jobs at all public files in the goals' scope at which the
                        gate accepts. There a public test on queried positions accepts at all 52
                        jobs (reads_of_live, Seat/ReadsAtLive.lean). From that, and from the fact
                        that no two sub-protocols of the first chain are at one place (one of the
                        tests on the plan), the positions that the description's rounds read of
                        these senders' trees meet budAt at every due list of challenges
                        (bud_of_live; "due": Seat/Bud.lean; that a verifier's challenges are due is
                        not proved). The test is checked at the library's written full-size values
                        by evaluation in Lean's kernel, with negative tests (readsW,
                        Seat/ReadsAtWritten.lean). It has no slack where that was tried. The count
                        is of one execution: one proof of one request.
  in scope, and the gate accepts
                        proved at the stored full-size public files VerifierAndGoals.storedPublicFiles, at the same files
                        under another named policy, and under every policy within four bounds. That
                        they are in scope is proved in the main library (VerifierAndGoals.inScope_full,
                        inScope_gap, inScope_zAt). That the gate accepts is proved in a side library
                        that the main library does not import (theLive_zFull,
                        AtFullSide/Top/LiveAtFull.lean; theLive_zGap and theLive_zAt,
                        AtFullSide/Top/LiveAtPolicies.lean). Many closed facts beneath these proofs
                        are by evaluation in Lean's kernel, and no independent checker has replayed
                        them. Nothing in Lean checks that the stored terms are the bytes of real
                        public files, and the makers are run at a constant in the place of the
                        public files' digest.
  the book is clear     BookClearAny at the senders of result (3) (it implies SpendersClearAny
                        there: spendersAny_of_clearAny, Seat/AtDescLotsSpenders.lean): proved in
                        this folder at no book of the release. Elsewhere, in scope, where the gate
                        accepts and the maker onlineProverFromPublicFiles returns, at the book that the maker returns and
                        at the returned description's own order of places: BookClearAny at the
                        opening's sender (`clear_at_opening`, AtFullSide/K1/BookAtOpening.lean);
                        SpendersClearAny at each of the 52 jobs (`clear_all`,
                        AtFullSide/K1/GoodAtReturn.lean; content at 2 of the 52: "What is covered").
                        At the key file's book, where `fullPub` returns it, at its three senders: at
                        the written numbers and the written order of places, `key_clear`
                        (AtFullSide/K1/KeyBookClear.lean); at the key file's own numbers, under
                        `OneFull` besides: `index_clear`, `multiplicities_clear`, `messageW_clear`
                        (E2E/OfflineFirstSends.lean). Each rests on an evaluation in Lean's kernel
                        (lists_ok; key_fast; the three lines of E2E/OfflineClearLines.lean). With a
                        coin spent it is proved in this folder at one made-up book
                        (guardTried_filled with ownerOkB_iff, At/GuardTestTie.lean).
                        At/FastBook.lean has a public test that walks a book's entries a few times
                        and implies the premise (clearAny_of_fast). What has been checked by running
                        a test is in the Limits of Seat/AtDescLots.lean.

What is covered. The counts are over the list of full-size sendings under the entry "SEND seed"
(Johnson/G/SendsLit.lean), by inspection, not proved. A table that is sent under another entry is
not in that list, so the totals are lower bounds.
  - The first chain of the proof file has at least 82 sendings. Result (3) covers 52 of them. That
    these are all places of the kind K1 on the chain is by inspection, not proved. The other 30 (25
    of the kind K2, 5 inside K12) are not covered.
  - fresh has content at 2 of the 52. Only these two have a mask row or a table that is sent along,
    and so coins that a later part can spend while the book is clear. The chain's other 30 sendings
    with a mask row are the 30 that are not covered.
  - Over all files K1 has 60 of the 119 sendings. Result (3) covers 55: the 52, and 3 of the 5 in a
    key file. The other 5 are not covered. (Seat/AtDescLots.lean counts for fieldsAtLots alone: 52,
    and 8 not covered.)

Limits of the folder.
  - No property is claimed: not hiding, not zero knowledge. Nothing in this folder derives index
    privacy (Johnson/WholeKey/Statement.lean) from these theorems, and none of them is one of the
    release's goal statements. Between them and index privacy are, among other things: the premise
    on the book (where it is proved: "the book is clear", above); that the gate accepts, at public
    files other than the stored ones; the sendings and the kinds of sub-protocol that are not
    covered; an honest prover of a whole chain that takes these senders (none is among the files
    that this folder imports, for the proof file or for a key file); what else the framework's rule
    requires at each sub-protocol (that each part can be run, what is passed on, that the verifier
    accepts); the committer's randomness, which is data here, never a coin; batches; the composition
    over a whole execution; and hashing. On the composition: the rule that takes exact and fresh
    from each row (file_owed_rows) concludes a structure of further premises, Owed. From Owed and
    more premises the framework derives the two equations again for each part inside one execution
    (cells₁, Johnson/Desc/ProofFile/Honest/Law/Rule/FileCells.lean). Nothing in this folder speaks
    of the view of a whole execution.
  - The sender and its simulator are general in the job. At the descriptions of the release's files
    only the sides at the places of result (3) are proved Seated.
  - The honest sender is a definition in Lean. No theorem connects it with a program.
  - Nothing is hashed: the tables are oracle messages, and what is disclosed holds no root, no
    nonce, no salt and no proof of work. So exact and fresh say nothing about the hashed proof.
    Challenges and queried positions are fixed in advance.
  - In rowsExact, rowsFresh and result (3) the data are a free variable. No theorem connects them
    with the model's weights.
  - The premises of results (1) to (3) are public conditions on parameters, challenges, positions
    and the book; ExactAt has three more, on the state and the front (m.seen = front.seen;
    front.holds; no abort by hid), which its proof does not use (exactOut, At/ExactAt.lean); the
    field exact of Good has a fourth, on the opened columns. Where a premise fails, a statement
    holds vacuously. Where a job
    does not fit its place, what is disclosed is the error value on both sides: exact then says
    nothing, and fresh speaks of the sender's coins alone.
  - exact is never to be quoted without fresh (At/ExactAt.lean says why).
  - Each statement speaks of one owner of coins and one spender.
  - A small example says nothing about the release's parameters.

Where things are. (1): At/Sim.lean (statements), At/RowsExact.lean, At/ExactAt.lean. (2):
At/Fresh.lean, At/CutTie.lean, At/FoldAny.lean and At/BookWide.lean (statements), At/RowsFresh.lean,
At/FreshWideProofs.lean, Seat/HandedWideProofs.lean. (3): Seat/AtDescStands.lean,
Seat/AtDescLots.lean (statement), Seat/AtDescLotsProof.lean, Seat/LotCount.lean,
Seat/LotPlaces.lean, Seat/RideFitsW.lean, Seat/ReadsAtLive.lean, Seat/AtKeyStands.lean,
Seat/AtKey.lean, Seat/FitsAtKey.lean, Seat/KeyReadsAtLive.lean. (4): CoreProofs.lean. (5):
At/Fresh.lean, Limits. (6): At/SmallPlaces.lean, At/SmallPlaceBase.lean, At/FilledBooks.lean. The
sender: Johnson/Desc/ProofFile/Honest/K1/Part.lean. Good: Johnson/Desc/ProofFile/Honest/Side.lean.
Reading order. This file; CoreProofs.lean; At/Sim.lean; At/Fresh.lean; At/Bridge.lean;
At/RowsExact.lean, At/RowsFresh.lean, At/FreshWideProofs.lean; At/ExactAt.lean,
At/FreshAtMember.lean, Seat/HandedWideProofs.lean; Seat/AtDescLots.lean.
The sub-folders.
  (root)  the model, its two theorems, pads (Pads.lean), general lemmas (Apart.lean).
  Tie/    lemmas that connect the library's codes, fields and sample rows with the model's symbols
          and linear forms.
  At/     the honest sender: the statements, the passage to the model, the proofs, executable tests
          on a book, and small example places and books (terms: At/SmallPlaces.lean).
  Seat/   the sender with its simulator as a row of the framework's rule, and at the descriptions.

What this file has. Definitions only: the model, and two named propositions. Both are proved under
the same names, without "Spec.", in CoreProofs.lean.
  Spec.sendExact  For every finite field K, every sender S of the model, all coefficients w of the
                  answers, every list of queries and any two data: if the list is within the bound
                  (Within) and Mends holds, then the distribution of what is disclosed (shown), over
                  uniform coins, is the same for both data.
  Spec.sendFresh  For every K, S, w, list of queries and data, and all sets U, Kn of message coins
                  and KnT of tail coins: if the list is within the bound and MendsOff holds, then
                  over uniform coins the tuple (the coins in U, what is disclosed, the coins in Kn,
                  the coins in KnT) has the distribution in which the coins in U are replaced by
                  fresh uniform values, independent of the rest.

Limits of these two statements.
  - Nothing in this file speaks of a protocol of the release: the two statements compare
    distributions in an abstract model. That the honest sender is an instance (At/Bridge.lean), and
    that the model's premises follow from the public premises of rowsExact and rowsFresh, is proved
    in At/.
  - Both hold vacuously where a premise fails: at a list beyond the bound, and at coefficients at
    which Mends or MendsOff is false.
  - There is one field. Rows over a field with answers in an extension of it are an instance only
    when each element of the extension is read as its coordinates over the smaller field
    (At/Bridge.lean does so).
  - MendsOff requires that the adjusting family leaves unchanged the message of every row that has
    even one tail coin in KnT. Where fewer points are queried than the tail has coins outside KnT,
    the conclusion can hold without that; no weaker premise is stated.

Terms of the model.
  row, symbol     A row has a message of l entries and a tail of r entries, all in K. Its symbol at
                  a point p is the value at p of the polynomial whose lowest r coefficients are the
                  tail and whose next l coefficients are the message (sym,
                  Johnson/LinkSim/Tail.lean).
  coin            Sender.Coins has two sorts: the message coins, named by Cn, and the entries of
                  each row's tail.
  data, lay       A row's message is the sum of the data, a free variable, and of the message coins'
                  contribution lay c (msg). lay may be any map.
  answer          a linear form, with public coefficients w, in the entries of all rows' messages
                  (ansAt). It reads no tail.
  pad             a message coin of an answer's own: its contribution to that answer is a factor
                  other than 0 times the coin, and 0 to every other answer (Pads, Pads.lean).
  discloses       shown: the symbols at a list of queries (row, point), in the list's order, and all
                  answers.

The other names.
  Sender K        the public shape: the rows with r and l, the names of the message coins, lay, and
                  the names of the answers.
  tl              a tail as a function on all natural numbers, 0 from r on.
  msg, symAt, form, ansAt  a row's message; its symbol at a point; a linear form; an answer.
  ptsOf, Within   the points that a list queries of a row; the bound on queries: of each row at most
                  r distinct points. Points are counted, not places in the list.
  Additive, AddsAt  lay is additive; lay is additive at one family s of message coins: adding s to
                    any coins adds lay s.
  wt              the contribution of message coins to an answer.
  Mends           for any values of the answers there is a family s, at which lay is additive, whose
                  contribution to the answers has these values.
  MendsOff        any change of the coins in U extends to a family s, at which lay is additive, that
                  is 0 on Kn, contributes 0 to every answer, and contributes 0 to the message of
                  every row that has a tail coin in KnT.
  cut, cutT       the message coins in a set; the tail coins in a set.

Sources. The two statements follow a written argument of this project, which is not in the
repository, for one sending with its OOD answers: run the same algorithm on the data 0; pads adjust
the answers, then tails adjust the symbols. They differ from it in seven points.
  (1) Any two data are compared, not data against 0. The case data' := 0 is the written argument's.
  (2) The step on the pads is a premise here (Mends, MendsOff). That pads with factors other than 0
      give Mends, and MendsOff if U, Kn and KnT satisfy Clear, in both cases for an additive lay, is
      proved in Pads.lean (mends_of_pads, mendsOff_of_clear).
  (3) What is known of the sender's other coins is two sets of coins (Kn, KnT), not entries of a
      book.
  (4) The list of queries holds points, not positions. Which position has which point is the
      caller's.
  (5) There is one field.
  (6) lay is any map. A coin need not have an entry of its own, and additivity is required at the
      adjusting families alone. The contribution of the other coins (a table that is made of fewer
      coins than it has entries) may be any function of them.
  (7) Data may be present at an entry to which a coin contributes too, since a message is the sum of
      the two. "Any two data" ranges over such data as well. A sender whose entry is a coin,
      whatever the data say, is the case of data that are 0 at that entry.
-/
import Johnson.LinkSim.Tail
import Prob.Linear

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim
open Prob OnBytes.LinkSim

/-- The public shape of a sender in the model: its rows with their lengths, the names of its message
coins and how they enter the messages, and the names of its answers. -/
structure Sender (K : Type) where
  /-- the names of the rows -/
  Row : Type
  [finRow : Fintype Row]
  [decRow : DecidableEq Row]
  /-- the length of a row's tail (r) and of its message (l) -/
  r : Row → ℕ
  l : Row → ℕ
  /-- the names of the message coins: the coins that enter messages -/
  Cn : Type
  [finCn : Fintype Cn]
  [decCn : DecidableEq Cn]
  /-- the message coins' contribution to the messages, by row and entry -/
  lay : (Cn → K) → Row → ℕ → K
  /-- the names of the answers -/
  Ans : Type
  [finAns : Fintype Ans]
  [decAns : DecidableEq Ans]

attribute [instance] Sender.finRow Sender.decRow Sender.finCn Sender.decCn Sender.finAns
  Sender.decAns

variable {K : Type} [Field K]

/-- The sender's coins: a value for each message coin, and the entries of each row's tail. -/
abbrev Sender.Coins (S : Sender K) : Type := (S.Cn → K) × ((ρ : S.Row) → Fin (S.r ρ) → K)

/-- The name of a tail coin: a row, and an index into its tail. -/
abbrev Sender.TailCoin (S : Sender K) : Type := (ρ : S.Row) × Fin (S.r ρ)

/-- A tail as a function on all natural numbers: 0 from r on. -/
def tl {r : ℕ} (t : Fin r → K) (q : ℕ) : K := if h : q < r then t ⟨q, h⟩ else 0

namespace Sender
variable (S : Sender K)

/-- A row's message: the data plus the message coins' contribution. -/
def msg (data : S.Row → ℕ → K) (c : S.Coins) (ρ : S.Row) : ℕ → K := data ρ + S.lay c.1 ρ

/-- The symbol of the row a.1 at the point a.2: the value there of the polynomial whose lowest
coefficients are the row's tail, followed by its message. -/
def symAt (data : S.Row → ℕ → K) (c : S.Coins) (a : S.Row × K) : K :=
  sym (S.r a.1) (S.l a.1) a.2 (S.msg data c a.1) (tl (c.2 a.1))

/-- The linear form with weights w in the entries of all rows' messages m. -/
def form (w : S.Row → ℕ → K) (m : S.Row → ℕ → K) : K :=
  ∑ ρ, ∑ j ∈ Finset.range (S.l ρ), w ρ j * m ρ j

/-- The answer i: the linear form with the weights w i in the rows' messages. It reads no tail. -/
def ansAt (w : S.Ans → S.Row → ℕ → K) (data : S.Row → ℕ → K) (c : S.Coins) (i : S.Ans) : K :=
  S.form (w i) (S.msg data c)

/-- What the sender discloses: the symbols at a list of queries (row, point), in the list's order,
and all answers. -/
def shown (w : S.Ans → S.Row → ℕ → K) (asks : List (S.Row × K)) (data : S.Row → ℕ → K)
    (c : S.Coins) : List K × (S.Ans → K) :=
  (asks.map (S.symAt data c), S.ansAt w data c)

/-- The set of points at which a list queries the row ρ. -/
def ptsOf [DecidableEq K] (asks : List (S.Row × K)) (ρ : S.Row) : Finset K :=
  ((asks.filter fun a => decide (a.1 = ρ)).map (·.2)).toFinset

/-- The bound on queries: the list queries each row at no more distinct points than the row's tail
has entries. -/
def Within [DecidableEq K] (asks : List (S.Row × K)) : Prop :=
  ∀ ρ, (S.ptsOf asks ρ).card ≤ S.r ρ

/-- lay is additive. -/
def Additive : Prop := ∀ a b : S.Cn → K, S.lay (a + b) = S.lay a + S.lay b

/-- The contribution of the message coins s to the answer i. -/
def wt (w : S.Ans → S.Row → ℕ → K) (s : S.Cn → K) (i : S.Ans) : K := S.form (w i) (S.lay s)

/-- lay is additive at the family s: adding s to any message coins adds lay s. -/
def AddsAt (s : S.Cn → K) : Prop := ∀ a : S.Cn → K, S.lay (a + s) = S.lay a + S.lay s

/-- For any values v of the answers there is a family s of message coins, at which lay is additive,
whose contribution to the answers is v. -/
def Mends (w : S.Ans → S.Row → ℕ → K) : Prop :=
  ∀ v : S.Ans → K, ∃ s : S.Cn → K, S.AddsAt s ∧ S.wt w s = v

/-- Any change δ of the coins in U extends to a family s of message coins, at which lay is additive,
that is 0 on Kn, contributes 0 to every answer, and contributes 0 to the message of every row that
has a tail coin in KnT. -/
def MendsOff (w : S.Ans → S.Row → ℕ → K) (U Kn : Finset S.Cn) (KnT : Finset S.TailCoin) : Prop :=
  ∀ δ : U → K, ∃ s : S.Cn → K, S.AddsAt s ∧ (∀ u : U, s u = δ u) ∧ (∀ k ∈ Kn, s k = 0) ∧
    S.wt w s = 0 ∧ ∀ x ∈ KnT, ∀ j < S.l x.1, S.lay s x.1 j = 0

/-- The values of the message coins in the set U. -/
def cut (U : Finset S.Cn) (c : S.Coins) : U → K := fun u => c.1 u

/-- The values of the tail coins in the set KnT. -/
def cutT (KnT : Finset S.TailCoin) (c : S.Coins) : KnT → K := fun x => c.2 x.1.1 x.1.2

end Sender

/-- If the queries are within the bound and Mends holds, then the distribution of what the sender
discloses, over uniform coins, is the same for any two data. Statement only; proved as sendExact in
Johnson/SendSim/CoreProofs.lean. -/
def Spec.sendExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (S : Sender K)
    (w : S.Ans → S.Row → ℕ → K) (asks : List (S.Row × K)) (data data' : S.Row → ℕ → K),
    S.Within asks → S.Mends w →
    (unif S.Coins).map (S.shown w asks data) = (unif S.Coins).map (S.shown w asks data')

/-- If the queries are within the bound and MendsOff holds, then over uniform coins the coins in U
are uniform and independent of what the sender discloses together with the coins in Kn and KnT.
Statement only; proved as sendFresh in Johnson/SendSim/CoreProofs.lean. -/
def Spec.sendFresh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (S : Sender K)
    (w : S.Ans → S.Row → ℕ → K) (asks : List (S.Row × K)) (data : S.Row → ℕ → K)
    (U Kn : Finset S.Cn) (KnT : Finset S.TailCoin),
    S.Within asks → S.MendsOff w U Kn KnT →
    (unif S.Coins).map (fun c => (S.cut U c, S.shown w asks data c, S.cut Kn c, S.cutT KnT c)) =
      (unif ((U → K) × S.Coins)).map fun a =>
        (a.1, S.shown w asks data a.2, S.cut Kn a.2, S.cutT KnT a.2)

end OnBytes.SendSim

#print axioms OnBytes.SendSim.Sender
#print axioms OnBytes.SendSim.Sender.Coins
#print axioms OnBytes.SendSim.Sender.TailCoin
#print axioms OnBytes.SendSim.tl
#print axioms OnBytes.SendSim.Sender.msg
#print axioms OnBytes.SendSim.Sender.symAt
#print axioms OnBytes.SendSim.Sender.form
#print axioms OnBytes.SendSim.Sender.ansAt
#print axioms OnBytes.SendSim.Sender.shown
#print axioms OnBytes.SendSim.Sender.ptsOf
#print axioms OnBytes.SendSim.Sender.Within
#print axioms OnBytes.SendSim.Sender.Additive
#print axioms OnBytes.SendSim.Sender.wt
#print axioms OnBytes.SendSim.Sender.AddsAt
#print axioms OnBytes.SendSim.Sender.Mends
#print axioms OnBytes.SendSim.Sender.MendsOff
#print axioms OnBytes.SendSim.Sender.cut
#print axioms OnBytes.SendSim.Sender.cutT
#print axioms OnBytes.SendSim.Spec.sendExact
#print axioms OnBytes.SendSim.Spec.sendFresh
