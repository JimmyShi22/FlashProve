-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/DefaultsIdle.lean: kind K14: the definitions of the kind's six
halves in the shared chain (the kind's own four and the two sendings') meet many cases "in silence":
by a default value, a shorter list or a truncated subtraction, with no error. This file lists these
cases, sorts them by what they hang on, and gathers under two names the sentences that bar those
listed under A (in part by a reading, as the list says at (5), (7) and (9)). Two structures of
sentences; statements with their proofs, most of them calls.

A. CASES THAT HANG ON PUBLIC DATA, WITH A SENTENCE HERE. Files: Honest/K14/Sendings.lean,
Honest/K14/Parts.lean, Honest/ForKinds.lean.
  (1) (withU S).getD #[]: "send o_u" as a sending of no message (jobU): PublicIdle.withU; and the
      library's arm that makes the list empty where no mask is sent ahead: PublicIdle.ahead
  (2) jobU's arm for a test on G_u without a stage: PublicIdle.stage
  (3) halves' arm for a shape that does not split (three halves, none at "SPLIT"), and the like arm
      in the list of "send o_omega"'s messages: PublicIdle.splits
  (4) trees that cannot be laid: the empty layout (columnOf, sentTables): SendIdle.trees; a message
      that lies in no tree, whose rows columnOf would leave out: SendIdle.trees' second clause
  (5) a code's number beyond its array: the default code (dueOf, laid, columnOf): SendIdle.base,
      SendIdle.mask, at each message that has rows of that sort. At a message WITHOUT rows of a sort
      the default code may still be evaluated; it is then multiplied by 0 rows or read by nobody: so
      by reading, with no sentence here
  (6) a coin beyond the part's count: 0 (SendJob.rows): SendIdle.fillers: the tables and the answers
      are the same whatever stands in for a coin beyond the count (sent_within_coins,
      Honest/K14/SendingsWithin.lean). SendIdle.count (each message's coins lie within the count)
      holds at every job and by itself says nothing on what laid asks for
  (7) laid's subtractions on natural numbers, which truncate at 0: c.ell - s.answers at a plain
      message; l - 1, t - 1 and k - 1 at a fold's fresh table. Where they truncate, one coin stands
      at two places or a counted coin is laid nowhere, AND (6) DOES NOT COVER THAT:
      SendIdle.plain, SendIdle.fresh (its first two clauses bar k - 1; that l and t start at 1 is
      freshRow_reads, Honest/K14/SendingsWithin.lean). A fresh table's row has 2 k - h + 1
      coefficients and the encoder reads a row's first places up to the mask code's message length:
      a shorter code would drop the last coefficients in silence: SendIdle.fresh's third clause
  (8) a seed beyond the list: the default seed (answersOf): the part hands answersOf a list of just
      Q.seeds seeds, at every challenge, and no message has more answers: SendIdle.seeds (like
      count it holds at every job)
  (9) a vector that does not fit its main rows is cut, and where the matrix's places reach into the
      pads an entry of the matrix is laid for a pad (rowsOf; the vectors' own texts,
      Johnson/Desc/K14/Honest/Coded.lean): barred by the library's test on the linear part's shape
      and codes: PublicIdle.lin. THAT THE TEST BARS BOTH IS A READING OF ITS TEXT, NO THEOREM HERE

B. CASES THAT HANG ON PUBLIC DATA, SHOWN IN THE FILES NAMED.
  (10) a word beyond a column's length: 0 (sentTables): a column's length hangs on the codes and the
      shapes alone (length_columnOf, Honest/K12/TableIsColumn.lean); that it is the tree's width is
      a public test there (widthFits), shown at the full size at tree 0 of "send o_u" and tree 1 of
      "send o_omega" alone (width_head)
  (11) the scalar at "SPLIT": scalarsPart pads with 0 or cuts, and adds lists of unlike lengths in
      silence: the part's one move returns one element (says_split, Honest/K14/PartsFit.lean), and
      the coin in it is the coin that it is handed, never a placeholder (coin_there, scalarAt_coin,
      Honest/K14/PartsCoin.lean)
  (12) sixOf's and nowSharedBy's errors, at which widerFillOwn (Honest/AtPureWiderAt.lean) lays no
      half at all: under the hypothesis at the full size both return (six_at_head,
      Honest/K14/SendingsAtFilling.lean; nowSharedBy_at_head, Honest/K14/AtWiderShared.lean)
  (13) a message's number beyond the sending: the default shape: offsetOf, columnOf and answersOf
      run over the numbers below the sending's size, and an answer's value sums over these: so by
      their texts

C. CASES THAT HANG ON A RUN: NO SENTENCE HERE; each named so that it can be asked for.
  * THE POINT IS HEARD, WHOLE. splitValue, jobU and jobOmega read challenges by heardFrom
    (Honest/ForKinds.lean), which returns a shorter list where fewer have been heard; and the
    vectors' texts take and drop elements of the point, so that a point of too few elements gives
    other weights in silence. What would bar it, and this file does not show it: that at each of
    these parts' rounds the challenge of "LIN point"
    (at "SPLIT" that of "LIN zeta" too) has been heard and holds as many elements as the shape
    counts. Lemmas that bear on it: heardFrom_member, heardFrom_more (Honest/Thread/HeardLaw.lean).
  * THE SEEDS ARE WHOLE. K1.cutSeeds cuts the seeds off the elements of the last challenge
    (State.lately); where these are too few a seed's point is shorter and its factor is 0. Under the
    test on the challenges' form neither happens: draws_send (Johnson/SendSim/At/SeatedAt.lean).

D. ZEROS THAT ARE NO DEFAULT OF AN ERROR. They are sent or committed as they stand. The definitions'
own heads call them placeholders; neither this file nor any file that it imports has a statement
that holds them against the format's pages.
  * AT REAL PLACES OF A MASK ROW: a fold's fresh table (the first mask, sent with o_u) holds the
    coefficients of the hiding polynomial and 0 at its other places (laid's arm for a fresh table;
    Fmt.M1.FoldOwn.freshRow, Fmt/M1Fold.lean). spot_zero (Honest/K14/SendingsReach.lean) proves a 0
    there; no theorem of that file or of this one says at which places
  * the free places of a main row: the vectors' own texts return 0 beyond their entries
    (Johnson/Desc/K14/Honest/Coded.lean)
  * wordsOf's 0 at the rows beyond the real ones, which an answer reads wherever the number of rows
    is no power of two
  * rowsOf's 0 in three zones of a committed row: between the matrix's entries and the pads; between
    the code's message length and the first tail; beyond the fold's entries. entriesOf, which the
    kind's own four halves are handed, is 0 at the pads and the tails too; that these four read the
    matrix's places alone is said in the head of Honest/K14/Parts.lean, by reading

  SendIdle, PublicIdle   the sentences, at a sending and at a plan
  codes_of_msgFits, plain_of_msgFits, fresh_of_msgFits   what the test on a message's shape gives
  sendIdle_of_fit     from the test on a sending's shapes (sendShapeFits)
  publicIdle_of_fit   from the test on the two sendings' shapes (sendingsFit) and four sentences
                      that it does not ask: (1)'s second, (2), (3), (9)
At the full size: publicIdle_at_head, Honest/K14/DefaultsIdleAtHead.lean.

Limits.
  * THAT THE LIST IS COMPLETE IS A READING of the definitions' texts, not a theorem.
  * SendIdle.fillers speaks of sentTables and answersOf. That the part's two moves say these, at the
    array made of its coins, is sendingPart's text; no theorem here names the moves.
  * Nothing here says that a coin below the count IS read.
  * The model encoder's points are the program's for codes of at most 2 ^ 32 positions
    (Honest/K14/Sendings.lean's head): nothing here bars a longer code.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsWithin
import Johnson.Desc.K1.Law.Declares
import Johnson.Desc.K1.Law.When
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open VerifiableInference.Desc (K1.cutSeeds)
open VerifiableInference.Desc.Own (treesMade)
open Desc.K14 (P14)

/-- **At a sending: the sentences on the cases (4) to (8) of this file's list.** -/
structure SendIdle (J : SendJob) : Prop where
  /-- the trees can be laid, and each message has a tree -/
  trees : ∃ l, treesMade J.Q.codes J.Q.sent = some l ∧ l.tree.size = J.Q.sent.size
  /-- a message with main rows names a code of the array -/
  base : ∀ k < J.Q.sent.size, (J.Q.sent.getD k default).shape.mainRows ≠ 0 →
    (J.Q.sent.getD k default).shape.code < J.Q.codes.base.size
  /-- a message with mask rows names a mask code of the array -/
  mask : ∀ k < J.Q.sent.size, (J.Q.sent.getD k default).shape.maskRows ≠ 0 →
    (J.Q.sent.getD k default).shape.maskCode < J.Q.codes.mask.size
  /-- a plain message without mask rows has at most as many answers as its code has places -/
  plain : ∀ k < J.Q.sent.size, ∀ high, J.sort k = .plain high →
    (J.Q.sent.getD k default).shape.maskRows = 0 →
    (J.Q.sent.getD k default).shape.answers ≤
      (J.Q.codes.base.getD (J.Q.sent.getD k default).shape.code default).ell
  /-- a fold's fresh table is of at least one variable and of no more row bits than variables, and
  its rows' coefficients fit the mask code's message length -/
  fresh : ∀ k < J.Q.sent.size, ∀ v h, J.sort k = .fresh v h → h ≤ v ∧ 1 ≤ v ∧
    2 * v - h + 1 ≤ (J.Q.codes.mask.getD (J.Q.sent.getD k default).shape.maskCode default).ell
  /-- each message's coins lie within the part's count -/
  count : ∀ k < J.Q.sent.size, offsetOf J.Q.codes J.Q.sent J.sort k +
    dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k) ≤ (sendingPart J).takes.e
  /-- the tables and the answers are the same whatever stands in for a coin beyond the count -/
  fillers : ∀ (t : State Ask Unit) (c : Cs (sendingPart J).takes) (d : Nat → E)
    (seeds : List (List E × E)),
    sentTables J.Q.codes J.Q.sent (J.rows t (coinsE c).toArray) =
        sentTables J.Q.codes J.Q.sent (rowsFilled J t (coinsE c).toArray d) ∧
      answersOf J.Q (J.rows t (coinsE c).toArray) seeds =
        answersOf J.Q (rowsFilled J t (coinsE c).toArray d) seeds
  /-- the list of seeds that the part cuts has a seed for each answer, at every list of elements -/
  seeds : (∀ l, (K1.cutSeeds J.Q.coordinates J.Q.seeds l).length = J.Q.seeds) ∧
    ∀ k < J.Q.sent.size, (J.Q.sent.getD k default).shape.answers ≤ J.Q.seeds

/-- What the test on a message's shape says of its two codes' numbers. -/
theorem codes_of_msgFits {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {sort : MsgSort}
    (h : msgShapeFits codes s sort = true) :
    (s.mainRows ≠ 0 → s.code < codes.base.size) ∧
      (s.maskRows ≠ 0 → s.maskCode < codes.mask.size) := by
  have hs : VerifiableInference.Desc.Own.sentShapeFits codes s = true := by
    cases sort <;> (unfold msgShapeFits at h; simp only [Bool.and_eq_true] at h)
    · exact h.1.1
    · exact h.1.1.1.1.1.1
  unfold VerifiableInference.Desc.Own.sentShapeFits at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  exact ⟨fun n => hs.1.1.2.resolve_left n, fun n => hs.1.2.resolve_left n⟩

/-- What it says of a plain message without mask rows. -/
theorem plain_of_msgFits {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {high : Bool}
    (h : msgShapeFits codes s (.plain high) = true) (hm : s.maskRows = 0) :
    s.answers ≤ (codes.base.getD s.code default).ell := by
  unfold msgShapeFits at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h.2 with c | c
  · exact c.1.2
  · omega

/-- What it says of a fold's fresh table. -/
theorem fresh_of_msgFits {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {v h : Nat}
    (hf : msgShapeFits codes s (.fresh v h) = true) :
    h ≤ v ∧ 1 ≤ v ∧ 2 * v - h + 1 ≤ (codes.mask.getD s.maskCode default).ell := by
  unfold msgShapeFits at hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  exact ⟨hf.1.1.2, hf.1.2, hf.2⟩

/-- **Where the test on a sending's shapes accepts, these sentences hold.** -/
theorem sendIdle_of_fit (J : SendJob) (hfit : sendShapeFits J = true) : SendIdle J where
  trees := by
    have h := hfit
    unfold sendShapeFits at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h.1.2
    refine ⟨l, hl, ?_⟩
    rw [VerifiableInference.Desc.Own.treesMade_eq] at hl
    exact VerifiableInference.Desc.K1.lay_tree_size hl
  base := fun k hk => (codes_of_msgFits (msgFits_at J hfit k hk)).1
  mask := fun k hk => (codes_of_msgFits (msgFits_at J hfit k hk)).2
  plain := fun k hk high e hm => plain_of_msgFits (e ▸ msgFits_at J hfit k hk) hm
  fresh := fun k hk v h e => fresh_of_msgFits (e ▸ msgFits_at J hfit k hk)
  count := fun k hk => due_in_count J k hk
  fillers := fun t c d seeds => sent_within_coins J hfit t c d seeds
  seeds := ⟨fun l => VerifiableInference.Desc.K1.cutSeeds_length _ _ l, fun k hk =>
    VerifiableInference.Desc.K1.le_seeds J.Q _ (List.mem_map.2 ⟨J.Q.sent[k], by simp, by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
      rfl⟩)⟩

/-- **At a plan: the sentences on the cases (1) to (9) of this file's list.** That lin bars (9) is a
reading of that test's text. a: the number of the round that the sendings' parts read; the sentences
do not hang on it. -/
structure PublicIdle (Q : P14) : Prop where
  /-- "send o_u" has its messages -/
  withU : ∃ u, Desc.K14.withU Q.S = some u
  /-- the masks are sent ahead -/
  ahead : Q.S.masksAhead = true
  /-- the test on G_u has a first stage -/
  stage : ∃ s, Q.S.testU.head? = some s
  /-- the shape splits: "SPLIT" has a round and a half -/
  splits : Q.S.sharedSplitNeeded = true
  /-- the library's test on the linear part's shape and codes accepts -/
  lin : OnBytes.linOk Q.codes Q.S = true
  /-- (4) to (8) at "send o_u" -/
  sendU : ∀ a, SendIdle (jobU ⟨Q, a⟩)
  /-- (4) to (8) at "send o_omega" -/
  sendOmega : ∀ a, SendIdle (jobOmega ⟨Q, a⟩)

/-- From the test on the two sendings' shapes, with the four sentences that it does not ask. -/
theorem publicIdle_of_fit {Q : P14} (hfit : sendingsFit Q = true) (hm : Q.S.masksAhead = true)
    (hst : ∃ s, Q.S.testU.head? = some s) (hsp : Q.S.sharedSplitNeeded = true)
    (hl : OnBytes.linOk Q.codes Q.S = true) : PublicIdle Q := by
  have h := hfit
  unfold sendingsFit at h
  simp only [Bool.and_eq_true] at h
  have eU : ∀ a, sendShapeFits (jobU ⟨Q, a⟩) = sendShapeFits (jobU ⟨Q, 0⟩) := fun a => by
    unfold sendShapeFits
    rfl
  have eO : ∀ a, sendShapeFits (jobOmega ⟨Q, a⟩) = sendShapeFits (jobOmega ⟨Q, 0⟩) := fun a => by
    unfold sendShapeFits
    rfl
  exact ⟨Option.isSome_iff_exists.1 h.1.1.1.1, hm, hst, hsp, hl,
    fun a => sendIdle_of_fit _ ((eU a).trans h.1.1.1.2),
    fun a => sendIdle_of_fit _ ((eO a).trans h.1.1.2)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.codes_of_msgFits
#print axioms ProofFile.Honest.K14.plain_of_msgFits
#print axioms ProofFile.Honest.K14.fresh_of_msgFits
#print axioms ProofFile.Honest.K14.sendIdle_of_fit
#print axioms ProofFile.Honest.K14.publicIdle_of_fit
