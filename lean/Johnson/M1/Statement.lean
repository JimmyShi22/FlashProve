-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/Statement.lean: THE LEMMA ON ENCODED ROWS THAT ZERO KNOWLEDGE NEEDS. STATEMENTS WITHOUT PROOFS. This file has the
head and the conjunction; the statements stand in Johnson/M1/Law.lean (protocol-free), Numbers.lean (at the protocol's numbers,
first chain), NumbersAt.lean (the other two chains) and AtDescription.lean (at the description that verify is compiled from).

IN PLAIN LINES.
 1. WHOSE VIEW. One request's proof (one request a proof), an HONEST verifier: challenges and positions are drawn
    independently of the prover's coins. Counted: the 82 prover's messages of encoded rows on the proof file's FIRST chain,
    in 83 trees, and EVERY opening of these trees by any of the three chains.
 2. A row is a Reed-Solomon word of (r random tail entries, then the message). In each tree the SHORTEST tail among its rows
    is exactly the number of positions drawn, in sum, for that tree: 219; 55, 55, 55, 46, 44; 55 at the index-mask message and
    at W's tree. No slack, tree by tree. One row is longer than its draws: W's main row, 3571 for 55.
 3. (A), THE ROWS. At each sending, whatever the rows' data are (the witness and all earlier coins included), the opened
    columns together with the out-of-domain answers have ONE distribution. Exact: no error term. `Spec.rows` says it over ALL of
    the sending's coins, those that later parts spend among them.

 4. It needs three public facts: the draws for a tree, summed, are at most its rows' tails (A1); each answer has a pad of its
    own under a factor that is drawn non-zero; the tail's entries are the word's lowest coefficients.
 5. (B), THE CHAIN. Everything else that is shown (each sumcheck's scalars, the merge's end value, the fold's, the last
    step's open words) is a one-to-one image of coins of its own, shifted by things earlier in one fixed order.
 6. So AT EVERY LIST OF CHALLENGES AT WHICH THE HONEST PROVER DOES NOT STOP FOR A PRIVATE REASON the view has a law that is
    made of the public result alone (`OneLawOff`). It is said challenge by challenge.
 7. IT IS NOT PERFECT, AND NOT «PERFECT GIVEN NO STOP». The smallness test K8 stops on hidden cells: Stop(w) hangs on the
    witness, so conditioned on no stop the law of the challenges themselves differs between two witnesses. What follows is
    STATISTICAL: distance at most Pr[Stop(w)] from the simulator (`Spec.chainStat`). TWO SORTS OF STOP, KEPT APART:
    PUBLIC (Bad): a set of challenges alone. There both sides are the notice «none»: a ledger of no block; the equation holds
    there too. No part of the honest prover has such a stop. PRIVATE (Hid w): K8's window, on hidden cells.
    So the letter `stop` below is to be filled with `PrivateStop bad hid`. Its bound is a LETTER (`StopBound`): no value is
    stated or used here. A LIMIT: how often K8's window stops the prover is proved nowhere in these files; the figures that
    exist on paper (one stands in the head of Honest/K8/Part.lean) are not reconciled with each other. A statement whose
    printed error bounds the WHOLE withheld set charges a public stop too, though the equation holds there.
    NO STOP, BUT A FALL, as the honest part's own file has it (Johnson/Desc/ProofFile/Honest/K4/Part.lean, «The stops. None of
    either sort»; k4CoinZero, k4Fall): where the element that joins the second token sumcheck's hiding polynomial to its claim
    is sampled as 0, «the prover plays on there: its moves divide by no sampled value», and that member of the verifier rejects.
 8. NOT CLAIMED: zero knowledge of anything; anything after hashing (there positions are no longer independent of the coins
    for free: the compiler's theorem must carry that); a batch's view: Omega's rows (3571 = 51 + 64·55) are shared by a
    batch's 64 requests; the shared chain's and the last chain's trees are counted apart, at one request
    (Johnson/M1/NumbersAt.lean), and no law of their rows is stated; masks derived from a seed; the committed tables' own budget.
 9. NOT CLAIMED: that Lean's honest prover is the program's. (B) is stated of LETTERS for the honest prover's term.
10. WHAT WOULD REFUTE IT: a tree drawn at one position more than r (A1 false); a shown value without a coin of its own; a
    coin paid twice (`Pays` false at a block); a further stop that hangs on the witness.

WHAT THE LEDGER ASKS OF THE HONEST PROVER: EIGHT DUTIES. No test of the verifier enforces one of them,
and each is needed with no slack. Uniform, and independent of each other and of all else:
  (i)   a tail for EVERY row of EVERY oracle message: the unsampled ones too (fresh masks, the masking word), and every kept
        member at EACH sending anew;
  (ii)  a pad for every sampled message, new at each sending;
  (iii) every mask entry that a ledger hands out: the link's mask row's, and the request's INDEX-MASK MESSAGE's;
  (iv)  the 2 k + 1 coefficients of every fold's hiding polynomial;
  (v)   the masking word of the last step, message and tails.
And: (vi) no data on a pad's places; (vii) what a later message holds hangs on the witness, the challenges and EARLIER coins
only; (viii) EVERY CLAIM ON WHICH A PART IS CALLED IS TRUE: target* and the last step's words are public functions of the rest
only because the claims are true. Where a claim turns false by an unlucky challenge, the prover stops, or the run falls: the
block refuses at its end and no part behind it is called.

IN THE FRAME OF Johnson/Desc/ProofFile/Honest/ (B) HAS A PROVED FORM: rule_views, rule_same (Honest/Law/Rule/Row.lean): from
`Owed F Bk H G Rel` and `G.owns = true`, at every due list of challenges outside the one silent set (`silentAt`), the honest
views' law is the session's; and one_exact_at (Honest/Law/Rule/OneAt.lean), which speaks outside the PRIVATE stops alone: its
simulator says «none» at a public stop. So at the honest prover's term (B) comes down to `Owed`. The ledger says the same
without the frame, for a reader; it is protocol-free.

WHO PAYS WHAT (the blocks of (B), in their order).
  1. each masked sumcheck's elements, in the order of sending  ·  its hiding coefficients and end masks: entries of the LINK's
     mask row (slot j = the j-th scalar sent)                                                        · toSim_bij
     EXCEPT a merge's end value fv' = fv + beta c (in the layers' sub-proofs and the head's): c is an entry of the request's
     index-mask message (sending 0, message 4, tree 1, mask code 12: 256 entries, tail 55 for 55 draws in sum); slot sFv of the
     link's own mask row masks nothing (OnBytes/Model/Merge.lean, WsMerged.sFv; Pending.lean's head). K13 takes the next
     entries of that message.
  then group by group (25 links, 6 stages), in the order of sending:
  2. the group's answers  ·  the pads                                                                · sendExact (Mends)
  3. its fold's 2 k + 1   ·  the fresh mask's coefficients (17 at 13 closings, 15 at 12; 3 9 7 7 9)   · run_one_to_one
  4. its opened columns   ·  the tails                                                               · tailCovers, within (A1)
  last: 5. the last step's open words  ·  the masking word                                           · Spec.base
  In `made`, with no coin, being public functions of the rest: target*, the masking word's symbols, every target.
-/
import Johnson.M1.Law
import Johnson.M1.Numbers

set_option autoImplicit false

namespace OnBytes.M1

/-- The count, the sending-by-sending law and the protocol-free laws. WITHOUT (A3), the description, AND WITHOUT (A4), `Spec.lent`:
the lent coins, that is, that each coin which a later part spends is charged once. (A4) is the one clause that can fail, and it
is a conjunct of nothing here. So this is NOT the lemma M1 whole. -/
def Spec.M1BareWithoutLent : Prop := Spec.numbers ∧ Spec.law

end OnBytes.M1

/- THE NAMES, WITH PATH:LINE (of the declaration or its docstring; no check keeps the lines current)
Spec.rowsExact            Johnson/SendSim/At/Sim.lean:308 · proved: At/RowsExact.lean:48 (rowsExact)
budAt · asked · shownR    Johnson/SendSim/At/Sim.lean:283 · :278 · :296
Spec.rowsFresh | Any      Johnson/SendSim/At/CutTie.lean:107 · At/FoldAny.lean:74
WithinAt · SpenderClear · BookClear   Johnson/SendSim/At/Fresh.lean:220 · :267 · :272 ; BookClearAny, Spec.sendFreshAtWide At/BookWide.lean:63, :75
Spec.sendExact | sendFresh  Johnson/SendSim/Defs.lean (end) · proved CoreProofs.lean:120, :129 ; tl, Sender: Defs.lean
sym · tailCovers · sym_shift  Johnson/LinkSim/Tail.lean:122 · :77 · :138
K1.Par                    Johnson/Desc/K1/Send.lean:85
sendFits · dueR · rowsR · Ride · rideFits   Johnson/Desc/ProofFile/Honest/K1/Coins.lean:127 · :119 · :138 · :62 · :84
seedsAt · seedsFit        Johnson/Desc/ProofFile/Honest/K1/Part.lean:83 · :87
sendingPar · rideOf · coreSender   Johnson/Desc/ProofFile/Honest/K2/Sending.lean:131 · :137 · :158
switchSent · switchFresh · switchPart   Johnson/Desc/ProofFile/Honest/K2/Part.lean:166 · :173 · :219
switchBud · asksWithin · SendSameLaw    Johnson/Desc/ProofFile/Honest/K2/Exact.lean:133 · :125 · :160
Own.treesMade             Johnson/Desc/Own/Trees.lean:116
readsTab · drawnTab · treesAt · readsWithinT   Johnson/SendSim/Seat/ReadsTab.lean:47 · :52 · :56 · :62
tabW · drawnW · readsW · readsW_rejects · lotsReadsB_of_written   Johnson/SendSim/Seat/ReadsAtWritten.lean:72 · :100 · :113 · :120 · :144
ReadsWithin · BudClause   Johnson/SendSim/Seat/Bud.lean:74 · :59 ; budAt_of_reads Seat/BudProof.lean:67
Spec.readsAt · reads_of_live · bud_of_live · handIn_of_live   Johnson/SendSim/Seat/ReadsAtLive.lean · :150 · :203 · :216
sendsFullLit              Johnson/G/SendsLit.lean:47 (119 sendings; 82 at (2, 0), by program)
proofSizedFull            Johnson/Desc/Ok/PlanWritten/SizedLit.lean:37 ; cutFirstFull CutLit.lean:31
WideLaw · tri_law · fresh_wide · fresh_wide_table   Code/FreshWide.lean:96 · :182 · :235 · :315
pr · unif · tv            Prob/Basic.lean:26 · :32 · :40
RunOneToOne · runSent · run_one_to_one   Johnson/Desc/ProofFile/Honest/K10/Sim.lean:443 · :422 · K10/SimMap.lean:239
close_exact · close_oneToOne   Johnson/Desc/ProofFile/Honest/K10/SimSent.lean:505 · :501
toSim_bij · exact_sumPart · exact_sumPart_field   …/Honest/SumLaw/SumBij.lean:263 · SumExact.lean:237 · :321
exact_rest · Asked        …/Honest/K12/Sim/Exact.lean:280 · :173
Good (exact, fresh; the second stop `.hid`)   …/Honest/Side.lean:506 ; K8's stop: …/Honest/K8/Part.lean, head
rule_views · rule_same · row_law  …/Honest/Law/Rule/Row.lean:156 · :190 · :121 ; Owed …/Honest/Owed.lean:139 ; silentAt …/Honest/Rule.lean
owed_of_threads           …/Honest/Law/OwedRule.lean ; rowOk_of Law/Rule/Bridge.lean ; cells₁ Law/Rule/FileCells.lean:81 ; session Law/Rule/Session.lean
-/
