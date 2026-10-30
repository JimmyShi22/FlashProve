-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/K9RowsByLinkStatement.lean: THE KIND K9 (the batching of a segment's claims): THE ROWS
OF THE DECLARED ROUND OF EACH OF THE 25 BATCHINGS, BY THE SEGMENT's NUMBER, AS NUMBERS: where the
public part's table of stretches and the entries of its first list of declared rounds are the
written ones; and so under the library's head. STATEMENTS ALONE: one definition with code, this
file's own, and four definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of
the library's goals: they are lemmas' statements.

WHAT IT IS FOR. The public test `rowsFitB` (Johnson/Desc/First/Link/K9RowsAsk.lean) compares a
number off a segment's plan with p.rows, p := `IM.k9At Z l` (Johnson/IMR/LinkSeat.lean). This is its
right side. WHAT IT IS NOT. NOTHING ON THE TEST's LEFT SIDE; THE TEST's YES IS NOT SAID AT ANY
SEGMENT. The full size alone.

  `rowsAtLink l`      the written numbers, by the segment's number (Johnson/P1K8R/RowsAtLink.lean)
  `rowsClosedB f`     THIS FILE's OWN: a test with code: at each l below 25 K9's numbers read off
                      the written places and entries (`k9WhereE xsW l`,
                      Johnson/AtFull/Desc/Lots/K9RowAt.lean, K9RowWritten.lean) are there, with
                      f l rows
  `K9RowsClosed`      the test says yes at `rowsAtLink`
  `K9RowsBites`       it can fail: with one row more at 24 it says no; with the numbers of 0 and 2
                      changed over it says no; at 25 no numbers are there
  `K9RowsOfWritten`   Z.cuts = cutWritten and the entries of Z.D.1 are esW: at each l below 25
                      `IM.k9At Z l` is some p with p.rows = rowsAtLink l
  `K9RowsAtHead`      the same at the head's Zp (`P5J.AtMg`), at every earlier hash o

NEAR. `full_rows` (Johnson/Desc/First/Batch/Law/Condition.lean): the same 25 numbers, of K9's rounds
of the written list IN THE LIST's ORDER: it does not say which segment's each is.
`k9_entry_written`, `rows_ne_zero`, `rows_le` (Johnson/LPFK9R/): K9's entry at a segment is a member
of the written list: no index. `OnBytes.Tie.Pv.Plan.closeAt` (OnBytes/Tie/Pv/Plan/PlanSizes.lean): a
written table by segment with these rows: data; no theorem. `rows_of_written`
(Johnson/LPFK10R/RowsLive.lean): the like road for the kind K10's number; which number its closed
term is, is shown there by no theorem. `batch_written` (K9RowWritten.lean), `k9_batch_closed`
(Johnson/AtFull/Rounds/K9At.lean): closed facts on the same written term.

Limits. Equations of numbers. It stands over files under Johnson/AtFull/. Nothing on any property.
-/
import Johnson.P1K8R.RowsAtLink
import Johnson.AtFull.Desc.Lots.K9RowWritten
import Johnson.IMR.LinkSeat
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open VerifiableInference.Desc (Chain)
open Johnson.AtFull.Desc.Lots (k9WhereE xsW esW)
open Johnson.AtFull.Cut (cutWritten)

/-- **The test.** This file's own. -/
def rowsClosedB (f : Nat → Nat) : Bool :=
  (List.range 25).all fun l => decide ((k9WhereE xsW l).map (·.rows) = some (f l))

/-- The closed fact's statement. Not proved here; a lemma's statement, none of the library's goals.
-/
def K9RowsClosed : Prop := rowsClosedB rowsAtLink = true

/-- The statement that the test can fail. Not proved here; a lemma's statement, none of the
library's goals. -/
def K9RowsBites : Prop :=
  rowsClosedB (fun l => if l = 24 then 24653738 else rowsAtLink l) = false ∧
    rowsClosedB (fun l => if l = 0 then 32005793 else if l = 2 then 32005923 else rowsAtLink l) =
      false ∧
    (k9WhereE xsW 25).isNone = true

/-- The statement at the written values. Not proved here; a lemma's statement, none of the library's
goals. -/
def K9RowsOfWritten : Prop :=
  ∀ (Z : ProofFile.Pub), Z.cuts = cutWritten → Z.D.1.map (·.entry) = esW →
    ∀ l, l < 25 → ∃ p, IM.k9At Z l = some p ∧ p.rows = rowsAtLink l

/-- The statement under the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def K9RowsAtHead : Prop :=
  ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg o Z D r Zp Np cF →
    ∀ l, l < 25 → ∃ p, IM.k9At Zp l = some p ∧ p.rows = rowsAtLink l

end P1K8

#print axioms P1K8.rowsClosedB
#print axioms P1K8.K9RowsClosed
#print axioms P1K8.K9RowsBites
#print axioms P1K8.K9RowsOfWritten
#print axioms P1K8.K9RowsAtHead
