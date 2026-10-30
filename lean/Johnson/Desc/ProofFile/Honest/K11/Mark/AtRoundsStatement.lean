-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/AtRoundsStatement.lean: THE SENTENCE THAT IS OWED FOR THE
MARK AT THE MERGE OF THE CLAIMS ON THE WEIGHTS (`headMergeMark`, Statement.lean of this folder), AT
EVERY LIST OF ROUNDS' DATA THAT FITS THE MERGE's OWN DECLARED ROUNDS: IN THE FORM IN WHICH THE
FRAME's AUTHORS' FIELD hM ASKS IT: STATEMENTS ALONE: three definitions of propositions. NOTHING IS
PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `MergeListedFit`        where dsb fits the merge's declared rounds pair by pair (`KindFits`,
                          Honest/Law/Due.lean: the data bear the declared round's entry and the kind
                          of that entry's name): each listed round of dsb (numbers 1 to lk + 1)
                          draws one field element and nothing else, and its entry's positions have
                          at most 64 bits (these entries draw no position: the number is 0): THE
                          PREMISE OF `HeadMergeMarkDebt`
  `HeadMergeMarkDebtAt`   so: at every such dsb and whatever is handed of the challenges in front:
                          `MarkDebt` at strings of hash blocks, at the mark's stated share's value
  `HeadMergeMarkDebtSeat` the same with the rounds read off the kind's block as it is seated
                          (`IM.seatedAs`), at any name and place: the sub-protocol that stands at
                          number 346 of the first chain under the library's head has that form
                          (`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFullStatement.lean)

Limits. Those of `HeadMergeMarkDebt`, but for its premise on the data. The share is A STATED NUMBER,
with a factor 2 to spare; it is not evaluated. The uniform law on the rounds' messages is named, not
derived. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.Statement
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (RDT)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.K8.Honest (OneElem)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)

/-- The statement on the listed rounds. Not proved here; a lemma's statement, none of the library's
goals. -/
def MergeListedFit : Prop :=
  ∀ (lk work : Nat) (dsb : List RDT),
    List.Forall₂ KindFits dsb ((mergeEntries lk 1 work).map fun e => { entry := e }) →
    ∀ i d, dsb[i]? = some d → i ∈ mergeListed lk → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64

/-- The statement of the mark's sentence at the declared rounds. Not proved here; a lemma's
statement, none of the library's goals. -/
def HeadMergeMarkDebtAt : Prop :=
  ∀ (P : HeadMergeP) (dsb : List RDT) (Q : List Fmt.Drawn → Prop),
    List.Forall₂ KindFits dsb ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) →
    MarkDebt (_root_.Run.ckP .two) (headMergeMark P) dsb Q (headMergeMark P).share.val

/-- The statement at the seated block's rounds. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeMarkDebtSeat : Prop :=
  ∀ (P : HeadMergeP) (name : String) (pl : Place) (dsb : List RDT) (Q : List Fmt.Drawn → Prop),
    List.Forall₂ KindFits dsb (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl).rounds →
    MarkDebt (_root_.Run.ckP .two) (headMergeMark P) dsb Q (headMergeMark P).share.val

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.MergeListedFit
#print axioms ProofFile.Honest.K11.HeadMergeMarkDebtAt
#print axioms ProofFile.Honest.K11.HeadMergeMarkDebtSeat
