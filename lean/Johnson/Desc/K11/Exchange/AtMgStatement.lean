-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtMgStatement.lean: THE TWO SENTENCES THAT THE MERGE OF THE CLAIMS ON THE
WEIGHTS OWES BEHIND ITS STEP, AS FIELDS OF THE COMPOSED MEANING OF THE TABLE OF JOINTS (`mgAll`,
Johnson/Desc/Sound/MgAll.lean): STATEMENTS ALONE: three, each a definition of a proposition. NOTHING
IS PROVED IN THIS FILE, and none of the three is one of the library's goals: they are lemmas'
statements. The texts are the table's; no prover is named.

Why. Johnson/Desc/K11/Exchange/Statement.lean and RowStatement.lean end in the table's sentence at
the reader that is the run itself, and in "every row that the reader gives holds". The composed
meaning reads a run through the readers of a link of the description, under the table's own names.

  `FormsAtLink`   the table's sentence at the reader that is the merge's run gives the sentence at
                  the readers of a link whose sub-protocol states, under the run's name, a run that
                  accepts just where the merge's does, with the same answers. (The other way is the
                  library's `formsQ_link_merge`, Johnson/Top/H0/MergeLaw/MergedAtLink.lean.)
  `MergedAtMg`    so, at a segment of the output head's sort: the field forms of the composed
                  meaning at (9, "merged")
  `WoAtMg`        "every row that the reader gives holds of the pile's own reading of the witness"
                  is the field wo of the composed meaning

Limits. General in the composed meaning's data, and in the segment: any of the output head's sort;
nothing asks that it is the one that the readers' second hole serves. hst and hr (what the link
states) are premises. That the sentences on the left hold is a premise. Nothing on any property.
-/
import Johnson.Desc.Sound.MgAt.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (TensorRow)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Link Claim Strs Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.MergeLaw (mergeStates)
open VerifiableInference.Desc.K9 (Readers readersOfLink holesAt statesOfLink)
open VerifiableInference.Desc.K13.Law (Holds)
open VerifiableInference.Desc.Sound (formsQ MsgQ MgData mgAll seatTab CellsQ MsgT)
open Johnson.Desc.First.Walk.Law (rowAt)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

/-- The statement from the run's own reader to a link's readers. X, mH, m: what the readers' two
holes take. l: the link. r: the run that its sub-protocol number `piece` states under the name. Not
proved here; a lemma's statement, none of the library's goals. -/
def FormsAtLink : Prop :=
  ∀ (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (l : Link S Claim) (own : List (ℕ × ℕ))
    (piece : ℕ) (run name : String) (r : ℕ → S → Except String (List Claim × S)) (s : S)
    (rd : ℕ × ℕ → MsgQ),
    (run == "K8.equations") = false →
    ((statesOfLink l piece).find? fun x => x.1 == run) = some (name, r) →
    (∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y) →
    formsQ (Readers.ofStates (mergeStates run)) own piece run s rd →
    formsQ (readersOfLink (holesAt X mH m l) l) own piece run s rd

/-- The statement at the composed meaning's field forms. D, Mg: the composed meaning's data, and the
meaning beneath. m: the segment. z: what was handed to the chain. b: the verifier's state. Not
proved here; a lemma's statement, none of the library's goals. -/
def MergedAtMg : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (m : ℕ) (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S))
    (z : P) (b : S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT),
    D.links[m]? = some .head → D.lk m = some l →
    ((statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) →
    (∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y) →
    formsQ (Readers.ofStates (mergeStates "the merge")) (D.N.group m) 8 "the merge" b
      (seatTab D.cs D.arr D.ms w) →
    (mgAll D Mg).forms m 9 "merged" (z, b) y w

/-- The statement at the composed meaning's field wo. Not proved here; a lemma's statement, none of
the library's goals. -/
def WoAtMg : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (m : ℕ) (z : P) (b : S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT),
    (∀ r : TensorRow, rowAt D.d1.lay (D.d1.ncl m) D.d1.lin b = some r →
      Holds Reading.gl (D.rw13 (z, b) w) r) →
    (mgAll D Mg).wo m (z, b) y w

end Johnson.Desc.First.ForkMerge.Exchange
