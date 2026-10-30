-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsAtStatement.lean: THE CLAUSE OF keeps OF THE KIND K11, FOR THE WHOLE
MEMBER, AS A FUNCTION OF THE PLACE: `K11KeepsAt P : Place → S → S → Prop`: the form in which the
honest side's frame lays that letter by the member's kind (`kpBy`,
Johnson/Desc/ProofFile/Honest/Thread/KeepsBy.lean, a file that is not in this library): one
definition, and STATEMENTS: three definitions of propositions. NOTHING IS PROVED IN THIS FILE, and
none is one of the library's goals: they are lemmas' statements.

  `K11KeepsAt P p s s'`      p is the kind's address on the first chain (`IM.k11Place`,
                             Johnson/IMR/K11Seat.lean), and `K11Keeps P s s'` (KeepsStatement.lean
                             of this folder): what an accepting step of the merge's member leaves
                             and turns of the verifier's state: the five facts on the state in front
                             and the one equation on the whole state behind that that file's
                             `K11Writes` holds, AND, BESIDE THESE, "s'.failed = none". AT A PLACE
                             THAT IS NOT ITS OWN IT IS FALSE: a laying at a wrong place can be paid
                             by nobody
  `K11KeepsAtIs`             at its own place it is that clause
  `K11KeepsAtElse`           at every other place it holds of no two states
  `HeadMergeKeepsAtOfStep`   its payer: a yes of the step of the kind's block as it stands at a seat
                             (`StepYes`, Johnson/Top/H0/Walk/Reach.lean) gives it at the kind's
                             address

Limits. The yes is a premise. `IM.k11Place` IS A WRITTEN ADDRESS, THE FULL SIZE's (link 24, piece
9): AT A CHAIN OF ANOTHER SIZE THE CLAUSE IS FALSE EVERYWHERE, at the merge's own place too. The
kind's public numbers P are a letter: they hang on no place. THAT THE SEAT's ADDRESS IS
`IM.k11Place` IS NOT ASKED IN THE PAYER: pl is free there; where the first chain lays the block, it
lays it at that address (`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean, under the
library's hypothesis on the public files, `P5J.AtMgA`). No thread and no prover stands here. Nothing
on any property.
-/
import Johnson.Desc.K11.Returns.OfFormStatement
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- **The kind's clause of keeps, as a function of the place.** False at a place that is not the
kind's own. -/
def K11KeepsAt (P : HeadMergeP) (p : Place) (s s' : S) : Prop :=
  p = IM.k11Place ∧ K11Keeps P s s'

/-- The statement that it is the clause at its own place. Not proved here; a lemma's statement, none
of the library's goals. -/
def K11KeepsAtIs : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11KeepsAt P IM.k11Place s s' ↔ K11Keeps P s s'

/-- The statement on every other place. Not proved here; a lemma's statement, none of the library's
goals. -/
def K11KeepsAtElse : Prop :=
  ∀ (P : HeadMergeP) (p : Place) (s s' : S), p ≠ IM.k11Place → ¬ K11KeepsAt P p s s'

/-- The statement on its payer. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadMergeKeepsAtOfStep : Prop :=
  ∀ (ft : ℕ) (P : HeadMergeP) (name : String) (pl : Place) (s s' : S),
    StepYes ft (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) s s' →
    K11KeepsAt P IM.k11Place s s'

end Johnson.Desc.First.ForkMerge.Returns

#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsAt
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsAtIs
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsAtElse
#print axioms Johnson.Desc.First.ForkMerge.Returns.HeadMergeKeepsAtOfStep
