-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsYesStatement.lean: A STRONGER CLAUSE OF keeps FOR THE KIND K11: THE
KIND's CLAUSE `K11Keeps` (KeepsStatement.lean of this folder) AND THE YES OF THE MERGE's OWN
DECISION; AND ITS WRAPPER BY THE PLACE: two definitions, and STATEMENTS: four definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are
lemmas' statements.

  `K11KeepsYes P s s'`         `K11Keeps P s s'`, and there are rounds rs with `headMergeDecide P s
                               rs = .ok s'`
  `K11KeepsYesAt P p s s'`     p is the kind's address on the first chain (`IM.k11Place`), and that:
                               the form in which the honest side's frame lays the letter by the
                               member's kind. AT A PLACE THAT IS NOT ITS OWN IT IS FALSE
  `K11KeepsYesAtGives`         it gives the weaker wrapper `K11KeepsAt` (KeepsAtStatement.lean of
                               this folder) at every place: so whatever takes that clause takes this
                               one
  `K11KeepsYesAtIs`            at its own place it is the stronger clause
  `K11KeepsYesAtElse`          at every other place it holds of no two states
  `HeadMergeKeepsYesAtOfStep`  its payer: a yes of the step of the kind's block as it stands at a
                               seat gives it at the kind's address

Why. `K11Keeps` holds an equation for the state behind in which what the merge leaves for the row on
the weights is a bare "there is": so it does not say which slot `K9.mergeOf` names behind the step;
the public test inside the sentence "forms" reads that slot. The library's lemmas that carry items
over the merge take the decision's yes.

Limits. Those of KeepsAtStatement.lean: the yes of the step is a premise of the payer; `IM.k11Place`
is a written address, the full size's; P is a letter. The weaker clauses of KeepsStatement.lean and
KeepsAtStatement.lean stand beside this one: it takes the place of neither. No thread and no prover
stands here. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsAtStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- **The kind's clause of keeps, with the yes of the merge's own decision.** -/
def K11KeepsYes (P : HeadMergeP) (s s' : S) : Prop :=
  K11Keeps P s s' ∧ ∃ rs, headMergeDecide P s rs = .ok s'

/-- **The stronger clause, as a function of the place.** False at a place that is not the kind's
own. -/
def K11KeepsYesAt (P : HeadMergeP) (p : Place) (s s' : S) : Prop :=
  p = IM.k11Place ∧ K11KeepsYes P s s'

/-- The statement that it gives the weaker wrapper. Not proved here; a lemma's statement, none of
the library's goals. -/
def K11KeepsYesAtGives : Prop :=
  ∀ (P : HeadMergeP) (p : Place) (s s' : S), K11KeepsYesAt P p s s' → K11KeepsAt P p s s'

/-- The statement that it is the clause at its own place. Not proved here; a lemma's statement, none
of the library's goals. -/
def K11KeepsYesAtIs : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11KeepsYesAt P IM.k11Place s s' ↔ K11KeepsYes P s s'

/-- The statement on every other place. Not proved here; a lemma's statement, none of the library's
goals. -/
def K11KeepsYesAtElse : Prop :=
  ∀ (P : HeadMergeP) (p : Place) (s s' : S), p ≠ IM.k11Place → ¬ K11KeepsYesAt P p s s'

/-- The statement on its payer. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadMergeKeepsYesAtOfStep : Prop :=
  ∀ (ft : ℕ) (P : HeadMergeP) (name : String) (pl : Place) (s s' : S),
    StepYes ft (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) s s' →
    K11KeepsYesAt P IM.k11Place s s'

end Johnson.Desc.First.ForkMerge.Returns

#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsYes
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAtGives
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAtIs
#print axioms Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAtElse
#print axioms Johnson.Desc.First.ForkMerge.Returns.HeadMergeKeepsYesAtOfStep
