-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeadRowsInScopeStatement.lean: THE PLAN OF THE OUTPUT HEAD's SUB-PROOF: ITS NUMBER OF
LINEAR CLAIMS AND ITS OWN NUMBER OF ROWS (THE PLAN's FIELD rows) ARE WRITTEN NUMBERS AT ALL PUBLIC
FILES IN THE GOALS' SCOPE: 297 AND 24,653,737; AND ONE EQUATION TOWARD THE LEFT SIDE OF THE PUBLIC
TEST `rowsFitB` (Johnson/Desc/First/Link/K9RowsAsk.lean) AT THE HEAD's PLAN: firstB + n * stepF IS
equationsF n. That the left side is the plan's number of rows follows with `public_H_rows` (see
NEAR): in the callers, not in a statement here. STATEMENTS ALONE: four definitions of propositions;
no definition of another kind. NOTHING IS PROVED IN THIS FILE, and none is one of the library's
goals: they are lemmas' statements.

WHAT IT IS NOT. NOTHING ON THE NUMBER OF ROWS THAT THE DESCRIPTION's DECLARED ROUND STATES, ANOTHER
TEXT's NUMBER (Johnson/P1K8R/K9RowsByLink.lean has it); THE TEST's YES IS NOT SAID. The head's plan
alone: nothing at the 24 other segments. The second and the third statement hold at every layout
file (a letter), as `plan_in_scope`.

  `PlanH2NLin`        general, no scope: where `Head.planH2` (OnBytes/Model/HeadPlan.lean) returns
                      hp: hp.nLin is `Head.claimsH` at hp's OWN data of the smallness test
  `HeadNLinInScope`   in scope, where `publicOf` returns X: X.H.nLin = 297
  `HeadRowsInScope`   the same: X.H.rows = 24653737
  `HeadLeftIsRows`    where `publicOf` returns X, no scope: at every n:
                      firstB X.H.tl + n * X.H.tl.stepF = X.H.tl.equationsF n

NEAR. `PlanWritten`, `plan_in_scope` (Johnson/Desc/Kinds/Law/HeadPlanWritten.lean): sixteen sizes of
the same plan in scope; neither of these two. `factsB`, `factsW`
(Johnson/AtFull/Head/PlanAtFull.lean): both numbers, by the kernel, of the plan at the stored free
numbers alone. `planClaims_at_head` (Johnson/Desc/First/Link/Law/PlanClaimsAtBatch.lean): at a state
reached at the head's batching the ledger's planned number is X.H.nLin: which number that is it does
not say. `public_H_rows` (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean), `planH2_rows` (BatRows.lean):
rows = nLin + equationsF: called. `firstOf_eq` (OnBytes/Tie/Pv/Tail/ClosedRows.lean), `topOf_eq`
(FoTopOf.lean): kin of the fourth statement: the same sum, each under a premise on the listed shapes
(the first: they fit the matrices, and mS is the number of rows of symbols; the second: the premise
that `public_H_mS` pays here). `firstB_fold` (Johnson/Desc/First/Link/Law/K9RowsParts.lean, another
group of authors' work): the fourth statement's sentence at any data, under the two premises that
are paid here; it is not called, and that file is not imported here.

Limits. Equations of numbers. Nothing on any property.
-/
import Johnson.Desc.First.Link.K9RowsAsk
import OnBytes.Model.VerifyPublic
import Johnson.Goal.Meaning.HeadShapeScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (firstB)

/-- The statement on the plan's routine. Not proved here; a lemma's statement, none of the library's
goals. -/
def PlanH2NLin : Prop :=
  ∀ (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border) (O : Head.Owner) (NGr lkW : Nat)
    (hp : Head.HPlanH2), Head.planH2 g h L b O NGr lkW = .ok hp →
    hp.nLin = Head.claimsH h L hp.tl (Head.readsH h L b)

/-- The statement on the claims. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadNLinInScope : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public),
    VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    Verify.publicOf Pb.pol Pb.KL lay = .ok X → X.H.nLin = 297

/-- The statement on the rows. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadRowsInScope : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public),
    VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    Verify.publicOf Pb.pol Pb.KL lay = .ok X → X.H.rows = 24653737

/-- The statement on the test's left side. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadLeftIsRows : Prop :=
  ∀ (pol KL : ByteArray) (lay : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL lay = .ok X →
    ∀ n, firstB X.H.tl + n * X.H.tl.stepF = X.H.tl.equationsF n

end P1K8

#print axioms P1K8.PlanH2NLin
#print axioms P1K8.HeadNLinInScope
#print axioms P1K8.HeadRowsInScope
#print axioms P1K8.HeadLeftIsRows
