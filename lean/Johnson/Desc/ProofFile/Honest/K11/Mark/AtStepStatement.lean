-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/AtStepStatement.lean: `HeadMergeLiveOfSilent`
(JoinStatement.lean of this folder) AT THE ROUNDS AS A MEMBER's STEP SHOWS THEM TO ITS DECISION, AND
FROM TWO FACTS ON THE LEDGER IN FRONT: STATEMENTS ALONE: two, each a definition of a proposition.
NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas'
statements.

A member's step shows its decision the view's rounds without the sealed digest (`noDigest`,
Johnson/Desc/Block.lean); a mark's test and `drawsFit` are asked at the view's own drawn values.

  `LaterDrawsNoDigest`    the elements that the rounds from number 1 on have drawn (`laterDraws`,
                          Johnson/Desc/K11/Live/BehindStatement.lean) are the same with and without
                          the digest
  `HeadMergeLiveAtStep`   R: the view's rounds. Where the mark says nothing at R's drawn values;
                          these fit the kind's declared rounds; the decision says yes from s to s'
                          on R without the digests; a, x: the head's own fields and what the head
                          heard, in front; the slot of the claim's value is filled; and nothing at
                          or above the ledger's next free number is filled:
                          `MergeLive P.lay.lk a.F.next x.sV s'`

Limits. The yes is a premise; so is that the drawn values fit; so are the two facts on the ledger.
No thread is named. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.JoinStatement
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.PscRun (Filled FreeAbove)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)
open Johnson.Desc.First.ForkMerge.Live (MergeLive laterDraws)

/-- The statement on the digest. Not proved here; a lemma's statement, none of the library's goals.
-/
def LaterDrawsNoDigest : Prop :=
  ∀ R : List Fmt.RoundView, laterDraws (R.map noDigest) = laterDraws R

/-- The statement at the step's rounds. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadMergeLiveAtStep : Prop :=
  ∀ (P : HeadMergeP) (fr : List Fmt.Drawn) (s s' : S) (R : List Fmt.RoundView) (a : HeadOwn)
    (x : OnBytes.Model.Head.Heard),
    (headMergeMark P).test fr (R.map (·.drawn)) = none →
    drawsFit (headClaimMergeKind P).rounds (R.map (·.drawn)) = true →
    headMergeDecide P s (R.map noDigest) = .ok s' → s.here = .head a → a.x = some x →
    Filled a.F x.sV → FreeAbove a.F →
    MergeLive P.lay.lk a.F.next x.sV s'

end ProofFile.Honest.K11
