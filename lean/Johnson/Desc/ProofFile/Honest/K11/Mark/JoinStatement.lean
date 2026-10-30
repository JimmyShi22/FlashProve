-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/JoinStatement.lean: WHERE THE MARK AT THE MERGE OF THE CLAIMS
ON THE WEIGHTS SAYS NOTHING, AT CHALLENGES THAT THE KIND's DECLARED ROUNDS CAN DRAW, THE CONDITION
`MergeLive` HOLDS BEHIND A YES OF THE KIND's DECISION: STATEMENTS ALONE: two, each a definition of a
proposition. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements.

  `HeadMergeLaterFit`       where the rounds' drawn values fit the kind's declared rounds
                            (`drawsFit`, Honest/Frame.lean): every element that a round from number
                            lk + 2 on has drawn reads other than 0: the round in the further
                            variable draws one, which its entry marks as never 0; the round of the
                            end value draws none
  `HeadMergeLiveOfSilent`   where the mark (`headMergeMark`, Statement.lean of this folder) says
                            nothing at the rounds' drawn values; these fit the declared rounds; the
                            decision says yes from s to s' on the rounds; a, x: the head's own
                            fields and what the head heard, in front; and the slot of the claim's
                            value lies below the ledger's next free number:
                            `MergeLive P.lay.lk a.F.next x.sV s'`
                            (Johnson/Desc/K11/Live/RunStatement.lean)

Limits. The yes is a premise; so is that the drawn values fit; so is the clause on the slot. THE
ROUNDS ARE THOSE ON WHICH THE DECISION RUNS: a member's step shows its decision the view's rounds
without the sealed digest (`noDigest`, Johnson/Desc/Block.lean), while a mark's test and `drawsFit`
are asked at the view's own drawn values: that bridge is not in this file. No thread is named.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.Statement
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)
open Johnson.Desc.First.ForkMerge.Live (MergeLive)

/-- The statement on the last two rounds. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeLaterFit : Prop :=
  ∀ (P : HeadMergeP) (rs : List Fmt.RoundView),
    drawsFit (headClaimMergeKind P).rounds (rs.map (·.drawn)) = true →
    ∀ i r, rs[i]? = some r → P.lay.lk + 2 ≤ i →
      ∀ e ∈ r.drawn.elems.map E.ofTriple, Reading.gl.val e ≠ 0

/-- The statement where the mark says nothing. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeLiveOfSilent : Prop :=
  ∀ (P : HeadMergeP) (fr : List Fmt.Drawn) (s s' : S) (rs : List Fmt.RoundView) (a : HeadOwn)
    (x : OnBytes.Model.Head.Heard),
    (headMergeMark P).test fr (rs.map (·.drawn)) = none →
    drawsFit (headClaimMergeKind P).rounds (rs.map (·.drawn)) = true →
    headMergeDecide P s rs = .ok s' → s.here = .head a → a.x = some x → x.sV < a.F.next →
    MergeLive P.lay.lk a.F.next x.sV s'

end ProofFile.Honest.K11
