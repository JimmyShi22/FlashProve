-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstGoes.lean: at the written sizes of the proof file and the written
arms, the routine that `Params.firstPlan` finishes ends well from the empty plan. By the cut: 25
pieces with a link, the piece without, and what follows the frame (ProofFirstSegsA.lean to
ProofFirstSegsE.lean: 27 closed facts by Lean's kernel), joined by `goes_body` (FirstCut.lean); that
a piece which goes from the plan without rounds goes from every plan is `goes_of` (Goes.lean) with
`FrP`. A law file; no running text imports it.

Statements.
  `links_25`, `groups_26`: the written sizes have 25 links and 26 groups: so each of the 26 pieces
    of the frame stands at a group that is there (`segAt` and `lastAt` are `pure ()` beyond the
    list). The 27th piece, `tailOf`, stands at no group.
  `proof_first_goes`: Goes proofSizedFull.set (bodyOf proofSizedFull subW) ().
  `proof_first_returns`: (bodyOf proofSizedFull subW { set := proofSizedFull.set, scope := .request
    }).isOk = true.

Limits. It says that the run ends well, not what it adds. That the written sizes and arms are those
of any public files is not said here. Nothing on soundness.
-/
import Johnson.AtFull.Made.ProofFirstSegsA
import Johnson.AtFull.Made.ProofFirstSegsB
import Johnson.AtFull.Made.ProofFirstSegsC
import Johnson.AtFull.Made.ProofFirstSegsD
import Johnson.AtFull.Made.ProofFirstSegsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.LinkJoin (frP_armRounds frP_pure)

theorem links_25 : proofSizedFull.request.link.length = 25 := by decide +kernel

theorem groups_26 : (reqGroups proofSizedFull.request).toList.length = 26 := by decide +kernel

theorem segs_all : ∀ l, l < 25 →
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList l) () = true
  | 0, _ => seg_0
  | 1, _ => seg_1
  | 2, _ => seg_2
  | 3, _ => seg_3
  | 4, _ => seg_4
  | 5, _ => seg_5
  | 6, _ => seg_6
  | 7, _ => seg_7
  | 8, _ => seg_8
  | 9, _ => seg_9
  | 10, _ => seg_10
  | 11, _ => seg_11
  | 12, _ => seg_12
  | 13, _ => seg_13
  | 14, _ => seg_14
  | 15, _ => seg_15
  | 16, _ => seg_16
  | 17, _ => seg_17
  | 18, _ => seg_18
  | 19, _ => seg_19
  | 20, _ => seg_20
  | 21, _ => seg_21
  | 22, _ => seg_22
  | 23, _ => seg_23
  | 24, _ => seg_24
  | n + 25, h => absurd h (by omega)

/-- **The routine goes from nothing open to nothing open.** -/
theorem proof_first_goes : Goes proofSizedFull.set (bodyOf proofSizedFull subW) () := by
  refine goes_body (fun l hl => ?_) ?_ ?_
  · rw [links_25] at hl
    exact goes_of (frP_segAt proofSizedFull (sub := subW) (fun l m => frP_armRounds _ _) _ l)
      (segs_all l hl)
  · rw [links_25]
    exact goes_of (frP_lastAt proofSizedFull _ 25) last_25
  · exact goes_of (frP_tailOf proofSizedFull (sub := subW) (frP_pure _)) tail_goes

/-- **The run ends well.** -/
theorem proof_first_returns :
    (bodyOf proofSizedFull subW { set := proofSizedFull.set, scope := .request }).isOk = true :=
  proof_first_goes.isOk

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.links_25
#print axioms Johnson.AtFull.Made.groups_26
#print axioms Johnson.AtFull.Made.segs_all
#print axioms Johnson.AtFull.Made.proof_first_goes
#print axioms Johnson.AtFull.Made.proof_first_returns
