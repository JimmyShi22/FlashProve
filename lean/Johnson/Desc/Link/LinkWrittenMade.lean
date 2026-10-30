-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkWrittenMade.lean: THE WRITTEN LINK IS MADE: CLOSED THEOREMS, BY THE KERNEL. The doubt behind them: for all that Lean proves, linkDecisionAtParameterFile may say no to all.
  okAt_full | okAt_small       the blocks' rounds' entries ARE the written plan's rounds
  planOk_full | planOk_small   the tests on the plan pass at the written description
  made_full | made_small       linkAt frP recordPlan | linkAt srP smallRecordPlan returns a link
OBJECT: Desc.K15.linkAt (the root's heart) · USER: decWritten_at (made_full) · linkAt_full | linkAt_small (planOk_full | planOk_small) · LETTERS: none. Nothing on soundness.
-/
import Johnson.Desc.Link.LinkWritten

set_option autoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params VerifiableInference.Desc

set_option maxRecDepth 1000000 in
theorem okAt_small : linkRoundsMatchPlan srP smallRecordPlan = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okAt_full : linkRoundsMatchPlan frP recordPlan = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem planOk_small : (linkDescriptionAt srP (linkDeclaredRounds srP) (linkRoundsMatchPlan srP smallRecordPlan)).planOk = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem planOk_full : (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).planOk = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rounds_small : ((linkDescriptionAt srP (linkDeclaredRounds srP) (linkRoundsMatchPlan srP smallRecordPlan)).roundsOf "entry file").toOption.isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rounds_full : ((linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).roundsOf "entry file").toOption.isSome = true := by decide +kernel

theorem made_of {P : P15} {plan : Fmt.Plan} (h1 : (linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).planOk = true)
    (h2 : ((linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).roundsOf "entry file").toOption.isSome = true) : ∃ L, linkAt P plan = .ok L := by
  have hw : (linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).planWord = none := by
    unfold OneChainFileDescription.planWord
    rw [if_pos h1]
  cases hr : (linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).roundsOf "entry file" with
  | error e => rw [hr] at h2; exact nomatch h2
  | ok l =>
    have hd : (linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).dsOf "entry file" = .ok ((_root_.Run.PQ.rds (specOf l)).map TypedOracleCompiler.Run.PQ.ofLib) := by
      unfold OneChainFileDescription.dsOf
      rw [hr]
      rfl
    refine ⟨⟨linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan), (_root_.Run.PQ.rds (specOf l)).map TypedOracleCompiler.Run.PQ.ofLib, (linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)).xsTyped⟩, ?_⟩
    unfold linkAt
    simp only [hw, hd]

/-- **The written link is made, at the full size.** -/
theorem made_full : ∃ L, linkAt frP recordPlan = .ok L := made_of planOk_full rounds_full

theorem made_small : ∃ L, linkAt srP smallRecordPlan = .ok L := made_of planOk_small rounds_small

end Desc.K15

#print axioms Desc.K15.made_full
#print axioms Desc.K15.made_small
#print axioms Desc.K15.okAt_full
#print axioms Desc.K15.planOk_full
#print axioms Desc.K15.okAt_small
#print axioms Desc.K15.planOk_small
