-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/ThreeTests.lean: three tests on the public files that stand before the verifier's
decisions say yes, side by side, at `VerifierAndGoals.storedPublicFiles`, at `VerifierAndGoals.zGap` and at `storedPublicFiles` under every
policy within four bounds. Calls alone. No definition: no goal is stated.
The three. (1) The goals' scope, `VerifierAndGoals.InScope` (Ladder.lean): out of scope the verifier rejects
everything (`verify_evaluate_out`, Johnson/Goal/Tie/VerifyEval.lean). (2) `protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean): where it says no the verifier rejects everything
(`theDescription_dead_all`, Johnson/Goal/Description/DeadParser.lean). (3) The outer match of the
decision of the copy's file (the entry file), `linkDecisionAtFiles Zk := Desc.K15.linkDecisionAtParameterFile Zk.pol`
(Johnson/Goal/Description/LinkDec.lean; Johnson/Desc/Link/LinkWritten.lean): three of its four arms
say no to all, and then the verifier rejects everything (`runs_of_accept`,
Johnson/Goal/Description/AcceptGivesGates.lean: an accept gives a yes of this decision); `protocolDataWellFormed`
does not ask it; in scope it cannot fail (`link_of_scope`): SO THE THREE TESTS ARE TWO HURDLES.
  `link_of_scope`: in scope the fourth arm is taken: `linkDecisionAtFiles (asDescriptionFiles Z)` is the run of the
    copy's file's description at the typed parameters: the law `Desc.K15.decWritten_inScope`
    (Johnson/Goal/Conditions/EntryWrittenLaw.lean).
  `tests_of`: the three side by side, general in the files. **`tests_zFull`**, `tests_zGap`,
    `tests_zAt`: its instances, with no premise but the four bounds.
  `linkGate_of`: so the third gate's value, in scope and live. `linkGate_zFull`, `linkGate_zGap`,
    `linkGate_zAt`.
Limits. THREE PLACES WHERE A TEST ON THE PUBLIC FILES CAN MAKE THE VERIFIER REJECT EVERYTHING ARE
SETTLED SIDE BY SIDE HERE. THEY ARE NOT ALL: there are more, some settled and some not, AND NO
THEOREM SAYS THAT ANY LIST OF THEM IS WHOLE. Of (3) the OUTER MATCH alone is
answered: no theorem here shows that the fourth arm's run ever says yes (`link_yes` does, under
`Meant`, on the Lean prover's view). So at these files a statement "whatever the verifier accepts
is right" is empty FOR NONE OF THESE THREE REASONS; that the verifier accepts some proof there is
not shown. ALL OF IT IS AS GOOD AS `theLive_zFull` (LiveAtFull.lean), on which every instance here
stands. The files are terms of the Lean library, made of those written in Ladder/Stored.lean, at the
full size alone: no Lean code ties them to the top-level folder examples/; the example's weights are
synthetic. `protocolDataWellFormed` is a fact at a fixed function, the second hash `OnBytes.secondHashFunction`, and at the
constant `fixedConfigurationDigest` in the digest's place. WHICH THEOREM SPEAKS WHERE. The soundness theorem at exact
match (`VerifierAndGoals.AtTheName.sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) has the
premise that the files' policy is (256, 256, 0): it speaks at `storedPublicFiles` alone and is silent, for that
other reason, at `zGap` and at every other policy. There the form under the files' policy alone
speaks (`soundUnderPolicy_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean); the four
bounds take in policies at which it says nothing of the counted tokens (theta = C with a large cap:
the docstring of `G8`, Ladder.lean). This file lies in the side library AtFullSide, which is built
with a larger thread stack (lake build AtFullSide). Nothing on soundness, on a binding of the
commitment (the opening form, `BindsWith`), on correctness of extraction, on completeness or on
hiding. `link_yes`: Johnson/Prover/Link/LinkJoinF.lean; premise `Meant`. Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Top.GatesOpen
import Johnson.Goal.Conditions.EntryWrittenLaw
import Johnson.Goal.Description.LinkDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Flat TypedOracleCompiler.Slice OnBytes.Tie
open Desc.K15
open FlashProve (protocolDataWellFormed linkDecisionAtFiles theLinkGate theLinkGate_live)
open VerifierAndGoals (asDescriptionFiles storedPublicFiles zGap zAt filesRead inScope_zAt)

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap VerifierAndGoals.zAt

/-- In scope the outer match of the copy's file's decision takes its fourth arm. -/
theorem link_of_scope {Z : VerifierAndGoals.PublicFiles} (hs : VerifierAndGoals.InScope Z = true) :
    linkDecisionAtFiles (asDescriptionFiles Z) =
      fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  decWritten_inScope hs

/-- The three tests side by side. -/
theorem tests_of {Z : VerifierAndGoals.PublicFiles} (hs : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    VerifierAndGoals.InScope Z = true ∧ protocolDataWellFormed (asDescriptionFiles Z) = true ∧
      linkDecisionAtFiles (asDescriptionFiles Z) =
        fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  ⟨hs, hl, link_of_scope hs⟩

/-- **The three tests say yes at `VerifierAndGoals.storedPublicFiles`.** -/
theorem tests_zFull :
    VerifierAndGoals.InScope storedPublicFiles = true ∧ protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧
      linkDecisionAtFiles (asDescriptionFiles storedPublicFiles) =
        fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  tests_of filesRead.full.1 theLive_zFull

/-- The same at `VerifierAndGoals.zGap`. -/
theorem tests_zGap :
    VerifierAndGoals.InScope zGap = true ∧ protocolDataWellFormed (asDescriptionFiles zGap) = true ∧
      linkDecisionAtFiles (asDescriptionFiles zGap) =
        fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  tests_of filesRead.other.1 theLive_zGap

/-- The same at `storedPublicFiles` under every policy within the four bounds. -/
theorem tests_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    VerifierAndGoals.InScope (zAt C theta cap) = true ∧ protocolDataWellFormed (asDescriptionFiles (zAt C theta cap)) = true ∧
      linkDecisionAtFiles (asDescriptionFiles (zAt C theta cap)) =
        fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  tests_of (inScope_zAt h1 h2 h3 h4) (theLive_zAt h1 h2 h3 h4)

/-- In scope and live, the third gate is that run. -/
theorem linkGate_of {Z : VerifierAndGoals.PublicFiles} (hs : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    theLinkGate (asDescriptionFiles Z) =
      fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  (theLinkGate_live _ hl).trans (link_of_scope hs)

/-- The third gate's value at `VerifierAndGoals.storedPublicFiles`. -/
theorem linkGate_zFull :
    theLinkGate (asDescriptionFiles storedPublicFiles) =
      fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  linkGate_of filesRead.full.1 theLive_zFull

/-- The same at `VerifierAndGoals.zGap`. -/
theorem linkGate_zGap :
    theLinkGate (asDescriptionFiles zGap) =
      fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  linkGate_of filesRead.other.1 theLive_zGap

/-- The same at `storedPublicFiles` under every policy within the four bounds. -/
theorem linkGate_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    theLinkGate (asDescriptionFiles (zAt C theta cap)) =
      fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  linkGate_of (inScope_zAt h1 h2 h3 h4) (theLive_zAt h1 h2 h3 h4)

end AtFullSide.Top

#print axioms AtFullSide.Top.link_of_scope
#print axioms AtFullSide.Top.tests_of
#print axioms AtFullSide.Top.tests_zFull
#print axioms AtFullSide.Top.tests_zGap
#print axioms AtFullSide.Top.tests_zAt
#print axioms AtFullSide.Top.linkGate_of
#print axioms AtFullSide.Top.linkGate_zFull
#print axioms AtFullSide.Top.linkGate_zGap
#print axioms AtFullSide.Top.linkGate_zAt
