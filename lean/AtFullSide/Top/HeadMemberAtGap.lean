-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/HeadMemberAtGap.lean: NOT a law on a distribution, NOT on any sub-protocol, NOTHING
on a file on a disk, NOTHING on whether the verifier accepts any proof: THE HEAD HYPOTHESIS
AT THE FULL SIZE (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean: "the head") HAS A MEMBER, WITH NO PREMISE,
AT THE SECOND OF THE GOALS' TWO NAMED SETS OF PUBLIC FILES AS Ladder/Stored.lean SPELLS THEM
(`VerifierAndGoals.zGap`): as HeadMemberAtFull.lean beside this file has it at the first (`VerifierAndGoals.storedPublicFiles`). Two
joins of the library's own theorems; no definition: no goal is stated. For whoever states something
"under every h : AtMgA ..." and wants it at these two sets without that hypothesis.

  `headMember_zGap`    there are Zp, Np, cF, x at which the head holds at `VerifierAndGoals.zGap`
  `headMember_named`   the same at every Z with `VerifierAndGoals.NamedFiles Z`: Z is `storedPublicFiles` or `zGap`

How a caller spends it: "obtain ⟨Zp, Np, cF, x, h⟩ := headMember_named Z hZ", then its own statement
at h. What it has in the end is a "there are letters at which ...": a bare "there is", as the third
part of `headMember_zFull`; no choice is made among members, and nothing here says how many there
are.

Why here. `theLive_zGap` lies in this side library, which is built with a larger thread stack and
which nothing under lean/Johnson/ imports: so this join, and whatever calls it, lies outside
lean/Johnson/: here, under lean/AtFullSide/.

Called. `P5J.head_of_live`: Johnson/P5J/HeadOfLive.lean. `VerifierAndGoals.filesRead`:
Johnson/Goal/Files/FilesReadProof.lean. `theLive_zGap`: AtFullSide/Top/LiveAtPolicies.lean.
`headMember_zFull`: AtFullSide/Top/HeadMemberAtFull.lean. This file imports a module of the folder
Johnson/Goal/ directly (Johnson.Goal.Files.FilesReadProof).

Limits, after those of the files called, which all hold here. TWO EXAMPLES, at the full size alone:
at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`: not at other files in the goals' scope. Both are terms written
in Ladder/Stored.lean: no Lean code ties them to the repository's folder examples/; the example's
weights are synthetic. ALL OF IT IS AS GOOD AS `theLive_zFull` (AtFullSide/Top/LiveAtFull.lean), on
which the member at `zGap` stands; the one at `storedPublicFiles` stands beside it, on the same two closed facts
on the layout file (`headMember_zFull`). WHICH HEAD: `P5J.AtMgA` (and the `AtMg` that it extends):
not `AtMgR`, and none of the other named conditions that a law takes beside the head. The member
stands at D := `dpZ Z`, r := `theProofRun (asDescriptionFiles Z)`, o := `OnBytes.secondHashFunction`: a statement that
fixes other letters does not meet it. An accept of `protocolDataWellFormed` is no sign that the verifier accepts
any proof. It stands over the makers' texts (fourteen entry tests); E2E/CompleteAsIOPAtNamed.lean
reaches it through AtFullSide/Top/HeadJoins.lean, so a build of the library shows a break. At the
second hash `OnBytes.secondHashFunction`, a fixed function, and at the
constant `fixedConfigurationDigest` in the digest's place, not at the digest of these files. The closed facts beneath
are proved by evaluation in Lean's kernel (`decide +kernel`; the layout file's literal by
`kernel_rfl`, under a thread stack of 128 MB): they have been checked by Lean's own kernel alone: no
independent checker has replayed them. It shows that a premise can be met; it adds nothing to what
follows from that premise. Nothing on soundness, completeness or hiding.

-/
import Johnson.P5J.HeadOfLive
import Johnson.Goal.Files.FilesReadProof
import AtFullSide.Top.LiveAtPolicies
import AtFullSide.Top.HeadMemberAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap

/-- **THE HEAD HAS A MEMBER AT THE THREE FILES OF `VerifierAndGoals.zGap`.** No premise. -/
theorem headMember_zGap :
    ∃ Zp Np cF x, P5J.AtMgA OnBytes.secondHashFunction VerifierAndGoals.zGap (VerifierAndGoals.AtTheName.dpZ VerifierAndGoals.zGap)
      (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.zGap)) Zp Np cF x := by
  obtain ⟨scope, pp, read, _⟩ := VerifierAndGoals.filesRead.other
  exact P5J.head_of_live VerifierAndGoals.zGap scope read theLive_zGap

/-- **The same at each of the goals' two named sets of public files.** -/
theorem headMember_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ Zp Np cF x, P5J.AtMgA OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z)
      (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles Z)) Zp Np cF x := by
  rcases hZ with rfl | rfl
  · exact headMember_zFull.2.2
  · exact headMember_zGap

end AtFullSide.Top

#print axioms AtFullSide.Top.headMember_zGap
#print axioms AtFullSide.Top.headMember_named
