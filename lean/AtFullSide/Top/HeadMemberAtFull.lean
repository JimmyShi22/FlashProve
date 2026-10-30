-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/HeadMemberAtFull.lean: the head has a member at the three full-size public files as
Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`), with no premise.

What it says. `headMember_zFull`: the test `protocolDataWellFormed` accepts at `asDescriptionFiles storedPublicFiles`; the named condition
`P5J.rowsRead` holds at `storedPublicFiles`; and there are Zp, Np, cF, x with `P5J.AtMgA secondHashFunction storedPublicFiles (dpZ
storedPublicFiles) (theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x`: the head has a member. It is
`headMember_zFull_of_two` (Johnson/AtFull/Top/HeadAtFull.lean) with its two premises shown: the key
file's maker returns (`theKeyLaid_zFull_returns`, AtFullSide/Planner/KeyLaidReturns.lean) and the
proof file's maker returns (`proofLaid_zFull`, Johnson/AtFull/Top/LiveAtZFull.lean, at the two
closed facts on the layout file: `lay_size`, AtFullSide/Layout/Size.lean; `layoutRead_full`,
AtFullSide/LayoutRead/Full.lean).

What it is for. Theorems of the library that speak under the head, or under an accept of `protocolDataWellFormed`,
are not empty at these three files for want of that premise: it is met there. That the verifier
accepts any proof at these files is not shown, from an honest prover (completeness) or from anybody.
A run of Lean's evaluator can show an accept of `protocolDataWellFormed` too, but proves nothing; this is a
theorem.

Why here. The two closed facts on the layout file stand over one constant (`lay_chars`,
AtFullSide/Layout/TieRfl.lean) that was seen to fail in Lean's kernel at the default thread stack
and passes at 128 MB: so they, and what calls them, stand in a side library, built with a larger
thread stack. Nothing under lean/Johnson/ imports it.

Limits. ONE EXAMPLE, at the full size alone: at `VerifierAndGoals.storedPublicFiles` alone: not at other files in the
goals' scope, not at the files whose policy has limits (`VerifierAndGoals.zGap`). `VerifierAndGoals.storedPublicFiles` is three
terms written in Ladder/Stored.lean: no Lean code ties them to the top-level folder examples/; the
example's weights are synthetic. WHICH HEAD: `P5J.AtMgA` (and the `AtMg` that it extends): not
`AtMgR` (the facts on every reached state), and none of the other named conditions that a law takes
beside the head. WHAT THE MEMBER IS: no proof and no request: Zp, Np, cF and x are what the makers
return at these three files, made from the public files alone, and there is no other. ONE FACT, NOT
THREE: the second and third parts follow from the first at all files in scope (`P5J.owed_of_live`,
`P5J.head_exists_at_name`). Of the verifier's tests on the public files the statement holds
`protocolDataWellFormed`, and the scope and the files' reading as fields of the member; the outer match of the
entry file's decision is not in it. An accept of `protocolDataWellFormed` is no sign that the verifier accepts any
proof: no key file, entry file or proof file is read here, and whether the verifier's three
decisions accept one is not said. It stands over the makers' texts (fourteen entry tests);
E2E/KeyStandFull.lean imports it, so a build of the library shows a break. At the second hash
`OnBytes.secondHashFunction`, a fixed
function, and at the constant `fixedConfigurationDigest` in the digest's place, not at the digest of these files. The
closed facts beneath are proved by evaluation in Lean's kernel (`decide +kernel`; the layout file's
literal by `kernel_rfl`, Johnson/Unfolds/KernelRfl.lean, under a thread stack of 128 MB). They have
been checked by Lean's own kernel alone: no independent checker has replayed them. It shows that a
premise can be met; it adds nothing to what follows from that premise. Nothing on soundness.

-/
import Johnson.AtFull.Top.HeadAtFull
import Johnson.AtFull.Top.LiveAtZFull
import AtFullSide.Planner.KeyLaidReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open VerifierAndGoals FlashProve
open VerifierAndGoals.AtTheName (dpZ)

/-- **THE HEAD HAS A MEMBER AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`.** No premise. -/
theorem headMember_zFull :
    protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧ P5J.rowsRead storedPublicFiles ∧
      ∃ Zp Np cF x,
        P5J.AtMgA OnBytes.secondHashFunction storedPublicFiles (dpZ storedPublicFiles) (theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x := by
  obtain ⟨_, _, _, _, hK⟩ := AtFullSide.Planner.theKeyLaid_zFull_returns
  obtain ⟨_, hP⟩ := _root_.AtFull.Top.proofLaid_zFull Johnson.Unfolds.Layout.lay_size
    Johnson.AtFull.LayoutRead.layoutRead_full
  exact _root_.AtFull.Top.headMember_zFull_of_two hK hP

#print axioms AtFullSide.Top.headMember_zFull

end AtFullSide.Top
