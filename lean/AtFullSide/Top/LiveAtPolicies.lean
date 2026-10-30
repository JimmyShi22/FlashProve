-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/LiveAtPolicies.lean: the description's test on the public files, `protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean), says yes at the goals' second named set of public files
(`VerifierAndGoals.zGap`) and at the first (`VerifierAndGoals.storedPublicFiles`) under every policy within four bounds. Calls
alone. No definition: no goal is stated.
Why. The laws that carry the test's verdict along a change of the acceptance policy
(Johnson/LPFPol/) give equal verdicts and do not say which. `theLive_zFull` (LiveAtFull.lean) says
which.
  **`theLive_zGap`**: no premise. By `LPFPol.live_gap_eq_full`
    (Johnson/LPFPol/LiveCorollaries.lean).
  **`theLive_zAt`**: at `VerifierAndGoals.zAt C theta cap` (Johnson/Goal/Files/ScopeAtPolicies.lean), for C <
    2^32, theta ≤ C, cap ≤ 1024 and 2^8 ≤ theta: by `LPFPol.live_in_range_at_stored`. These are all
    files of that form that are in the goals' scope (`VerifierAndGoals.inScope_zAt_iff`).
Limits. A YES OF `protocolDataWellFormed` IS NO SIGN THAT THE VERIFIER ACCEPTS ANY PROOF. It is one of three tests
on the public files that ThreeTests.lean settles side by side; they are not all that are known, and
no theorem says that any list of them is whole. ALL OF IT IS AS GOOD AS `theLive_zFull`
(LiveAtFull.lean), on which every instance here stands. The layout file, the scale file and the
parameter file's five other free numbers are `storedPublicFiles`'s throughout. The files are terms of the Lean
library, made of those written in Ladder/Stored.lean, at the full size alone: no Lean code ties them
to the repository's folder examples/; the example's weights are synthetic. `protocolDataWellFormed` is a fact at a
fixed function, the second hash function `OnBytes.secondHashFunction`, and at the constant `fixedConfigurationDigest` in the
digest's place. WHICH THEOREM SPEAKS WHERE. The soundness theorem at exact match
(`VerifierAndGoals.AtTheName.sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) has the premise
that the files' policy is (256, 256, 0): it speaks at `storedPublicFiles` alone and is silent, for that other
reason, at `zGap` and at every other policy. There the form under the files' policy alone speaks
(`soundUnderPolicy_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean); the four bounds
take in policies at which it says nothing of the counted tokens (theta = C with a large cap: the
docstring of `G8`, Ladder.lean). This file lies in the side library AtFullSide, which is built with
a larger thread stack (lake build AtFullSide). Nothing on soundness, on a binding of the commitment
(the opening form, `BindsWith`), on correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Top.LiveAtFull
import Johnson.LPFPol.LiveCorollaries
import Johnson.Goal.Files.ScopeAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open VerifierAndGoals FlashProve

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap VerifierAndGoals.zAt

/-- **The test says yes at `VerifierAndGoals.zGap`.** -/
theorem theLive_zGap : protocolDataWellFormed (asDescriptionFiles zGap) = true :=
  LPFPol.live_gap_eq_full.trans theLive_zFull

/-- **The test says yes at `storedPublicFiles` under every policy within the four bounds.** -/
theorem theLive_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) : protocolDataWellFormed (asDescriptionFiles (zAt C theta cap)) = true := by
  rw [zAt_form]
  exact LPFPol.live_in_range_at_stored theLive_zFull C theta cap h1 h2 h3 h4

end AtFullSide.Top

#print axioms AtFullSide.Top.theLive_zGap
#print axioms AtFullSide.Top.theLive_zAt
