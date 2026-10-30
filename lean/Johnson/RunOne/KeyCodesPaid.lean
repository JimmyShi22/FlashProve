-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCodesPaid.lean: THEOREMS. **KeyCodesStay.lean's one premise is paid, AND NO PREMISE IS LEFT**: the proximity test's seat at the ranges only grows the statement: keyD_grows_yes (Johnson/RunOne/Law/K12GrowsYes.lean: over
k12_grows (Johnson/Desc/K12/Law/GrowsTest.lean), which has no premise but the yes, and same_k12 (Johnson/RunOne/Law/RngAnyCl.lean), which carries the law from Cl := Unit to the key file's claims), CALLED.
So, at EVERY X N P: chain 1 keeps «a statement only grows»; at every record that the chain reaches the statement has grown out of the start's; the carried codes are the plan's.
OBJECT. Key.rangesTest (Key.enterRanges one) Key.leaveRanges N · Key.firstChain · (Key.descriptionFromSource X N P).first. USER. As KeyCodesStay.lean's. LETTERS. one · D · told · set · N; X · N · P · D.
  ranges_grows        Decides (By Grows st₁) (the ranges' test's seat)
  chain1_grows        **ChainKeeps (By Grows st₁) (Key.firstChain one D told set N)** · first_grows: at (Key.descriptionFromSource X N P).first
  codes_at_reached₁ | grows_at_reached₁   **Hist₁ (Key.descriptionFromSource X N P) D k a → (stAt a).codes = X.Y.k.oneTime.codes, for every k**; and Grows from the start's statement
What is not claimed. Chains 2 | 3 (KeyCodesLater.lean). The groups' members against the plan. Nothing on soundness.

-/
import Johnson.RunOne.KeyCodesStay
import Johnson.RunOne.Law.K12GrowsYes

set_option autoImplicit false

namespace Johnson.RunOne.KeyCodes

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block Chain Grows)
open VerifiableInference.Desc.Ground (GroundKeeps By groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps)
open LPFD (Hist₁)

/-- **The proximity test's seat at the ranges only grows the statement**: keyD_grows_yes, in the frame's words. -/
theorem ranges_grows (one : OneTime) (N : H2U.PlaceNums) : Decides (By Grows st₁) (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim) :=
  Johnson.RunOne.Law.K12GrowsYes.keyD_grows_yes one N

/-- **Chain 1 keeps «a statement only grows».** -/
theorem chain1_grows (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) : ChainKeeps (By Grows st₁) (firstChain one D told set N) :=
  chain1_keeps groundKeeps_grows one D told set N (ranges_grows one N)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Chain 1 of the description keeps «a statement only grows».** -/
theorem first_grows : ChainKeeps (By Grows st₁) (descriptionFromSource X N P).first := chain1_grows _ _ _ _ _

/-- **The carried codes are the plan's at every record that the first chain reaches.** -/
theorem codes_at_reached₁ (D : OnBytes.Maker.WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : (stAt a).codes = X.Y.k.oneTime.codes :=
  codes_reached₁ D (ranges_grows _ N) k a h

/-- And the statement there has grown out of the start's. -/
theorem grows_at_reached₁ (D : OnBytes.Maker.WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : Grows { codes := X.Y.k.oneTime.codes } (stAt a) :=
  grows_reached₁ D (ranges_grows _ N) k a h

end Johnson.RunOne.KeyCodes

#print axioms Johnson.RunOne.KeyCodes.ranges_grows
#print axioms Johnson.RunOne.KeyCodes.chain1_grows
#print axioms Johnson.RunOne.KeyCodes.first_grows
#print axioms Johnson.RunOne.KeyCodes.codes_at_reached₁
#print axioms Johnson.RunOne.KeyCodes.grows_at_reached₁
