-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt3Arm.lean: THE COMPOSED MEANING's PARAMETER uA (the stated function at an
attention segment), AT ITS OWNER's TERM. Two definitions.

  `At.uA Zp` := `Att.P.uArm (X Zp)` (Johnson/Desc/First/Att/K05StatedArm.lean).
  `At.𝔇AtArm Zp 𝔇₁`: it laid over a structure 𝔇₁.
ITS OWNER's TERM ANSWERS 0 IN SILENCE at a segment l at which the public parameters hold no
attention plan (`(X Zp).A[l / 2]?`). The named test that shuts it: that option is some at every
attention segment.
Limits. A definition. Nothing on soundness.

-/
import Johnson.P5J.LettersRec
import Johnson.Desc.First.Att.K05StatedArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

/-- The stated function at an attention segment. -/
noncomputable def uA (Zp : ProofFile.Pub) : ℕ → VerifiableInference.Desc.Sound.UFn :=
  VerifiableInference.Desc.First.Att.P.uArm (X Zp)

/-- uA, laid. -/
noncomputable def 𝔇AtArm (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₁ with uA := uA Zp }

end P5J.At
