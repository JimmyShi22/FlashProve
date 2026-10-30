-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt3HeadArm.lean: THE COMPOSED MEANING's PARAMETER uH (the stated function at the
output head's segment), AT ITS OWNER's TERM. Two definitions.

  `At.uH Zp` := `Kinds.Head.Law.uHeadK6 (X Zp)` (Johnson/Desc/Kinds/Law/StatedHeadArm.lean): no
    parameter but the public parameters.
  `At.𝔇AtHeadArm Zp 𝔇₁`: it laid over a structure 𝔇₁.
IN THE OWNER's TEXT (`nuK6`): 0 at a mask's entry from the number of slots on, and 0 at every
place that is neither a mask's nor a cell's: two defaults that answer in silence; and the numeral 24
(the head's segment).
Limits. Definitions. Nothing on soundness.

-/
import Johnson.P5J.LettersRec
import Johnson.Desc.Kinds.Law.StatedHeadArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

/-- The stated function at the output head's segment. -/
noncomputable def uH (Zp : ProofFile.Pub) : ℕ → VerifiableInference.Desc.Sound.UFn :=
  VerifiableInference.Desc.Kinds.Head.Law.uHeadK6 (X Zp)

/-- uH, laid. -/
noncomputable def 𝔇AtHeadArm (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₁ with uH := uH Zp }

end P5J.At
