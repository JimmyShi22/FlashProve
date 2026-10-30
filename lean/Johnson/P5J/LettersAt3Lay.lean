-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt3Lay.lean: THE COMPOSED MEANING's PARAMETER uL (the stated function at a
feed-forward segment), AT ITS OWNER's TERM. Definitions.

  `At.names3 Zp l`: the names of segment l's arrays, off the built segments of the public
    parameters: TYPED HERE, to the letter of the owner's post on its "meant filling".
  `At.uL Zp` := `OnBytes.Road.K4.uLAt (X Zp) (names3 Zp)` (Johnson/Road/K4/ULayAt.lean).
  `At.𝔇AtLay Zp 𝔇₁`: it laid over a structure 𝔇₁.
TWO DEFAULTS ANSWER IN SILENCE: in the owner's term `(Look.tlAt X l).getD {}` (the empty data of a
closing part where the public parameters hold none at l); in the meant filling `.getD #[]` (no names
where the list of built segments has no entry l). The named tests that shut them: `(Look.tlAt (X Zp)
l).isSome` and `(Zp.made.p.built.links[l]?).isSome` at every feed-forward segment l.
Limits. Definitions. Nothing on soundness.

-/
import Johnson.P5J.LettersRec
import Johnson.Road.K4.ULayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

/-- The names of a segment's arrays. -/
def names3 (Zp : ProofFile.Pub) (l : ℕ) : Array (ℕ × String) :=
  ((Zp.made.p.built.links[l]?).map (·.arrayOf)).getD #[]

/-- The stated function at a feed-forward segment. -/
noncomputable def uL (Zp : ProofFile.Pub) : ℕ → VerifiableInference.Desc.Sound.UFn :=
  OnBytes.Road.K4.uLAt (X Zp) (names3 Zp)

/-- uL, laid. -/
noncomputable def 𝔇AtLay (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₁ with uL := uL Zp }

end P5J.At
