-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/DrawOfGood.lean: THE LENGTHS OF WHAT IS DRAWN (DrawFit,
Johnson/Prover/All/Yes.lean), WHICH THE PROVER's OWN THEOREMS ASK, FOLLOW FROM THE PRINTER's RECORD
ON THE DRAW (GoodOwes, Johnson/Prover/Print/FitsOfGood.lean) at the plan's number of salt bytes, and
the lengths of the copy's leaves' salts.

Main names.
  drawFit_of_good   GoodOwes at salt := saltG S.G · each of the copy's leaves' salts has
    256 + 8 * saltG S.G bits: THEN DrawFit at the input's wire record and lengths.

By: drawFit_tOf (Johnson/Prover/At/OwedAt.lean).

Not shown here: that GoodOwes is met. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FitsOfGood
import Johnson.Prover.At.OwedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop (Dig)
open LPFD.Full (saltG)
open OnBytes.Prover OnBytes.Prover.Print

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

theorem drawFit_of_good {Kap : Type} (c : ByteArray) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC S c₀ m₀)) (capT capL capB : ℕ → ℕ)
    (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (s₁ : ℕ → Bits)
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap)
    (hG : GoodOwes S c₀ m₀ c (saltG S.G) sL bcT bcL bcB capT capL capB i r₁ s₁ d)
    (hs : ∀ j, j < (R S c₀ m₀).protocol.wordLength → (d.s j).length = 256 + 8 * saltG S.G) :
    DrawFit (R S c₀ m₀).queryLayout (R S c₀ m₀).compilerParameters d :=
  drawFit_tOf S c₀ m₀ d sL bcT bcL bcB _ _ _ _ _ _ hG.depthL hs hG.formT hG.coT.fit hG.formL hG.coL
    hG.formB hG.coB.fit

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.drawFit_of_good
