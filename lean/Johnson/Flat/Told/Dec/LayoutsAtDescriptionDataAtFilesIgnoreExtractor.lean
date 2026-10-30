-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFilesIgnoreExtractor.lean: the told record at D⋆
  (Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean) reads no S.ext: so an extractor made of the record can
  be laid into S.ext without a circle.

  **DescriptionDataAtFiles.layoutsByPublicReading_ignoresExtractor**   ({ S with ext := e } : DescriptionDataAtFiles Zk).layoutsByPublicReading c₀ m₀ = S.layoutsByPublicReading c₀ m₀ := rfl
No ∃. It says nothing of what the extractor finds. 
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop (Dig)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

theorem DescriptionDataAtFiles.layoutsByPublicReading_ignoresExtractor (e : (s : IntegerTransformer.Settings) → Commitment → QueryLog → Option (ModelWeights s)) :
    ({ S with ext := e } : DescriptionDataAtFiles Zk).layoutsByPublicReading c₀ m₀ = S.layoutsByPublicReading c₀ m₀ := rfl

end FlashProve

#print axioms FlashProve.DescriptionDataAtFiles.layoutsByPublicReading_ignoresExtractor
