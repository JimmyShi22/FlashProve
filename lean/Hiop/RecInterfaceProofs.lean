-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecInterfaceProofs.lean: two proofs on index binding of the holographic interactive oracle
proof with a record phase.
In this library's words: proofs of the statements of Hiop/RecInterface.lean: index binding by
explicit lists and for languages (`soundR_iff_at`, `soundR_lang`).










Terms: lean/GLOSSARY.md.
-/
import Hiop.RecInterface
import Hiop.RecKitSound
import Hiop.RecKitHonest

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

theorem soundR_iff_at : Spec.soundR_iff_at := by
  intro I X Wn L Rno wit εs
  constructor
  · rintro ⟨h0, ⟨eR, bR, hR⟩, ⟨εT, bT, hT⟩, ⟨εL, bL, hL⟩, ⟨εB, bB, hB⟩⟩
    exact ⟨eR, εT, εL, εB, ⟨h0, hR, hT, hL, hB⟩, bR, bT, bL, bB⟩
  · rintro ⟨eR, εT, εL, εB, h, bR, bT, bL, bB⟩
    exact ⟨h.noneColl, ⟨eR, bR, h.rcd⟩, ⟨εT, bT, h.sndT⟩, ⟨εL, bL, h.sndL⟩, ⟨εB, bB, h.sndB⟩⟩

theorem soundR_lang : Spec.soundR_lang := by
  intro I X Wn L Rno wit eR εT εL εB h rec
  refine sndBL_of_sndBP X _ (L.batAt rec) L.maxBatchSize L.early L.late _ _ εB ?_ (h.sndB rec)
  rintro x y τ (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, _, hw⟩

variable {I X Wn : Type}

end Iop
