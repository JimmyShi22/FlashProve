-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAllProofs.lean: two small facts on the segments of the model: `plainOK`, `seg_cases`.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2Proofs
import Cb.Gen.Tensor
import Hiop.Enc
import CompileK.GenWit
import Cm.RelBase
import Inst.Model.IndexM
import Cm.SegLayoutPlain
import Cm.SegIdxModel
import Cb.Req.ReqSpec
import Cm.SegLayoutProofs
import Cm.SegLayoutPlainProofs
import Cm.SegIdxModelProofs
import Mathlib.Data.FinEnum

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

theorem plainOK : Hd.plain.OK := lay_figures.2.2.2.2.2

/-- a segment is a feed-forward segment, an attention segment or the head -/
theorem seg_cases {k : ℕ} (hk : k < nSeg) :
    (∃ g < nGr, k = 2 * g) ∨ (∃ g < nGr, k = 2 * g + 1) ∨ k = 24 := by
  have hk : k < 25 := hk
  by_cases h24 : k = 24
  · exact Or.inr (Or.inr h24)
  · by_cases h2 : k % 2 = 0
    · exact Or.inl ⟨k / 2, show k / 2 < 12 by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨k / 2, show k / 2 < 12 by omega, by omega⟩)

end Cm.Seg
