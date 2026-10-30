-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqCellsProofs.lean: one lemma on a segment's conditions (`holds_congr`).

Terms: lean/GLOSSARY.md.
-/
import Hiop.Chain
import Mathlib.Algebra.BigOperators.Fin
import Cb.Req.ReqSpecProofs
import Cb.Gen.CodeProofs
import Cb.Gen.CodeProofsComp
import Blocks.ClosingBlock
import Blocks.StageMap
import Blocks.VecAppend
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cb.Req
open Blocks Iop Prob Hiop
open scoped ENNReal

variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Under the hypotheses below, the conditions of a segment depend on the matrices only at the
places that it reads. -/
theorem holds_congr {X : Type} {S : SegSpec X F E} {Φ : IdxFmt F} {x : X} {W : ℕ → ℕ → F}
    {A A' : ℕ → ℕ → ℕ → E} (hw : S.WF Φ)
    (h : ∀ p ∈ S.places, A p.1 p.2.1 p.2.2 = A' p.1 p.2.1 p.2.2) (hA : S.Holds Φ x W A) :
    S.Holds Φ x W A' := by
  refine ⟨fun f hf b hb => ?_, fun q hq b hb => ?_⟩
  · rw [← fam_val_congr X F E f Φ x W A A' (hw.1 f hf) (fun p hp => h p (Or.inl ⟨f, hf, hp⟩)) b hb]
    exact hA.1 f hf b hb
  · rw [← fam_val_congr X F E q.1 Φ x W A A' (hw.2 q hq)
        (fun p hp => h p (Or.inr ⟨q, hq, hp⟩)) b hb]
    exact hA.2 q hq b hb

end Cb.Req
