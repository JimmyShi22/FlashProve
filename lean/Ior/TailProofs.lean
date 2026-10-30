-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/TailProofs.lean: proofs of the statements of Ior/Tail.lean.

Main names (statements and hypotheses: Ior/Tail.lean):
  `piece_seq_dec`, `piece_pre`: see their statements in Ior/Tail.lean.

Limits: see Limits in the head of Ior/Tail.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Tail
import Ior.BearsProofs
import Ior.ChainProofs

set_option autoImplicit false

namespace Iop
open Prob IOR
open scoped ENNReal

theorem piece_seq_dec : Spec.piece_seq_dec := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C d e₂ P₁ P₂ qa qb qc h₁ h₂
  exact ⟨good_seq_dec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e₂ _ _ h₁.good h₂.good,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    noTie_seq _ _ _ _ _ _ _ _ h₁.noTie h₂.noTie,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem piece_pre : Spec.piece_pre := by
  intro K Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H A' A B ext P f g m back qi qi' qo hS h hq
  exact ⟨good_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g m back hS h.good,
    fun w x => h.noHid _ _,
    noTie_pre _ _ _ _ _ _ _ f g h.noTie,
    bears_pre _ _ _ _ _ _ _ f g _ _ _ _ h.bears hq⟩

end Iop
