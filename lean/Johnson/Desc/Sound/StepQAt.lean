-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StepQAt.lean: **WHAT THE ROW shared_joint_count's LAWS LEAD TO (stepAt) MEETS THE ONE SENTENCE THAT THE TABLES' GLUE ASKS OF THE SHARED CHAIN's STEP (stepQ), BY UNFOLDING.** One statement, general in every letter.
By report: the tables' Glues.g₂ and "the condition is handed on" both come down to one field of TablesFit (Johnson/P5J/TopTables.lean): stepQ : ∀ k a b, Q₂ k a b → onQ₂ … (k + 1) b ∧ ((∃ w, relQ₂ … (k + 1) b w) → ∃ w, relQ₂ … k a w),
at a free letter Q₂; the row's statement (SharedJointCountRowB.lean) fixes Pl.Q₂ = stepAt …; and, by report, "whether stepAt meets stepQ by unfolding is not held".
  stepQ_at   at Q₂ := stepAt Ns Mg Pm Oc split p l ext, whatever the numbers, meanings, promises, condition, pieces and extractor: that sentence.
Limits. That the field of TablesFit reads so, sign for sign, at its own letters (tiedNumbers · tiedMeaning · ocEnd) is a quotation: that file is not imported, and no Lean here holds the two together. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SharedJointCountRowB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj OnBytes.Params
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

theorem stepQ_at {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (Ns : NumbersS)
    (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt) :
    ∀ k a b, stepAt Ns Mg Pm Oc split p l ext k a b →
      onQ₂ Ns Pm Oc split p l (k + 1) b ∧
        ((∃ w, relQ₂ Ns Mg split p l (k + 1) b w) → ∃ w, relQ₂ Ns Mg split p l k a w) :=
  fun k a _ h => ⟨h.1, fun ⟨w, hw⟩ => ⟨ext k a w, h.2 w hw⟩⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.stepQ_at
