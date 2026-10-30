-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldLawBlock.lean: the fold's own law at the sheet's `foldRun`: where the law of
FoldLaw.lean meets the sheet.

Main name:
  `foldRun_cons`: the very fold at b :: bs is the very fold at [b], then the very fold at bs.

Limits: those of Johnson/Desc/Sound/FoldLaw.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldLaw
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

namespace Sound

/-- **The very fold at b :: bs is the very fold at [b], then the very fold at bs.** -/
theorem foldRun_cons (F : Frame) (name : String) (b : Block S Cl) (bs : List (Block S Cl))
    (back : List Fmt.RoundView) (s : S) (R₁ R₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (hne : bs ≠ [])
    (hlen : R₁.length = b.rounds.length)
    (hc : ((b.reads F.ft (R₁.map (·.drawn))).flatMap id).length = c₁.length) :
    foldRun F name (b :: bs) back s ⟨R₁ ++ R₂, c₁ ++ c₂⟩ =
      (foldRun F b.name [b] [] s ⟨R₁, c₁⟩).bind fun s' => foldRun F name bs back s' ⟨R₂, c₂⟩ := by
  have k := foldLaw S Cl F.ft b bs s R₁ (R₂ ++ back) c₁ c₂ hlen hc
  have hE : bs.isEmpty = false := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  simp only [foldRun, chainAt_toOption, List.isEmpty_cons, hE, Bool.false_eq_true, if_false,
    List.append_assoc, List.append_nil]
  exact k

end Sound

end VerifiableInference.Desc
