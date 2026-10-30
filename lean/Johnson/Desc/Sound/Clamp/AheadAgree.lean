-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Clamp/AheadAgree.lean: two readers of the witness that agree at the entries which
an array's blocks read give the same cells of an array that is read AHEAD of its sending (`cellA`,
Johnson/Desc/Sound/FormsAhead.lean: the cells that the approximate range proof's own run reads
before the oracle message that holds them is sent). One statement and its proof; no definition.

  `cellA_agree`  cellA codes h rd' = cellA codes h rd
Why: as CellAgree.lean, whose `cellOfBlock_agree` it calls.
Limits. Nothing says that two given readers agree at these entries. Nothing on soundness.

-/
import Johnson.Desc.Sound.FormsAhead
import Johnson.Desc.Sound.Clamp.CellAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)

/-- **The cells that are read ahead.** -/
theorem cellA_agree (codes : Codes) (h : K9.Ahead) (rd rd' : ℕ × ℕ → MsgQ)
    (hh : ∀ b J, b ∈ h.A.blocks →
      J < 2 ^ (rowBitsOf h.shape .main + placeBitsOf codes h.shape .main) →
      (K9L.inBlock b (rowBitsOf h.shape .main) (placeBitsOf codes h.shape .main) J : GQ) ≠ 0 →
      rd' h.seat false (J % 2 ^ rowBitsOf h.shape .main) (J / 2 ^ rowBitsOf h.shape .main) =
        rd h.seat false (J % 2 ^ rowBitsOf h.shape .main) (J / 2 ^ rowBitsOf h.shape .main)) :
    cellA codes h rd' = cellA codes h rd := by
  funext i c
  unfold cellA
  congr 1
  refine List.map_congr_left fun b hb => ?_
  exact cellOfBlock_agree b _ _ _ _ (fun J hJ h0 => hh b J hb hJ h0) i c

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.cellA_agree
