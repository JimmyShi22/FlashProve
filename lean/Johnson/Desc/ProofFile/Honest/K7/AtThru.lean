-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtThru.lean: the round that names the next token (kind K7), read
through (Honest/Thru.lean). The part reads the public instance alone, and reading through leaves the
public instance as it is, so the lot read through is the same lot at the new letters, and
`replySLot` at any letters, without its simulators, is `replyLot` read through.

  `replyPart_thru`, `replyLot_thru`   the part and the lot, read through
  `replySLot_thru`   the lot with its simulator, without it, is the lot read through

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Rows
import Johnson.Desc.ProofFile.Honest.Thru

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ W₀' Rc Rc' Tr X : Type}

theorem replyPart_thru (g : W₀' → W₀) (rd : Rc' → Rc) :
    Part.thru (Local.thru g rd) (Local.thru g rd)
        (replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) =
      (replyPart : Part (Local W₀' Rc' Inst Tr) (Local W₀' Rc' Inst Tr) X) := rfl

theorem replyLot_thru (g : W₀' → W₀) (rd : Rc' → Rc) :
    HLot.thru (Local.thru g rd) (Local.thru g rd)
        (replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) =
      (replyLot : HLot (Local W₀' Rc' Inst Tr) (Local W₀' Rc' Inst Tr) X) := rfl

/-- **The lot read through is `replySLot` without its simulators.** -/
theorem replySLot_thru (g : W₀' → W₀) (rd : Rc' → Rc) :
    (replySLot (W₀ := W₀') (Rc := Rc') (Tr := Tr) (X := X)).toHLot =
      HLot.thru (Local.thru g rd) (Local.thru g rd)
        (replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.replyPart_thru
#print axioms ProofFile.Honest.replyLot_thru
#print axioms ProofFile.Honest.replySLot_thru
