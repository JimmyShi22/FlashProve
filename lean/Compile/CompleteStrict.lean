-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CompleteStrict.lean: the strict-format check on the openings of external positions
(`strictExt`, Compile/Bcs.lean) passes if every opening is at a position that is read and has a salt
of exactly sMT bits (`strictExt_of`). External: of the external strings (`ExtSpec`, Iop/InteractiveOracleProof.lean):
oracles that are fixed before the first message.
-/
import Compile.CompleteAcc

set_option autoImplicit false

noncomputable section

namespace Compile.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ}

theorem strictExt_of {sMT : ℕ} {E : ExtSpec} (we : WireE E) {isRead : E.Pos → Bool}
    {g : E.Pos → Option (Opening lam E.Sym)}
    (h : ∀ p op, g p = some op → isRead p = true ∧ op.salt.length = sMT) :
    strictExt sMT we isRead g = true := by
  unfold strictExt
  refine List.all_eq_true.2 fun p _ => ?_
  split
  · rfl
  · rename_i op hop
    obtain ⟨h1, h2⟩ := h p op hop
    simp [h1, h2]

end Compile.Cmpl

