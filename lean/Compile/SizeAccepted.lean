-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SizeAccepted.lean: what the strict-format check says of the openings of external positions
(words of this library: lean/GLOSSARY.md).

  `of_strictExt`   For a well-formed wire record (`WireE.OK`, Iop/Wire.lean): where the
                   strict-format check (`strictExt`, Compile/Bcs.lean) passes, every opening is at a
                   position that is read and has a salt of exactly sMT bits.

Limits: it does not prove that an accepted proof obeys a size bound.
-/
import Compile.SizeHonest
import Compile.GlueBinding

set_option autoImplicit false

noncomputable section

namespace Compile.SizeA
open Iop Rom Compile.Cmpl Compile.SizeH

variable {I X : Type} {lam K : ℕ}

/-! ## What the check says -/

theorem of_strictExt {sMT : ℕ} {E : ExtSpec} {we : WireE E} (hw : we.OK) {isRead : E.Pos → Bool}
    {g : E.Pos → Option (Opening lam E.Sym)} (h : strictExt sMT we isRead g = true) (p : E.Pos)
    (op : Opening lam E.Sym) (hop : g p = some op) :
    isRead p = true ∧ op.salt.length = sMT := by
  have h1 := List.all_eq_true.1 h p (hw.complete p)
  simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

end Compile.SizeA

