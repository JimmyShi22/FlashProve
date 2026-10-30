-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdProofs.lean: the proofs of the statements of Cb/Obj/LdObjectThird.lean.

An assembly: each clause is a theorem of one of these files, at "within a third":
Cb/Ld/LdWfThird.lean, Cb/Ld/LdWfFull.lean (weights-formedness), Cb/Obj/LdObjectThirdTests.lean (the
test, the link), Cb/Obj/LdObjectTowerThird.lean (towers), Cb/Obj/LdObjectWfRows.lean (the rest of
the plan), Cb/Obj/LdObjectWf.lean (the line on budgets),
Cb/Obj/LdObjectThirdErr.lean,
Cb/Obj/LdObjectErr.lean, Cb/Ld/LdWfList.lean (errors). Nothing is defined here that a statement
reads.

Limits: what the head of Cb/Obj/LdObjectThird.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThird
import Cb.Obj.LdObjectThirdTestsProofs
import Cb.Ld.LdWfList

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- the whole test of a test within a third is a tail -/
theorem LdRunD.In3.tail {E : Type} [Field E] [Fintype E] {S : Sig E} {D : LdRunD S} (h : D.In3) :
    D.T.OK D.t := by
  obtain ⟨Tw, d, hT, ht, -, -, -, hTw⟩ := h
  rw [hT, ht]
  exact ldTowG3_tail E D.B S D.G D.Sb D.sl D.Z Tw hTw

theorem ldIn3_ok : Spec.ldIn3_ok := by
  intro E _ _ S D h
  obtain ⟨Tw, d, hT, ht, hL, hG, hZ, hTw⟩ := id h
  exact ldT3_run E S D d hG hL hZ h.tail

end Cb
