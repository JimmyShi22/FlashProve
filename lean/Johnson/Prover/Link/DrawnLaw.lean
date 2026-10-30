-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DrawnLaw.lean: WHAT THE TWO READERS OF A ROUND's FIRST SAMPLED ELEMENT GIVE AT
AN EMPTY LIST: drawnE (Johnson/Prover/Link/FoldSay.lean) and drawnOf
(Johnson/Prover/Link/FormFold.lean) read "elems.headD (0, 0, 0)". Statements and proofs.

  drawnE_empty    at an empty list drawnE gives what it gives at the list of the one element
                  (0, 0, 0)
  drawnE_zero     and that is the field's 0
  readE_drawnOf   drawnOf, read in the field, is drawnE of what the round sampled

Why. The definitions do not reject a list that is too short. At the rounds "FOLD epsilon", "FOLD
round", "BASE lambda" and "BAT" the plan lets the one sampled element be 0 (drawE = 1, drawNZ = 0:
OnBytes/Params/EntryStagesRecord.lean): so the value at an empty list is a value that a typed
challenge can take there.
Not shown here. That a list is never empty where these are read. Nothing on what any value that is
sent discloses. Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldSay
import Johnson.Prover.Link.FormFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice

theorem drawnE_empty (p : List Nat) (t : List Int) (g : Option ByteArray) :
    drawnE ⟨[], p, t, g⟩ = drawnE ⟨[(0, 0, 0)], p, t, g⟩ := rfl

theorem drawnE_zero (p : List Nat) (t : List Int) (g : Option ByteArray) :
    drawnE ⟨[], p, t, g⟩ = 0 := readE_zero

theorem readE_drawnOf (r : Fmt.RoundView) : readE (drawnOf r) = drawnE r.drawn := rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.drawnE_empty
#print axioms Johnson.Prover.Link.drawnE_zero
#print axioms Johnson.Prover.Link.readE_drawnOf
