-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7HearsOnceUnder.lean: THE SUB-PROTOCOL THAT SITS AT A PLACE OF THE KIND K7
HEARS ONCE (Law/K7HearsOnce.lean), IN WHATEVER DRESS: general in the dress: whatever accepts only
where the lot's own sub-protocol accepts, with the same state behind. Statements and proofs.

  k7_under_hearsOnce   b.Under x, x a member of ProofFile.h1Own G.
  k7_lot_hearsOnce     b.Under b', b' a sub-protocol of the kind K7 of a lot's list, given as "b' is
                       x.retype, x a member of ProofFile.h1Own G" (IM.lot_K7, IMR/K7Seat.lean, ends
                       in that form).
  hV_of_V              the premise hV from "the plan's vocabulary is the reference's".

WHAT IT IS NOT. UNDER hV (the plan's vocabulary is no larger than the reference's). That a given
sub-protocol of the chain is Under the lot's own is a premise. Nothing on soundness.
LETTERS. No letter stands under "there is" in a conclusion.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K7HearsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model (ppref)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

theorem k7_under_hearsOnce {G : ProofFile.Ground} (hV : G.W.hS.V ≤ ppref.V) {Cl : Type}
    {b : Block S Cl} {x : Block S Unit} (hx : x ∈ ProofFile.h1Own G) (hU : b.Under x) :
    b.HearsOnce (P5J.heardV fun s : S => s) :=
  VerifiableInference.Desc.hearsOnce_of_under hU (h1Own_hearsOnce hV hx)

theorem k7_lot_hearsOnce {G : ProofFile.Ground} (hV : G.W.hS.V ≤ ppref.V) {Cl Cl' : Type}
    {b : Block S Cl} {b' : Block S Cl'} (hb' : ∃ x ∈ ProofFile.h1Own G, b' = x.retype)
    (hU : b.Under b') : b.HearsOnce (P5J.heardV fun s : S => s) := by
  obtain ⟨x, hx, rfl⟩ := hb'
  exact k7_under_hearsOnce hV hx fun s rs gs s' H => hU s rs gs s' H

theorem hV_of_V {G : ProofFile.Ground} (h : G.W.hS.V = 202048) : G.W.hS.V ≤ ppref.V := by
  rw [h]
  decide

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_lot_hearsOnce
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hV_of_V
