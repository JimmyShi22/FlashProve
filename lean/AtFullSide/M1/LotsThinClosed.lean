-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsThinClosed.lean: the rule's door on the book at K1's senders on the first chain, with
no premise left but scope, the gate and the maker's return: the opening's clause is
clear_written (AtFullSide/K1/BookAtOpening.lean). How far it speaks: the head of LotsDoor.lean.
-/
import AtFullSide.M1.LotsThin
import AtFullSide.K1.BookAtOpening

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest OnBytes.SendSim.Seat

variable {W₀ Rc Tr X₀ X' : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
  {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

/-- **THE DOOR.** -/
theorem door_closed (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    ∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
      lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true :=
  door_of_clear (AtFullSide.K1.clear_written (B := aheadBook) rfl) hS hL h

end AtFullSide.M1

#print axioms AtFullSide.M1.door_closed
