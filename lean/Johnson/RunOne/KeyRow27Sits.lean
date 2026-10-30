-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow27Sits.lean: K14_sits, THE KEY FILE's HALF, AT THE PLACE 7 OF THE SHARED CHAIN
("LIN zeta"): the seating substituted
into the premise hb of row 2.7's laws (Johnson/RunOne/KeyRow27Chance.lean: zeta_half₂_at | _seat;
KeyRow27Number.lean: _rounds | _key).
Beside Johnson/RunOne/KeyK14Sits.lean (the places 1 · 2 · 4 · 5), in its form.

OBJECT   (Key.descriptionFromSource X N P).shared.blocksInOrder[7]
USER     zeta_half₂_at | _seat | _rounds | _key's premise hb, at the block b that the frame's call
hands («(c₂ :: k₂)[7]? = some b»)
  sits7_of_seating   from any seating «flat[1 + j]? = some (seat b)»: whatever lies at flat[7] has
  linZeta for its yes
  hb_of_flat7        at the key file's description, by shared_at_blocks

NOT HERE: that blocks (p14At X P) can be said (planOk) · that the maker's piece number 7 holds held
of that block at one round.
A tie of a law to the constant that the seat calls. Nothing on soundness.

-/
import Johnson.RunOne.KeyK14Sits
import Johnson.RunOne.KeyRow27Chance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14 (P14 blocks linZeta)

/-- **From any seating**: whatever lies at the place 7 has linZeta for its yes. -/
theorem sits7_of_seating {Cl : Type} (Q : P14) (l : List (Block St₂ Unit)) (h : blocks Q = some l)
    (flat : List (Block St₂ Cl))
    (hs : ∀ (j : Nat) (b : Block St₂ Unit), l[j]? = some b → flat[1 + j]? = some (seat b))
    (b : Block St₂ Cl) (hb : flat[7]? = some b) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' → linZeta d rs = some d' := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_blocks Q l h
  obtain rfl : seat b7 = b := Option.some.inj ((hs 6 b7 rfl).symm.trans hb)
  exact zeta_hb Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b7) rfl

/-- **K14_sits, the key file's half, at the place 7.** -/
theorem hb_of_flat7 (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (l : List (Block St₂ Unit))
    (h : blocks (p14At X P) = some l)
    (b : Block St₂ _) (hb : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' → linZeta d rs = some d' := by
  refine sits7_of_seating (p14At X P) l h _ (fun j c hc => ?_) b hb
  rw [shared_at_blocks X N P l h]
  exact getElem?_seated seat _ l _ _ j c hc

end Johnson.RunOne.KeyRows23
