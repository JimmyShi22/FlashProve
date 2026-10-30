-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerShown.lean: WHAT A SENDING SHOWS: proofs of the three statements of
Johnson/Desc/K14/Law/LedgerShownOwed.lean.

The law of a sending on the shared chain asks of K1's own piece (`sendPiece`,
Johnson/Desc/K1/Law/GoodSend3.lean) that behind it every new member is shown (`Piece.ShownAll`,
Johnson/Desc/Sound/ShownOfData.lean). That file proves it of the pieces that the maker cuts
(`shownOfData`). Here it is carried from the one piece to the other.
  `shownSame`: `ShownAll` reads of a piece its base and its rounds' data alone: two pieces over one
    frame that agree in these two have it together, whatever their blocks, extractors and errors.
  `shownAtSend`: so it goes over from any piece with two rounds to K1's piece at that base and these
    rounds' data.
  `shownAtCut`: so at every description, at every piece of two rounds that the maker cuts of the
    shared chain, K1's piece shows every member of a list whose seats fit.
How. The type of a transcript hangs on the piece's rounds' data, so both pieces are taken apart into
their fields before the two equations are spent; then the two statements are one by unfolding.
Limits. `SeatFits` stays a premise: a test on the plan. `ShownAll` speaks only of a member whose
tree is one that the piece's own stretch sends: of any other member it says nothing, here as there.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerShownOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker _root_.Run
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (sendPiece)
open _root_.Run.PQ (CK)

/-- **`ShownAll` reads of a piece its base and its rounds' data alone.** -/
theorem shownSame : ShownSameOwed := by
  intro C Fr S Cl W S' Cl' W' Xi p q G cs m seat hb hd h
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  have hb' : qbase = pbase := hb
  have hd' : qds = pds := hd
  clear hb hd
  subst hb'
  subst hd'
  exact fun y τ k n sh hj hs => h y τ k n sh hj hs

/-- **From a piece with two rounds to K1's piece** at its base and its rounds' data. -/
theorem shownAtSend : ShownAtSendOwed := by
  intro Fr S Cl W S' Cl' W' Xi p blk base d₁ d₂ c e G cs m seat hb hd h
  have e₁ : (sendPiece (W := W') (F := Fr) blk base d₁ d₂ c e).base = p.base := hb.symm
  have e₂ : (sendPiece (W := W') (F := Fr) blk base d₁ d₂ c e).ds = p.ds := hd.symm
  exact shownSame (ckP .two) Fr S Cl W S' Cl' W' Xi p _ G cs m seat e₁ e₂ h

/-- **The law's premise on what a sending shows**, at the maker's pieces of the shared chain. -/
theorem shownAtCut : ShownAtCutOwed := by
  intro Xi F file D h hs c₁ c₂ Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc p hp
    d₁ d₂ hd S' Cl' W' blk c e cs new hfit x hx
  have hall := (shownOfData Xi F file D h hs c₁ c₂ cs x.1.l x.1.seat (hfit x hx) (ckP .two) Y S₁ S₂
    S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc).2.1 p hp
  exact shownAtSend _ S₂ Cl W S' Cl' W' Xi p blk p.base d₁ d₂ c e F cs x.1.l x.1.seat rfl hd hall

end Desc.K14.Law
