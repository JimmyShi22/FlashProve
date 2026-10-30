-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ClosePin.lean: FROM `K04LawAt` TO `K04Law` (Johnson/Desc/Plain/K04Plain.lean) AT A
PIECE THAT HOLDS K4's BLOCK AND PUTS NO ROUND BEHIND ITS OWN: the pin that `k04_of_at` asks, from a
reader of the pinned part off a statement. One theorem, of a few lines. Glue: `yes_of_out`
(CarriageHeard.lean) laid into `k04_of_at`. No draw, no count.

  `k04Law_of_dec`: let dec read a tuple of messages off a statement. If (hc) what the row reads and
  leaves open (`Letters.ctx`) says of (b, w) at least that the part of w is dec b, and (hd) at a
  yes, under the promise in front, dec reads the same behind as in front, then `K04LawAt` gives
  `K04Law`, at the same errors.

Limits. K04_law IS NOT PROVED BY THIS: `K04LawAt`, hc and hd are premises. dec IS A LETTER, filled
by nobody: meant: the library's decoder with a sample, at the record's own sample (`OMsg.dec`, as in
`PinAt`, Johnson/Desc/Sound/MsgSig.lean): by reading, at that filling of the pins hc holds of the
items alone; at the plain shadow `PIN` (Johnson/Desc/Msg.lean: a member of the list) only beside «no
collision»; part must read the members inside their ranges; hd is then a fact on `behindOf` (the
stored table as it was; what the stage leaves) and on the seat's three setters; hc is a line on the
letter ctx (the three pins). Nothing shows that a dec with hc and hd is there at the real row. USER:
`Plan4K.k04Law_fill` (CloseFill.lean), `RefSeat.k04Law_refFill` (CloseRefFill.lean).
-/
import Johnson.Road.K4.CarriageHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters K04Law K04LawAt k04_of_at)

variable {T Wt Cl Mm : Type} {Fr : Frame}

/-- **`K04Law` from `K04LawAt`**, by a reader of the pinned part that a yes leaves as it was. -/
theorem k04Law_of_dec (L : Seat T) (Sm : Sem Wt) (Lt : Letters T Wt Fr) (part : Wt → Mm)
    (par : Par) (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hback : pc.back = []) (h : K04LawAt L Sm Lt part par bk pc) (dec : T × Fr.E.Str → Mm)
    (hc : ∀ b w, Lt.ctx b w → part w = dec b)
    (hd : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
      dec (behindOf L pc a τ o G) = dec a) :
    K04Law L Sm Lt par bk pc := fun hb hh =>
  k04_of_at L Sm Lt part dec par bk pc h
    (fun a τ b w ha hout hw => by
      obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hh hb hback a b τ hout
      rw [hc _ w hw]
      exact hd a τ fo o G ha hy) hb hh

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04Law_of_dec
