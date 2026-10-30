-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/KeptOfYes.lean: `KeptAtS` FROM A YES OF THE PIECE, IN THE ROAD's OWN LETTERS.
`kept_atS` (KeptAtS.lean) starts from a yes of the block's `decide`; the road's tops have a `Yes`
(CarriageHeard.lean: what the seat finds of the lookup; the rounds fit and are small; the hearing's
return) and the statement behind as `behindOf` lays it by the seat's three setters. Statements and
proofs, at the seat `seatS` (Johnson/Desc/First/K4/SeatS.lean): calls, no new argument.

  `lay_of_look`: where `seatS.look s` finds a record fo, s stands in a layers' link that holds fo.
  `kept_of_hear`: where `seatS.look s = some fo` and K4's plain hearing returns (o, G, u) from the
    seat's ledger, at any tape: `KeptAtS p s` of the record with G, o and "nothing owed" laid by the
    seat's setters.
  **`kept_of_yes`**: `Yes seatS par pc a τ fo o G → KeptAtS par a.1 (behindOf seatS pc a τ o G).1`.
  `rest_of_yes`: so `Rest a.1 (behindOf seatS pc a τ o G).1` (seven of the record's nine fields and
    four readers of the link stay; a layers' link stays one, with its context and what it holds of
    the lookups), and the stored table is as it was (by the definition of
    `behindOf`).

Limits. «A YES OF THE PIECE» IS HERE THE RECORD `Yes` (CarriageHeard.lean) AT A PIECE pc THAT IS A
LETTER: nothing in this file ties pc to K4's block. From a yes of a piece's verifier to a `Yes` goes
`yes_of_out`, under three premises: the piece holds `below bk`; bk hears as K4's own block at the
seat (`HearsAs`); the piece puts no round behind (pc.back = []). ONE DIRECTION, FROM A YES. Of a
`Yes` only `look` and `hears` are spent. Nothing on what the stage leaves of the trees (`sLeft`).
Those of KeptAtS.lean. Nothing on soundness.
-/
import Johnson.Road.K4.KeptAtS
import Johnson.Road.K4.CarriageHeard
import Johnson.Desc.First.K4.SeatS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par hearFl seatS seatS_fork seatS_laid hearFl_later Rest rest_of_laid)
open OnBytes.Desc.First.K4.Slots (hear_fills own_fo hear_fresh)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- Where the seat finds what the lookup returned, the record stands in a layers' link. -/
theorem lay_of_look {s : S} {fo : Forest.Heard} (h : seatS.look s = some fo) :
    ∃ a : LayOwn, s.here = .lay a ∧ a.fo = some fo := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  cases here with
  | lay a => exact ⟨a, rfl, h⟩
  | _ => cases h

/-- Where the seat finds what the lookup returned (hl) and the hearing returns from the seat's
ledger (hh): `KeptAtS` of the record that the seat's three setters lay. -/
theorem kept_of_hear {p : Par} {s : S} {fo : Forest.Heard} {o : Own} {G : Fork} {tp u : Tape}
    (hl : seatS.look s = some fo)
    (hh : hearFl { p.P with tokv := seatS.tokv s } p.hp p.g fo (seatS.fork s) tp =
      some (o, G, u)) :
    KeptAtS p s (seatS.setOwed (seatS.setOwn (seatS.setFork s G) o) none) := by
  obtain ⟨a, ha, hfo⟩ := lay_of_look hl
  rw [seatS_fork ha] at hh
  rw [seatS_laid ha]
  have hh' : hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F tp = some (o, G, u) := hh
  exact ⟨a, fo, o, G, ha, hfo, rfl, hearFl_later hh', rfl, rfl, rfl, rfl,
    rest_of_laid G (some o) none ha, own_fo hh',
    fun hS => ⟨hear_fills hS hh', hear_fresh hS hh'⟩, _, _, hh'⟩

variable {Wt Cl : Type} {Fr : Frame}

/-- **From a yes of the piece.** -/
theorem kept_of_yes {par : Par} {pc : Piece (ckP .two) Fr S Cl Wt} {a : S × Fr.E.Str}
    {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    (y : Yes seatS par pc a τ fo o G) : KeptAtS par a.1 (behindOf seatS pc a τ o G).1 :=
  kept_of_hear y.look y.hears

/-- What a yes leaves of the record, and the stored table. -/
theorem rest_of_yes {par : Par} {pc : Piece (ckP .two) Fr S Cl Wt} {a : S × Fr.E.Str}
    {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    (y : Yes seatS par pc a τ fo o G) :
    Rest a.1 (behindOf seatS pc a τ o G).1 ∧ (behindOf seatS pc a τ o G).2.1 = a.2.1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := kept_of_yes y
  exact ⟨hR, rfl⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.kept_of_hear
#print axioms OnBytes.Road.K4.kept_of_yes
#print axioms OnBytes.Road.K4.rest_of_yes
