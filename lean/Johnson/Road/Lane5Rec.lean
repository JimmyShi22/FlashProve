-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5Rec.lean

How a lookup reads its own record of public numbers (OnBytes.Model.Forest.Shape): the number n of a
call (it has 2^n keys) and a row of a call's table. The lookup's block claims before itself
(Cb.Fo.forIn, OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; written out as Port.jIn,
OnBytes/Tie/Pv/Lookup/Shift/ShiftQLay.lean), beside its caller's own joint: for every k below h.NC:
InTable (nOf h k) (kOf h k) (the caller's key vector of call k) (the rows tauN h k of call k's
table). This file imports none of the lookup's files. It types two of the three readings with the
bodies that they have there, by a reading; the third, kOf, has the body of kN
(OnBytes/Tie/Pv/Lookup/Ends/Joint.lean). Nothing here compiles them with the lookup's own.

Main definitions and theorems:
* "nF", "tauF": the readings. Used at attention (Johnson/Road/Lane5ForIn.lean) and at the layers
  (Johnson/Road/Lane5ForInG.lean). At the head: Johnson/Road/Ends/HeadForIn.lean.
* "tauF_eq": below the number of calls tauF is the tauN of OnBytes/Tie/Pv/Lookup/Ends/Joint.lean.
  (Beyond it tauF reads the default call's table, tauN is 0.)

-/
import OnBytes.Tie.Pv.Lookup.Ends.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.L5

open OnBytes.Ends

/-- n of the lookup's call c, with the body of the lookup's files' nOf. -/
def nF (h : Model.Forest.Shape) (c : ℕ) : ℕ := ((h.calls[c]?).map (·.n)).getD 0

/-- Row t of call c's table as a number, with the body of the lookup's files' tauN. -/
def tauF (h : Model.Forest.Shape) (c t : ℕ) : ℕ := ((h.calls.getD c {}).tauAt t).toNat

/-- Below the number of calls the two readings of a table's row are one. -/
theorem tauF_eq {fs : Model.Forest.Shape} {k : ℕ} (hk : k < fs.calls.size) (t : ℕ) :
    tauF fs k t = tauN fs k t := by
  unfold tauF tauN
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rfl

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.tauF_eq
