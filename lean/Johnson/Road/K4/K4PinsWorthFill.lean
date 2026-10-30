-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsWorthFill.lean: WHAT K4's ROW CONCLUDES ON THE LOOKUP's PLANES, KEYS AND RIDER
(`K3WorthPlanes`, `K3WorthKeys`, `K3WorthRider` at `nuLay` and `tupleW`:
Johnson/Road/K4/K4PinsPlanes.lean, K4PinsKeys.lean, K4PinsRider.lean) IS WHAT THE ITEM worth SAYS AT
ITS OWNERS' OWN LAYER OF THE TABLE's MEANING (`fillK3All`,
Johnson/Desc/First/Look/K3FillWorth.lean), at a layers' segment. Three theorems: the owners'
equation `worth_at_lay`, and two names' equations (Johnson/Road/K4/K4PinsLayNu.lean). No draw, no
count.

  **`planes_of_fill`**, **`keys_of_fill`**, **`rider_of_fill`**: at a meaning Mg whose field worth
    is
    `fillK3All X D L Mg0`'s: the road's conclusion gives `Mg.worth m 2 "planes" | "keys" | "rider"`,
    from: m is a layers' segment of the record (`attAt X m = none` · `layAt X m = some x` ·
    `tlAt X m = some tl`) · the lookup on the calls stands at piece 2 there · the owners' letter
    msgW is enc at the witness's cells. THE ROAD's LETTERS ARE THE OWNERS': rad, arr, oW, wOf, nr,
    nc := L's · seatT j := L.seat x.link false j · q := `pubAt X (m / stepOf X)`.

STANDS OVER Johnson/Desc/First/Look/K3FillWorth.lean with its cone, which stands in this tree.

OBJECT: `fillK3All`'s field worth. USER: Johnson/Road/K4/K4PinsEndFill.lean; meant: the three lines
on worth of `K4MeanEqs` (Johnson/Road/K4/K4PinsEnd.lean). LETTERS: X, D, L, Mg0, Mg, m, x, tl, enc:
free.

Limits. K04_law IS NOT PROVED BY THIS. IT WILL TURN WHEN THAT LAYER TURNS. L IS A LETTER: which
seats, radius, arr, oW, wOf, nr, nc, msgW are meant is said nowhere. `K4MeanEqs` speaks at
nr := hRef, nc := 2 ^ kRef, tl := the plan's, and at the number of the planes' matrix off the plan's
layout: that L's and the record's are these is not asked here. One direction.
-/
import Johnson.Road.K4.K4PinsLayNu
import Johnson.Desc.First.Look.K3FillWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.First.Look (Sent msgLay layLay layRider attAt layAt tlAt pubAt stepOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3WorthPlanes K3WorthKeys K3WorthRider K3Letters fillK3All
        worth_at_lay worthLay layNu layMu layMs)

variable {P Cells Tok : Type} (X : Public) (D : Sent) (L : K3Letters Cells Tok)
  (Mg0 Mg : Meaning P (Wit Cells Tok MsgT)) (hW : Mg.worth = (fillK3All X D L Mg0).worth) (m : ℕ)
  {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
  (hx : layAt X m = some x) (ht : tlAt X m = some tl)
  (hpc : VerifiableInference.Desc.K3.pieceAt X m false = 2) (enc : Cells → L.oW.Msg)
  (hmsg : L.msgW = fun w => enc w.cells)
include hW hna hx ht hpc hmsg

/-- **The planes.** -/
theorem planes_of_fill (z : P) (t : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthPlanes (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D L.rad tl L.oW L.wOf L.nr L.nc (matIx (pubAt X (m / stepOf X)).y).iB
        (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)) t w) :
    Mg.worth m 2 "planes" (z, t) y w := by
  rw [hW, ← hpc, worth_at_lay X D L Mg0 m hna hx ht]
  unfold worthLay
  rw [if_pos rfl, hmsg]
  have e : (fun w : Wit Cells Tok MsgT => nuLay x D L.rad tl L.oW L.wOf L.nr L.nc
      (matIx (pubAt X (m / stepOf X)).y).iB
      (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)) =
      layNu x (pubAt X (m / stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc
        (fun j => L.seat x.link false j.1) L.arr (fun w : Wit Cells Tok MsgT => enc w.cells) :=
    funext fun w => nuLay_layNu x (pubAt X (m / stepOf X)) D L.rad _ tl L.oW enc L.wOf L.nr L.nc
      L.arr w
  rw [e] at h
  exact h

/-- **The keys.** -/
theorem keys_of_fill (z : P) (t : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthKeys (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D L.rad tl L.oW L.wOf L.nr L.nc (matIx (pubAt X (m / stepOf X)).y).iB
        (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w))
      (fun w => Cb.Fo.forK Cb.Gl.E
        (layLay (pubAt X (m / stepOf X)) x.fs x.lm x.F.next x.ns tl L.nr L.nc) ()
        (Cb.Fo.zext (msgLay x tl D L.rad L.oW L.wOf L.nr L.nc
          (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)))) t w) :
    Mg.worth m 2 "keys" (z, t) y w := by
  rw [hW, ← hpc, worth_at_lay X D L Mg0 m hna hx ht]
  unfold worthLay
  rw [if_neg (by decide), if_pos rfl, hmsg]
  have e : (fun w : Wit Cells Tok MsgT => nuLay x D L.rad tl L.oW L.wOf L.nr L.nc
      (matIx (pubAt X (m / stepOf X)).y).iB
      (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)) =
      layNu x (pubAt X (m / stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc
        (fun j => L.seat x.link false j.1) L.arr (fun w : Wit Cells Tok MsgT => enc w.cells) :=
    funext fun w => nuLay_layNu x (pubAt X (m / stepOf X)) D L.rad _ tl L.oW enc L.wOf L.nr L.nc
      L.arr w
  rw [e] at h
  simp only [tupleW_layMs] at h
  exact h

/-- **The rider.** -/
theorem rider_of_fill (z : P) (t : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthRider (fun s : S => s.fork?) (fun s : S => s.lookHeard?)
      (layRider x (pubAt X (m / stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc Iop.extNone Unit) x.lm
      x.F.next (fun _ => ())
      (fun w => tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w) t w) :
    Mg.worth m 2 "rider" (z, t) y w := by
  rw [hW, ← hpc, worth_at_lay X D L Mg0 m hna hx ht]
  unfold worthLay
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl, hmsg]
  simp only [tupleW_layMs] at h
  exact h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planes_of_fill
#print axioms OnBytes.Road.K4.keys_of_fill
#print axioms OnBytes.Road.K4.rider_of_fill
