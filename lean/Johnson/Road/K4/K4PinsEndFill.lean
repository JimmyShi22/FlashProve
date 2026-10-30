-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsEndFill.lean: THE THREE LINES ON THE ITEM worth OF `K4MeanEqs`
(Johnson/Road/K4/K4PinsEnd.lean), IN THEIR OWN SHAPES, AT A MEANING WHOSE FIELD worth IS K3's
LAYER's (`fillK3All`, Johnson/Desc/First/Look/K3FillWorth.lean). Glue over
Johnson/Road/K4/K4PinsWorthFill.lean: rewriting by equations on public letters. No draw, no count.

  `WorthTies X L p m x`: THE TIES, ON PUBLIC LETTERS: m is a layers' segment of the public
    parameters with the place x and the smallness test's public parameters · the lookup on the calls
    stands at piece 2
    · K3's numbers of rows and columns of the committed matrix are the reference ones · the
    plan's layout is the public parameters'.
  **`worth_lines`**: under `WorthTies`, "Mg's field worth is `fillK3All X D L Mg0`'s" and "the
    letter msgW of K3 is enc at the witness's cells": the three implications that `K4MeanEqs` asks
    as its fields planes, keys, rider, at rad, arr, oW, wOf := L's, seatT j := L.seat x.link false
    j, q := `pubAt X (m / stepOf X)`.



OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsOfMeans.lean; meant: the assembly of K4's law.
LETTERS: X, D, L, Mg0, Mg, p, m, x, enc, Zt: free.

Limits. K04_law IS NOT PROVED BY THIS. `WorthTies` IS A PREMISE: equations on public letters, each
decidable: none has run. L IS A LETTER.
-/
import Johnson.Road.K4.K4PinsWorthFill
import Johnson.Road.K4.K4PinsEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.First.Look (Sent msgLay layLay layRider attAt layAt tlAt pubAt stepOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3WorthPlanes K3WorthKeys K3WorthRider K3Letters fillK3All)
open Inst.Model.Layout (kRef hRef)

/-- **The ties, on public letters.** -/
structure WorthTies {Cells Tok : Type} (X : Public) (L : K3Letters Cells Tok) (p : Par) (m : ℕ)
    (x : VerifiableInference.Desc.First.Look.Place) : Prop where
  noAtt : attAt X m = none
  place : layAt X m = some x
  tail : tlAt X m = some p.hp.tl
  piece : VerifiableInference.Desc.K3.pieceAt X m false = 2
  rows : L.nr = hRef
  cols : L.nc = 2 ^ kRef
  layout : p.P.y = X.y

variable {P Cells Tok : Type} (X : Public) (D : Sent) (L : K3Letters Cells Tok)
  (Mg0 Mg : Meaning P (Wit Cells Tok MsgT)) (p : Par) (m : ℕ)
  (x : VerifiableInference.Desc.First.Look.Place) (enc : Cells → L.oW.Msg) (Zt : P)

/-- **The three lines on worth, in `K4MeanEqs`' own shapes.** -/
theorem worth_lines (T : WorthTies X L p m x) (hW : Mg.worth = (fillK3All X D L Mg0).worth)
    (hmsg : L.msgW = fun w => enc w.cells) :
    (∀ (t : S) (y : Strs) w,
      K3WorthPlanes (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
        (fun w => nuLay x D L.rad p.hp.tl L.oW L.wOf hRef (2 ^ kRef) (matIx p.P.y).iB
          (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)) t w →
      Mg.worth m 2 "planes" (Zt, t) y w) ∧
    (∀ (t : S) (y : Strs) w,
      K3WorthKeys (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
        (fun w => nuLay x D L.rad p.hp.tl L.oW L.wOf hRef (2 ^ kRef) (matIx p.P.y).iB
          (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w))
        (fun w => Cb.Fo.forK Cb.Gl.E
          (layLay (pubAt X (m / stepOf X)) x.fs x.lm x.F.next x.ns p.hp.tl hRef (2 ^ kRef)) ()
          (Cb.Fo.zext (msgLay x p.hp.tl D L.rad L.oW L.wOf hRef (2 ^ kRef)
            (tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w)))) t w →
      Mg.worth m 2 "keys" (Zt, t) y w) ∧
    ∀ (t : S) (y : Strs) w,
      K3WorthRider (fun s : S => s.fork?) (fun s : S => s.lookHeard?)
        (layRider x (pubAt X (m / stepOf X)) p.hp.tl D L.rad L.oW L.wOf hRef (2 ^ kRef)
          Iop.extNone Unit) x.lm x.F.next (fun _ => ())
        (fun w => tupleW x D L.rad (fun j => L.seat x.link false j.1) L.oW enc L.arr w) t w →
      Mg.worth m 2 "rider" (Zt, t) y w := by
  rw [← T.rows, ← T.cols, T.layout]
  exact ⟨fun t y w h => planes_of_fill X D L Mg0 Mg hW m T.noAtt T.place T.tail T.piece enc hmsg Zt
      t y w h,
    fun t y w h => keys_of_fill X D L Mg0 Mg hW m T.noAtt T.place T.tail T.piece enc hmsg Zt t y w
      h,
    fun t y w h => rider_of_fill X D L Mg0 Mg hW m T.noAtt T.place T.tail T.piece enc hmsg Zt t y w
      h⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.worth_lines
