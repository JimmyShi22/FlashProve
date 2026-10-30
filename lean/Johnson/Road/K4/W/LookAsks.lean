-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/LookAsks.lean: CONDITIONAL.

Not shown here. THAT LookAsks HOLDS ANYWHERE: no example is known. WHERE ITS WEIGHT LIES: ν stands
under "there is", so the two clauses "the mask row is ν's" and "the planes' matrix in Mm holds ν's
cells" can be met by make, for any mask row and any Mm: lay ν at these places as they say. THE DEBT
IS THAT, AT SUCH A ν, the rounds rs are what the lookup has heard (HeardIs) and the lookup's three
claims on its planes hold (K3Planes): so that the honest lookup's coins and bits are this mask row
and this matrix. These are the lookup's side's to show; run and cols are public; sized is a clause
on the ledger in front, "F is later than F0" one on the two ledgers; ok is a public test. Nothing on
soundness, on completeness or on any other property.

All that W/PlanesTrue.lean asks beside the run's return and the public facts on the layout, at one
state, in one structure; and from it the field look of `ItemSlots` (W/ItemOfKept.lean): so that
field is no bare hypothesis.

  `LookAsks tl o F mask Mm`   F: the ledger in front of the run "front". There are a ledger F0, a
      number first, rounds rs and an assignment ν of the lookup's places such that: rs are what the
      lookup has heard at F0; F is later than F0; the mask row is ν's; the planes' matrix in Mm
      holds ν's cells; and the lookup's three claims on its planes hold at ν (K3Planes). Besides:
      the lookup's numbers pass their test; F's arrays have its size; the planes' matrix has its
      rows in one run, and at least the planes' columns.
  `look_of_asks`   the field look.
No property is claimed.
-/
import Johnson.Road.K4.W.PlanesTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open OnBytes.Model.Layer (Pub Own matIx)
open OnBytes.Desc.First.K4 (planesParts)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.OnPublicFiles (K3Planes)

/-- **What the lookup's three claims ask, at one state.** This defines a hypothesis; the definition
claims nothing. -/
structure LookAsks (tl : HTailF2) (o : Own) (F : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Mats Cb.Gl.E) :
    Prop where
  /-- what was heard, the mask row, the planes' cells and the lookup's own sentence, at one ν -/
  heard : ∃ (F0 : Fork) (first : ℕ) (rs : TwV.Rounds Cb.Gl.E) (ν : _root_.Fo.Pl → Cb.Gl.E),
    _root_.Fo.HeardIs Reading.gl o.H.fo F0 (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs) ∧
    _root_.Fo.Later F0 F ∧ (mask = fun j => ν (.mask j)) ∧
    (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      Mm (matIx o.v.y).iB r c = ν (.cell r c)) ∧
    K3Planes o.H.fo.shape o.v.y.h.lmb first ν rs
  /-- the lookup's numbers pass their test -/
  ok : FoNums.ok o.H.fo.shape = true
  /-- the ledger's arrays have its size -/
  sized : PscRun.Sized F
  /-- the planes' matrix has its rows in one run -/
  run : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1
  /-- and at least the planes' columns -/
  cols : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k

/-- **The field look of ItemSlots.** CONDITIONAL: on the run's return, on Gr and on every clause of
A. -/
theorem look_of_asks {h : Layer.Shape} {pc : List (List String)} {rd : Layer.Reads}
    {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
    {pts : List (String × Array E)} {D : Dim} {rows : Bool} {P : Pub} {g : ℕ} {F G : Fork}
    {fs : Array Aff} (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    (Gr : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) {mask : ℕ → Cb.Gl.E}
    {Mm : Mats Cb.Gl.E} (A : LookAsks tl o F mask Mm) :
    ∀ pp, planesParts o.v o.H.fo = some pp →
      LookThree Reading.gl (G.worldOf Reading.gl mask (entryTrue tl o Mm)) o pp := by
  obtain ⟨F0, first, rs, ν, hI, h0, hm, h4, hP⟩ := A.heard
  exact look_item hfr Gr Mm hI h0 A.ok A.sized ν hm A.run A.cols h4 hP

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.look_of_asks
