-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/LookCols.lean: CONDITIONAL.

Not shown here. THAT WHAT THE LOOKUP HAS HEARD HAS THE LAYOUT's SHAPE: a hypothesis (hs; LookLeft's
field shape). THE OTHER THREE FIELDS OF LookLeft are the lookup's side's to show. No example is
known of any. Where K4Ground holds: the head of W/Ground.lean. Nothing on what the planes' matrix
holds. Nothing on soundness, on completeness or on any other property. No property is claimed.

The two public clauses of `LookAsks` (W/LookAsks.lean), run and cols, taken out of it: from the
public facts on the layout (K4Ground, W/Ground.lean) and one equation of shapes. A layout's kbm is
the number of the planes' columns at its own shape of the lookup, by the library's `layout_kbm`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean).

  `cols_of_shape`   the planes' columns fit the planes' matrix in the smallness test's list.
  `LookLeft tl o F mask Mm`   what is left of LookAsks: its fields heard, ok, sized, to the letter;
      and the equation of shapes.
  `lookAsks_of_left`   LookAsks from LookLeft and K4Ground.
-/
import Johnson.Road.K4.W.LookRun
import Johnson.Road.K4.W.LookAsks
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open OnBytes.Model.Layer (Own matIx)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.OnPublicFiles (K3Planes)

/-- **The planes' columns fit.** CONDITIONAL: on G and hs. -/
theorem cols_of_shape {h : Layer.Shape} {pc : List (List String)} {v : Layer.Env}
    {rd : Layer.Reads} {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    {tl : HTailF2} {H : Layer.Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun} {D : Dim}
    (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (hs : H.fo.shape = v.y.fo) :
    planeCols H.fo.shape v.y.h.lmb ≤ (tl.mats.getD (matIx v.y).iB {}).k :=
  cols_of_ground G (by rw [hs, _root_.Fo.PlaneMatG.layout_kbm G.lay])

/-- **What is left of LookAsks.** This defines a hypothesis; the definition claims nothing. -/
structure LookLeft (tl : HTailF2) (o : Own) (F : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Mats Cb.Gl.E) :
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
  /-- what the lookup has heard has the layout's shape -/
  shape : o.H.fo.shape = o.v.y.fo

/-- **LookAsks from what is left of it and the public facts on the layout.** CONDITIONAL: on G and
A. -/
theorem lookAsks_of_left {h : Layer.Shape} {pc : List (List String)} {rd : Layer.Reads}
    {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
    {pts : List (String × Array E)} {D : Dim}
    (G : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) {F : Fork} {mask : ℕ → Cb.Gl.E}
    {Mm : Mats Cb.Gl.E} (A : LookLeft tl o F mask Mm) : LookAsks tl o F mask Mm :=
  { heard := A.heard, ok := A.ok, sized := A.sized, run := run_of_ground G
    cols := cols_of_shape G A.shape }

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.cols_of_shape
#print axioms OnBytes.Road.K4.W.lookAsks_of_left
