-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLawP.lean: the table of scales that is made from what the verifier's publicOf
returns is lawful in the library's sense, if the scale file's words and seven numbers of the
parameter file are the full-size shipped example's.

Johnson/Road/FormsKeysLaw.lean shows that the table made from the example's scale words, at the
shape hKF and the final norm nfKF, is the library's reference table and so is lawful. This file
carries that to the letters of the verifier's own entry point: the layers' shape layerShape X.P, the
scales X.layers.sc and the final norm npOf X.hS of a value X of publicOf
(OnBytes/Model/VerifyPublic.lean).

What is compared with what: as in FormsKeysLaw.lean. That the scales in the value of publicOf are
what Layer.scalesOf returns on the words of the scale file, at the shape of the layout in that
value, is scales_of_public (Johnson/Road/HeadL5Grp.lean), a walk through the text of publicOf.

Main theorems.
 - fileOf_eps, lawful_at: of the layers' shape the table reads the two norms' constants alone; so it
   is lawful at every shape with the example's two constants, at the record scKF and the final norm
   nfKF.
 - reader_record, lawful_of_reader: the record that Layer.scalesOf returns (the words, 13 or 12 to a
   layer, the number of layers); so the table is lawful at what that reader returns on the example's
   words, at every shape with four of the example's numbers.
 - shape_of_public: the shape of the layout in the value of publicOf is layerShape of the parameter
   file as read.
 - lawful_public: the table at the letters of publicOf is lawful.

The hypotheses of lawful_public, and where they are met. publicOf returns X. The words of the scale
file are scalesKF. Four numbers of the layers' shape: profile 4, 48 layers, the two constants 53687.
The final norm's three numbers are nfKF's. All but the first are closed equations on public files;
that they hold at the full-size example's files is held by a run that is no part of this library;
nothing here shows it.

Who reads the target: as the head of FormsKeysLaw.lean says.

What is not claimed. Nothing on other scale words or other numbers: that the verifier's tests give
the library's ranges is not shown. At the example the first twelve words are the same in all 48
layers; the thirteenth, the rotary flag, is 0 in each fourth layer and is read by no theorem here.
So the example cannot see one of the twelve words taken from another layer; that the words of layer
L come from the record of layer L is wordsAt_eq (Johnson/Road/FormsKeysWords.lean), for every file.
The program does not import this file.
-/
import Johnson.Road.FormsKeysLaw
import Johnson.Road.HeadPub
import Johnson.Road.HeadL5Grp

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Shape Scales)
open OnBytes.Model.Verify (Public publicOf layerShape)
open Inst.Model (NormPar)

/-- Of the layers' shape, the library's record of a scale file reads the two norms' constants
alone. -/
theorem fileOf_eps {h h' : Shape} (sc : Scales) (e1 : h.eps1 = h'.eps1) (e2 : h.eps2 = h'.eps2) :
    fileOf h sc = fileOf h' sc := by
  unfold fileOf
  rw [e1, e2]

/-- The table is lawful at every shape with the full-size example's two constants, at the example's
record of scale words and its final norm. -/
theorem lawful_at {h : Shape} {sc : Scales} {nf : NormPar} (he1 : h.eps1 = 53687)
    (he2 : h.eps2 = 53687) (hsc : sc = scKF) (hnf : nf = nfKF) : (scalesOf h sc nf).Lawful := by
  subst hsc hnf
  have e : scalesOf h scKF nfKF = scalesOf hKF scKF nfKF := by
    show (⟨(fileOf h scKF).words, nfKF⟩ : Cm.Scales) = ⟨(fileOf hKF scKF).words, nfKF⟩
    rw [fileOf_eps (h' := hKF) scKF he1 he2]
  rw [e]
  exact lawful_words

/-- The record that the verifier's reader of a scale file returns: the words, 13 to a layer at
profile 4 and 12 otherwise, the shape's number of layers. -/
theorem reader_record {h : Shape} {W : Array ℕ} {sc : Scales}
    (hr : Model.Layer.scalesOf h W = .ok sc) : sc = ⟨W, if h.p4 then 13 else 12, h.L⟩ := by
  unfold Model.Layer.scalesOf at hr
  obtain ⟨-, hr⟩ := ok_of_refuse hr
  exact (Except.ok.inj hr).symm

/-- The table is lawful at what the verifier's reader returns on the full-size example's scale
words, at every shape with profile 4, 48 layers and the example's two constants, with the example's
final norm. -/
theorem lawful_of_reader {h : Shape} {W : Array ℕ} {sc : Scales} {nf : NormPar}
    (hr : Model.Layer.scalesOf h W = .ok sc) (hW : W = scalesKF.toArray) (hp4 : h.p4 = true)
    (hL : h.L = 48) (he1 : h.eps1 = 53687) (he2 : h.eps2 = 53687) (hnf : nf = nfKF) :
    (scalesOf h sc nf).Lawful := by
  have e : sc = scKF := by
    rw [reader_record hr, hW, hL, if_pos hp4]
    rfl
  exact lawful_at he1 he2 e hnf

/-- The shape of the layout in the value of publicOf is the layers' shape of the parameter file as
read. -/
theorem shape_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) : X.y.h = layerShape X.P := by
  obtain ⟨P, y, hpl, eP, ey, -⟩ := Hd.public_parts h
  rw [ey, eP]
  exact layout_shape (Hd.layerLayout_of_polLayout hpl)

/-- The table of scales at the letters of the verifier's entry point is lawful in the library's
sense, if the scale file's words are the full-size example's, the layers' shape has profile 4, 48
layers and the example's two constants, and the final norm's numbers are the example's. -/
theorem lawful_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hW : Model.fileWords KL = scalesKF.toArray)
    (hp4 : (layerShape X.P).p4 = true) (hL : (layerShape X.P).L = 48)
    (he1 : (layerShape X.P).eps1 = 53687) (he2 : (layerShape X.P).eps2 = 53687)
    (hnf : Hd.npOf X.hS = nfKF) :
    (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).Lawful := by
  have hs := Hd.scales_of_public h
  rw [shape_of_public h] at hs
  exact lawful_of_reader hs hW hp4 hL he1 he2 hnf

#print axioms fileOf_eps
#print axioms lawful_at
#print axioms reader_record
#print axioms lawful_of_reader
#print axioms shape_of_public
#print axioms lawful_public

end OnBytes.Road
