-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLaw.lean: the table of scales that is made from the full-size shipped
example's scale words and final norm is the library's reference table, and so it is lawful in the
library's sense.

The library's step from its relation to "the reply is the integer model's" (forces in
Cm/TargetPRelProofs.lean) asks that the table of scales be lawful (Cm.Scales.Lawful in
Cm/Rel2.lean): ranges for the shifts and the two norms of each of 48 layers, a range for the shift
of attention, one such shift in a group of four layers, ranges for the final norm, and K ≤ M in
every norm. Johnson/Road/FormsKeysScl.lean makes a table of the library from the verifier's scale
file (scalesOf). This file shows that at the example's words that table is lawful.

What is compared with what. scalesOf hKF sc nfKF, where sc is what the verifier's own reader
Layer.scalesOf (OnBytes/Model/LayerLayout.lean) returns on the example's 696 scale words, with the
library's reference table Cm.sRef (Cm/Rel2Guards.lean). Between them stand fileOf
(Johnson/Road/FormsKeysWords.lean), which cuts the verifier's file into the library's records by the
verifier's kl and klM, and the library's KLFile.words.

Main theorems.
 - words_kit: in all 48 layers the words are the reference's. An evaluation of closed numbers by
   Lean's kernel.
 - scales_ref: the table is Cm.sRef. lawful_words: so it is lawful, by the library's lawful_sRef.
 - scales_of_words: what Layer.scalesOf returns on the words is the record scKF. lawful_kit:
   lawful_words on what that reader returns.
 - unlawful_zero: with the final norm 0, 0, 0 no table is lawful.

Where the final norm's numbers come from. Not from the scale file: from the lines MF, KF, epsF_lo
and epsF_hi of the parameter file, which the verifier's headShape (OnBytes/Model/VerifyPublic.lean)
hands to the head's sub-proof. nfKF is written by hand; a guard holds it against what headShape
makes of the example's parameter file. The final norm matters: at ⟨0, 0, 0⟩ no table is lawful
(unlawful_zero).

The hypothesis of lawful_kit, and that it is met: Layer.scalesOf returns on the words: a guard. That
the words are those of the example's file: a guard of Johnson/Road/FormsKeysRunK.lean reads them
back from the bytes; that scalesKF and linesKF are the shipped files is not shown in Lean.

Who reads the target. By reading: forces (through forces_at) and trace_of_true in
Cm/TargetPRelProofs.lean take s.Lawful as a hypothesis. By a search: the name stands in 25 files of
the library's folder Cm; what each does with it has not been read.

What is not claimed. Nothing on other scale files: that the verifier's tests on a file give the
library's ranges is not shown. Two of the five fields, one shift in a group and K ≤ M, are no
refusal of the verifier: they are conditions of its standard parameter form (oneShift, normShifts in
OnBytes/Model/VerifyStages.lean). The library's table has 48 layers: at the small shipped example
there is no such table. The program does not import this file.
-/
import Johnson.Road.FormsKeysScl
import Johnson.Road.FormsKeysRunK
import Cm.Rel2Guards

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Verify (polLayout headShape)
open Inst.Model (NormPar wRef ppref)

/-- The record of the full-size example's scale words: the words, 13 to a layer, 48 layers. -/
def scKF : Model.Layer.Scales := ⟨scalesKF.toArray, 13, 48⟩

/-- The final norm's three numbers, as the full-size example's parameter file has them. -/
def nfKF : NormPar := ⟨44, 30, 53687⟩

/-- In all 48 layers the words that the library's reading makes of the example's records are the
library's reference words. An evaluation of closed numbers by Lean's kernel. -/
theorem words_kit : ∀ L : Fin 48, (fileOf hKF scKF).words L = wRef := by decide +kernel

/-- The table of scales made from the example's scale words and final norm is the library's
reference table. -/
theorem scales_ref : scalesOf hKF scKF nfKF = Cm.sRef := by
  have h : (fileOf hKF scKF).words = fun _ => wRef := funext words_kit
  show (⟨(fileOf hKF scKF).words, nfKF⟩ : Cm.Scales) = ⟨fun _ => wRef, ppref.nf⟩
  rw [h]
  rfl

/-- So it is lawful in the library's sense. -/
theorem lawful_words : (scalesOf hKF scKF nfKF).Lawful := by
  rw [scales_ref]
  exact Cm.lawful_sRef

/-- What the verifier's reader of a scale file returns on the example's words, at the example's
shape, is the record scKF. -/
theorem scales_of_words {sc : Model.Layer.Scales}
    (h : Model.Layer.scalesOf hKF scalesKF.toArray = .ok sc) : sc = scKF := by
  unfold Model.Layer.scalesOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  exact (Except.ok.inj h).symm

/-- The table of scales made from what the verifier's reader returns on the full-size example's
scale words, with the example's final norm, is lawful in the library's sense. -/
theorem lawful_kit {sc : Model.Layer.Scales}
    (h : Model.Layer.scalesOf hKF scalesKF.toArray = .ok sc) : (scalesOf hKF sc nfKF).Lawful := by
  rw [scales_of_words h]
  exact lawful_words

/-- The final norm matters: with the numbers 0, 0, 0, which fileOf writes into the library's record
of a file, no table is lawful. -/
theorem unlawful_zero (h : Model.Layer.Shape) (sc : Model.Layer.Scales) :
    ¬ (scalesOf h sc ⟨0, 0, 0⟩).Lawful := by
  intro H
  obtain ⟨h1, -⟩ := H.nf
  have h2 : (1 : ℤ) ≤ 0 := h1
  exact absurd h2 (by decide)

/- the reader returns on the words -/
#guard (Model.Layer.scalesOf hKF scalesKF.toArray).isOk

/- the final norm's numbers are what the verifier's headShape makes of the parameter file -/
#guard (match polLayout (textK linesKF) with
  | .ok (P, y) => ((headShape P y).MF, (headShape P y).KF, ((headShape P y).epsF : ℤ)) ==
      (nfKF.M, nfKF.K, nfKF.eps)
  | .error _ => false)

#print axioms words_kit
#print axioms scales_ref
#print axioms lawful_words
#print axioms scales_of_words
#print axioms lawful_kit
#print axioms unlawful_zero

end OnBytes.Road
