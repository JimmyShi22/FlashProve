-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerTop.lean: the record "a group of layers is in order", cut into five fields
by name.

LayerOrd (Johnson/Road/FormsKeysLinkL.lean) says of the integer matrices Mz behind the sub-proof of
a group of layers: their entries are small, all identities of the group vanish on their cells, and
all entries of the group's key vectors lie in their tables. None of this speaks of a transcript.
This file names the parts by which part of the sub-proof's check tests them.
 - SmallM (Johnson/Road/FormsKeysDictZ.lean): the clause small: the smallness test.
 - NormField: the identities (J1) to (J9): tested at the norms' token point, a draw of its own.
 - HotField: the identity (J10): tested at the tail of the lookup's point.
 - EmbField: the identity (J11), in the first group: the embedding's claim and the merge.
 - KeyField: the clause key: the lookup, with the batched sumcheck, the second token sumcheck, the
   gated product layers and the merge.

Main definitions: castM, NormField, HotField, EmbField, KeyField. Main theorems: layer_start (the
five fields give the record), layer_fields (the record gives the five). Both derive nothing: the
five are the record's clauses, the clause idn cut by the three kinds of names of identities.

What is owed. That the first claim of the chain of the sub-proof's rounds, at matrices that are a
function of the committed messages, gives these fields. No such statement is here: Mz, Wi and x are
free letters. The words above on which part of the check tests a field name who is meant to give
it; nobody does yet.

At which sizes. The library's reference sizes DF and the field Cb.Gl.E, as LayerOrd asks. The one
use of LayerOrd (linkOK_layer, Johnson/Road/FormsKeysLinkL.lean) asks more of the shape.

What is not claimed. No field is shown here. The program does not import this file.


-/
import Johnson.Road.FormsKeysLinkL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows.Norms

open OnBytes.Model.Layer (Lay Scales)
open Inst.Model (Mat ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Idn idnVal embR keyVec layerR lut aC)

/-- The casts of integer matrices into the challenge field. -/
def castM (Mz : Mats ℤ) : Mats Cb.Gl.E := fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)

/-- The identity (J11) at every valid name: in the first group the stream that comes in is the
embedding of the request's tokens. -/
def EmbField (h : Model.Layer.Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (x : Cm.Seg.XI) : Prop :=
  ∀ j i, (Idn.j11 j i).Valid DF (decide (g = 0)) →
    idnVal (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y (castM Mz)))
      (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) (.j11 j i) = 0

/-- The clause key of LayerOrd. -/
def KeyField (h : Model.Layer.Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat) :
    Prop :=
  ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
    ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
        Cb.Tab Cb.Gl.F).set,
      keyVec (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y (castM Mz))) Inst.Model.tbRef
          (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
          c X = algebraMap Cb.Gl.F Cb.Gl.E u

/-- The identities (J1) to (J9) at every valid name. -/
def NormField (h : Model.Layer.Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (x : Cm.Seg.XI) : Prop :=
  ∀ k ν i, (Idn.jn k ν i).Valid DF (decide (g = 0)) →
    idnVal (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y (castM Mz)))
      (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) (.jn k ν i) = 0

/-- The identity (J10) at every valid name. -/
def HotField (h : Model.Layer.Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (x : Cm.Seg.XI) : Prop :=
  ∀ l i, (Idn.j10 l i).Valid DF (decide (g = 0)) →
    idnVal (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y (castM Mz)))
      (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) (.j10 l i) = 0

/-- LayerOrd's three clauses under five names. It derives nothing: its body is the record's
constructor. -/
theorem layer_start {h : Model.Layer.Shape} {sc : Scales} {y : Lay} {g : ℕ} {Mz : Mats ℤ}
    {Wi : Mat} {x : Cm.Seg.XI} (hS : SmallM y Mz) (hN : NormField h sc y g Mz Wi x)
    (hH : HotField h sc y g Mz Wi x) (hE : EmbField h sc y g Mz Wi x)
    (hK : KeyField h sc y g Mz Wi) : LayerOrd h sc y g Mz Wi x :=
  ⟨hS, fun j hv => by
    cases j with
    | jn k ν i => exact hN k ν i hv
    | j10 l' i => exact hH l' i hv
    | j11 j' i => exact hE j' i hv, hK⟩

/-- The record gives the five fields. -/
theorem layer_fields {h : Model.Layer.Shape} {sc : Scales} {y : Lay} {g : ℕ} {Mz : Mats ℤ}
    {Wi : Mat} {x : Cm.Seg.XI} (O : LayerOrd h sc y g Mz Wi x) :
    SmallM y Mz ∧ NormField h sc y g Mz Wi x ∧ HotField h sc y g Mz Wi x ∧
      EmbField h sc y g Mz Wi x ∧ KeyField h sc y g Mz Wi :=
  ⟨O.small, fun k ν i hv => O.idn (.jn k ν i) hv, fun l i hv => O.idn (.j10 l i) hv,
    fun j i hv => O.idn (.j11 j i) hv, O.key⟩

end OnBytes.Road.Rows.Norms
