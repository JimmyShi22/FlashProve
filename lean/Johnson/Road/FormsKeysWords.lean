-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWords.lean: the dictionary of the scale file's words, against the library's
own reading of the file.

Johnson/Road/FormsKeysFits.lean says once, in wordsAt, which word of a layer's record in the
verifier's scale file is which of the library's scales. The library has a reading of its own: a file
is given as records (KLFile: 13 words for each of 48 layers, 3 more for each of 24 layers with
routed experts), KLFile.words says which word is which, and Words.scale makes the scales of a layer
(Inst/Model/ProgTests.lean). This file shows that the two dictionaries are one.

What is compared with what: wordsAt with KLFile.words and Words.scale, for every scale file and
every layer below 48, through fileOf: the verifier's file cut into records by the verifier's own two
functions Scales.kl and Scales.klM.

Main definition: fileOf. Main theorem: wordsAt_eq.

What is not claimed. At profile 3 a layer's record in the verifier's file has 12 words, so the
records of 13 words that fileOf makes overlap there: word 12 of a layer is the next layer's word 0,
and word 11 is the rotary flag. The theorem holds all the same, since KLFile.words reads no word 12.
The library has no reading of a flat file: how the words of the file are cut
into records is the verifier's rule alone (fileOf). The library's file has 48 layers; for another
number of layers it has no reading. The words of the final normalisation and of the acceptance
policy are set to 0 in fileOf: KLFile.words does not read them. The program does not import this
file.
-/
import Johnson.Road.FormsKeysFits
import Inst.Model.ProgTests

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Shape Scales)
open Inst.Model (KLFile)

/-- The verifier's scale file as the library's records: word i of layer L by Scales.kl, word i of
the record number e of the layers with routed experts by Scales.klM at layer 2 e + 1; the two norms'
constants from the shape. -/
def fileOf (h : Shape) (sc : Scales) : KLFile where
  lay L i := sc.kl L.val i.val
  moe e i := sc.klM (2 * e.val + 1) i.val
  eps1 := h.eps1
  eps2 := h.eps2
  MF := 0
  KF := 0
  epsF := 0
  C := 0
  theta := 0
  cap := 0

/-- The two dictionaries are one: for every scale file and every layer below 48, the scales that
wordsAt reads are those that the library's own reading makes of the file's records. -/
theorem wordsAt_eq (h : Shape) (sc : Scales) (L : Fin 48) :
    wordsAt h sc L.val = ((fileOf h sc).words L).scale := by
  have e : L.val % 2 = 1 → 2 * (L.val / 2) + 1 = L.val := by omega
  unfold wordsAt KLFile.words Inst.Model.Words.scale fileOf
  by_cases hL : L.val % 2 = 1
  · simp only [hL, if_true, e hL]
    rfl
  · simp only [hL, if_false]
    rfl

#print axioms wordsAt_eq

end OnBytes.Road
