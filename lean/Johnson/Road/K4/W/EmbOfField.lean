-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/EmbOfField.lean: CONDITIONAL.

What is here. The hypothesis `EmbCube` (W/EmbOpened.lean: in the first group the stream that comes
in is the embedding of the tokens, at every feature and every position) from the library's
`EmbField` (Johnson/Road/Rows/LayerTop.lean: the same identity at every valid name, at the cells of
the images of a list of integer matrices, the embedding of an index's matrix and a request's
tokens). The identity reads no table of scales, so the two tables need not agree. One statement; its
proof unfolds the identity.

  `embCube_of_field`   **`EmbCube DF t emb tok d`.**

Not shown here. THAT THE LIBRARY's `EmbField` HOLDS OF ANY LIST, INDEX AND REQUEST: E is a
hypothesis. ht: the cells are the cells of the images of the list. hemb: the embedding that is read
is the embedding of the index's matrix. htok: the tokens that are read are the request's, at every
position. hd: the number of features is at most the library's. Of the hypotheses together no example
is known. THE FULL SIZE ALONE: `EmbField` stands at the library's reference sizes `DF`. THE FIRST
GROUP ALONE. Nothing on soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).
-/
import Johnson.Road.K4.W.EmbOpened
import Johnson.Road.Rows.LayerTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Scales)
open OnBytes.Road.Rows.Norms (EmbField castM)
open Inst.Model (Scl Mat ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell xS embR)

/-- **`EmbCube` FROM THE LIBRARY's `EmbField` AT THE FIRST GROUP.** sc': any table of scales.
CONDITIONAL: on E, ht, hemb, htok and hd. -/
theorem embCube_of_field {hS : Layer.Shape} {sc : Scales} {y : Lay} {Mz : Mats ℤ} {Wi : Mat}
    {x : Cm.Seg.XI} (E : EmbField hS sc y 0 Mz Wi x) (sc' : Scl) {t : Cell → Cb.Gl.E}
    {emb : ℕ → ℕ → Cb.Gl.E} {tok : ℕ → ℕ} {d : ℕ}
    (ht : t = cellsOf DF (cellsAt y (castM Mz)))
    (hemb : emb = embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E))
    (htok : ∀ p, p < 2 ^ DF.lT → tok p = Cm.Seg.tokX x p) (hd : d ≤ DF.d) :
    EmbCube (scl := sc') DF t emb tok d := by
  intro j hj p hp
  have q := E j p ⟨rfl, Nat.lt_of_lt_of_le hj hd, hp⟩
  show xS DF t 0 j p - emb (tok p) j = 0
  rw [ht, hemb, htok p hp]
  exact q

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.embCube_of_field
