-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgWit.lean: that the record TiesW can be met.
States: (tiesW_of_laid) TiesW (AlgGam.lean) CAN BE MET, at the same names of cells at which
fits_of_layout_any (Johnson/Road/FormsKeysAdmit.lean) meets Fits and AlgTies.lean's ties_of_fits
then gives TiesG: t := cellsOf D (cG P cell). The weights w := wOfG P g cell and the rotary tables
tbG P, with L0 := g * Lam, meet their clauses by definition; the attention output's clause follows
from tied_cellsOf (Johnson/Road/FormsKeysFits.lean) and AlgTies.lean's val_of_tied.
Under public clauses alone: the plain facts on the layout (Laid), the switches, sizes that agree
with the shape, profile 4, the tensor o found with two limbs in one of the four families of
matrices, an even width of a head.
Does not say: that these public clauses hold together at a shape (a run:
Johnson/Road/FormsKeysRun8.lean, Johnson/Road/FormsKeysO.lean).
-/
import Johnson.Road.FormsKeysFits
import Johnson.Road.Ends.AlgTies
import Johnson.Road.Ends.AlgGam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model.Layer (Ten)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Arr)

/-- The library's table functions with the verifier's rotary table; the three others are 0. -/
def tbG (P : Model.Layer.Pub) : Tables :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0,
    fun L i j => Model.Layer.ropeC P.y.h P.sc P.rope L i j false,
    fun L i j => Model.Layer.ropeC P.y.h P.sc P.rope L i j true⟩

variable {K : Type} [Field K] [scl : Scl]

omit scl in
/-- **TiesW can be met.** -/
theorem tiesW_of_laid {P : Model.Layer.Pub} (g : ℕ) (cell : G.NameG → K) {D : Dim}
    (L : Laid P.y) (S : Switches P.y.h) (Z : Sized P.y.h D) (hp4 : P.y.h.p4 = true) {ten : Ten}
    (hin : inList P.y.h .o) (hT : P.y.T_ (arrName .o) = some ten) (hn : ten.nl = Arr.nCell .o)
    (hm : ten.mat < 4) (hev : P.y.h.dh % 2 = 0) :
    TiesW P g cell D (cellsOf D (cG P cell)) (tbG P) (g * P.y.Lam) (wOfG P g cell) where
  p4 := hp4
  valO := fun inst j i => by
    have e := val_of_tied hT (tied_cellsOf L S Z (cG P cell) hin hT hn) hm inst j i
    simpa [arrName, Arr.off] using e
  d := Z.d.symm
  f := Z.f.symm
  ch := Z.ch.symm
  even := by
    rw [Z.ch]
    exact hev
  w := fun _ _ => rfl
  C := fun _ _ _ _ => rfl
  S := fun _ _ _ _ => rfl

#print axioms tiesW_of_laid

end OnBytes.Road.Alg
