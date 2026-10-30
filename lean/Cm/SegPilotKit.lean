-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegPilotKit.lean: what the feed-forward segment reads, as affine forms (over the algebra of
Cm/SegAlg.lean).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). An affine form in cells is `CForm` (Cb/Req/ReqSpec.lean).
Used for the feed-forward segment's families (Cm/SegPilotAff.lean, Cm/SegFFCellLed.lean,
Cm/SegFFMatKit.lean) and by Cm/SegFFAffPass.lean.

Main names:
  `mapLW`, `wOf g W`: the weights of the layers of group g, read from the index matrix over F and
    carried into E: what the statements labelled (V) (the head of Cm/TargetSegFFAffPass.lean) of
    families with weights speak of.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAlg
import Cm.SegLayoutProofs
import Inst.Model.FF.Trace

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset

section FF
variable {E : Type} [Field E] (g : ℕ)

/-- The matrices, read as a trace of the feed-forward segment of group g. -/
def tA (A : ℕ → ℕ → ℕ → E) : FFSeg.Cell → E := fun c =>
  A (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2

/-- one cell -/
def cCell (c : FFSeg.Cell) : CForm E := cAt (ownFF g c).place

/-- The read-out formula (`FFSeg.val`) as a form. -/
def cVal (X : FFSeg.Arr) (a j i : ℕ) : CForm E :=
  cSum X.nCell (fun k => ((256 : E) ^ k) • cCell g ⟨X, k, a, j, i⟩) + cK (((X.off : ℤ) : E))

variable (A : ℕ → ℕ → ℕ → E)

@[simp] theorem val_cCell (c : FFSeg.Cell) : (cCell g c : CForm E).val A = tA g A c := val_cAt A _

@[simp] theorem val_cVal (X : FFSeg.Arr) (a j i : ℕ) :
    (cVal g X a j i : CForm E).val A = FFSeg.val (tA g A) X a j i := by
  simp [cVal, FFSeg.val]

/-- the place of a valid cell that the feed-forward segment of group g reads -/
def IsFF (p : Cb.Place) : Prop := ∃ c : FFSeg.Cell, c.Valid DF ∧ p = (ownFF g c).place

/-- every place of the form f has `IsFF g` -/
abbrev InFF (f : CForm E) : Prop := AllPl (IsFF g) f

theorem inFF_cCell {c : FFSeg.Cell} (hc : c.Valid DF) : InFF g (cCell g c : CForm E) :=
  AllPl.cAt ⟨c, hc, rfl⟩

theorem inFF_cVal {X : FFSeg.Arr} {a j i : ℕ} (ha : a < X.cnt DF)
    (hj : j < X.width DF) (hi : i < DF.T) :
    InFF g (cVal g X a j i : CForm E) :=
  AllPl.add (AllPl.cSum fun _ hk => AllPl.smul _ (inFF_cCell g ⟨hk, ha, hj, hi⟩)) (AllPl.cK _)

/-- for g < `nGr` a place with `IsFF g` is among those that the layout says segment 2 g reads
(`reads`) -/
theorem isFF_reads (h : Hd) (hg : g < nGr) {p : Cb.Place} (hp : IsFF g p) :
    p ∈ reads h (2 * g) := by
  obtain ⟨c, hc, rfl⟩ := hp
  exact Or.inl ⟨g, c, rfl, hg, hc, rfl⟩

end FF

/-- the weights of a layer, carried along a ring homomorphism -/
def mapLW {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (w : FFSeg.LW R) : FFSeg.LW R' :=
  ⟨fun j x => f (w.Wq j x), fun j x => f (w.Wk j x), fun j x => f (w.Wv j x),
    fun j x => f (w.Wo j x), fun j x => f (w.Wg j x), fun j x => f (w.Wu j x),
    fun j x => f (w.Wd j x), fun j x => f (w.Wr j x), fun e j x => f (w.Eg e j x),
    fun e j x => f (w.Eu e j x), fun e j x => f (w.Ed e j x)⟩

theorem mapLW_ofInt {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (w : LayerW) :
    mapLW f (FFSeg.LW.ofInt R w) = FFSeg.LW.ofInt R' w := by
  simp [mapLW, FFSeg.LW.ofInt]

/-- The weights that the families of group g read: layer 4 g + ℓ, read from the index matrix W over
F by the layout, carried into E. -/
def wOf {F E : Type} [Field F] [Field E] [Algebra F E] (g : ℕ) (W : ℕ → ℕ → F) : ℕ → FFSeg.LW E :=
  fun l => mapLW (algebraMap F E) (FFSeg.layerR ppref Layout.kRef W (4 * g + l))

theorem mem_tabOf {F : Type} [Field F] {L : Lut} {T : ℕ} (hL : L.rows = 2 ^ T) (u : F) :
    u ∈ (tabOf L T : Tab F).set ↔ u ∈ (FFSeg.lutSet L : Set F) :=
  mem_tabOf_iff hL u

end Cm.Seg
