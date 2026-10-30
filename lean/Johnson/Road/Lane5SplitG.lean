-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5SplitG.lean

The seam before the lookup of a group of layers, in the layouts' numbering: the group's cells are
small, its identities vanish, and every call's keys lie in its table; so link 2 g is in order.

"LayerOrd" (FormsKeysLinkL.lean) has three clauses on the integer matrices behind a group's
sub-proof: small; idn; key: all entries of the group's eight key vectors are images of entries of
the library's reference tables. The third is the lookup's. "linkOK_even" proves "LinkOK" at link 2
g from the three.

WHAT THE TWO PARTS WEIGH. In the library's segments every rounded product is checked by a key, and
the product is formed inside the key. So the lookup clause holds every product with a weight matrix
(layers, head) and the scores and accumulators (attention); the first part reads of the weights the
embedding alone. A bridge must therefore show that a call's key vector is that formula at the cells
and at the committed weights: it holds the matrix products, not a renaming of tables. Here:
"LayerR0" takes the weights through the embedding alone; every product with the layers' eleven
kinds of weight matrices stands in "LayerKeys". Who gives "small" is not said here: by the
verifier's own words it is what the smallness test is meant to give, not the lookup.

Main definitions and theorems:
* "LayerR0": the first two clauses: the group's meaning WITHOUT its lookup clause.
* "LayerKeys": the third clause.
* "layerOrd_iff_split": "LayerOrd" is the two together.
* "LayerBridge": for the letters of a lookup's calls ("CallsAt", Lane5Split.lean): "every call's
  keys lie in its table" gives "LayerKeys". NAMED, NOT PROVED HERE. It is an implication and no
  more.
* "linkOK_of_layerSplit": under five public hypotheses on shape and layout: "LayerR0", "InTables"
  and "LayerBridge" give "LinkOK" at link 2 g, at the family of segments with the ledger's head and
  the library's matrices "libMZ y g Mz".
* "splitG_of_layer": so, under "LayerR0", "SplitG" (Lane5Split.lean) holds there. Its own premise
  "LinkR0" is not used: nobody shows that "LinkR0" at the library's matrices gives "LayerR0" in the
  layouts' numbering.

Not claimed: "LayerBridge" for any calls. The library's tables stand in "LayerKeys", not a
verifier's. The matrices hold integers: how a field element is lifted is said nowhere here. All is
at the reference sizes. All that FormsKeysLinkL.lean and Lane5Split.lean do not claim.
-/
import Johnson.Road.FormsKeysLinkL
import Johnson.Road.Lane5LedgerLinks
import Johnson.Road.Lane5Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Model.Layer (Lay Shape Scales layout)
open Inst.Model (Scl Tables Mat ppref AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell Idn idnVal embR keyVec layerR lut aC)

/-- **The meaning of a group of layers without its lookup clause.** -/
def LayerR0 (h : Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (x : Cm.Seg.XI) : Prop :=
  SmallM y Mz ∧ ∀ j : Idn, j.Valid DF (decide (g = 0)) →
    idnVal (scl := sclOf h sc g 4) DF
        (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
        (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0

/-- **The lookup clause of a group of layers.** -/
def LayerKeys (h : Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat) : Prop :=
  ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
    ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
        Cb.Tab Cb.Gl.F).set,
      keyVec (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          Inst.Model.tbRef (4 * g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
        algebraMap Cb.Gl.F Cb.Gl.E u

/-- **A group of layers is in order if and only if both parts hold.** -/
theorem layerOrd_iff_split {h : Shape} {sc : Scales} {y : Lay} {g : ℕ} {Mz : Mats ℤ} {Wi : Mat}
    {x : Cm.Seg.XI} :
    LayerOrd h sc y g Mz Wi x ↔ LayerR0 h sc y g Mz Wi x ∧ LayerKeys h sc y g Mz Wi :=
  ⟨fun H => ⟨⟨H.small, H.idn⟩, H.key⟩, fun H => ⟨H.1.1, H.1.2, H.2⟩⟩

/-- **The bridge from a lookup's calls to the group's key vectors.** -/
def LayerBridge (h : Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (C : CallsAt) : Prop :=
  C.InTables → LayerKeys h sc y g Mz Wi

variable {h : Shape} {pc : List (List String)} {y : Lay}

/-- **The seam before the lookup of group g of layers.** -/
theorem linkOK_of_layerSplit (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF)
    (Z2 : Sized2 h DF) (hp4 : h.p4 = true) {Mz : Mats ℤ} {Wi : Mat} {g : ℕ} (hg : g < nGr)
    (sc : Scales) (nf : Inst.Model.NormPar) (pol : AcceptancePolicy) (x : Cm.Seg.XI) {C : CallsAt}
    (B : LayerBridge h sc y g Mz Wi C) (R : LayerR0 h sc y g Mz Wi x) (I : C.InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf h sc nf) pol) Wi x (2 * g) (libMZ y g Mz) :=
  linkOK_pol pol (by have := hg; unfold nGr at this; omega)
    (linkOK_even hy S Z Z2 hp4 Cm.Seg.Hd.main Mz Wi hg sc nf x R.1 R.2 (B I))

/-- **So, under "LayerR0", the seam of Lane5Split.lean holds at the library's matrices of the
group.** -/
theorem splitG_of_layer (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF)
    (Z2 : Sized2 h DF) (hp4 : h.p4 = true) {Mz : Mats ℤ} {Wi : Mat} {g : ℕ} (hg : g < nGr)
    (sc : Scales) (nf : Inst.Model.NormPar) (pol : AcceptancePolicy) (x : Cm.Seg.XI) {C : CallsAt}
    (B : LayerBridge h sc y g Mz Wi C) (R : LayerR0 h sc y g Mz Wi x) (A : ℕ → Mx)
    (hA : A (2 * g) = libMZ y g Mz) :
    SplitG (scalesOf h sc nf) pol Wi x A g C := by
  intro _ I
  rw [hA]
  exact linkOK_of_layerSplit hy S Z Z2 hp4 hg sc nf pol x B R I

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.layerOrd_iff_split
#print axioms OnBytes.Road.L5.linkOK_of_layerSplit
#print axioms OnBytes.Road.L5.splitG_of_layer
