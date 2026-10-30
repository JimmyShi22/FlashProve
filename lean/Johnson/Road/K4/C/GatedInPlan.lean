-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/GatedInPlan.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the public hypothesis
GatedIn (GatedCells.lean) at every layout that the verifier's function layout returns under the
library's switches: by the three laws of the library and the rounding up that serve the streams
(StreamsOf.lean), at the arrays of the two gated products' factors. Statements and proofs.

  `gated_inMat`         one limb's feature.
  **`gatedIn_of_laid`**   GatedIn from the library's facts on a layout.
  **`gatedIn_of_plan`**   GatedIn from K4Plan.

Not shown here. That a plan with the public facts K4Plan exists: no example is known.
No property is claimed.
-/
import Johnson.Road.K4.C.StreamsOf
import Johnson.Road.K4.C.GatedCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Pub Ten)
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim Arr)

variable {y : Lay}

/-- A limb of an array of two limbs, one instance a layer and one channel for each unit of the inner
width, in the matrix af: its feature lies inside the parts of that matrix. -/
theorem gated_inMat (L : Laid y) (L2 : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
    {A : Arr} (hA : inList y.h A) (hn : A.nCell = 2) (hc : A.cnt D = D.nl) (hw : A.width D = D.f)
    (hm : A.mx = .af) {X : Ten} (hX : y.T_ (arrName A) = some X) {l ix j : ℕ} (hl : l < 2)
    (hix : ix < y.Lam) (hj : j < y.h.f) : InMat y 0 (tenCell X.place l ix j) := by
  rw [(place_eq_feat L S Z A hA hX l ix j).1]
  have h1 := Inst.Model.FFSeg.IndexFacts.feat_lt D (X := A) (k := l) (inst := ix) (j := j)
    (by rw [hn]; exact hl)
    (by
      rw [hc]
      show ix < 2 ^ D.lL
      rw [Z.lL, ← L.Lam]
      exact hix)
    (by
      rw [hw]
      show j < D.P.f
      rw [Z.f]
      exact hj)
  rw [hm, ← (feat_total L2 S Z).1] at h1
  exact ⟨by decide, Nat.lt_of_lt_of_le h1 (cap_af L2)⟩

/-- **THE FEATURES OF THE TWO TENSORS LIE INSIDE THEIR MATRIX**, from the library's facts on a
layout. -/
theorem gatedIn_of_laid (L : Laid y) (L2 : Laid2 y) (S : Switches y.h) {D : Dim}
    (Z : Sized y.h D) : GatedIn y where
  s := fun _ hX _ hl _ hix _ hj =>
    gated_inMat L L2 S Z (A := Arr.sl) (Or.inl rfl) rfl rfl rfl rfl hX hl hix hj
  u := fun _ hX _ hl _ hix _ hj =>
    gated_inMat L L2 S Z (A := Arr.up) (Or.inl rfl) rfl rfl rfl rfl hX hl hix hj

/-- **GatedIn AT EVERY PLAN WITH THE PUBLIC FACTS K4Plan.** -/
theorem gatedIn_of_plan {hS : Layer.Shape} {pc : List (List String)} {P : Pub} {g : ℕ}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) : GatedIn P.y := by
  obtain ⟨hsh, L⟩ := laid_of_layout A.lay A.sw.p3
  exact gatedIn_of_laid L (laid2_of_layout A.lay) (by rw [hsh]; exact A.sw)
    (by rw [hsh]; exact A.sized)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.gated_inMat
#print axioms OnBytes.Road.K4.C.gatedIn_of_laid
#print axioms OnBytes.Road.K4.C.gatedIn_of_plan
