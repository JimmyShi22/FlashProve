-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StreamsOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the public hypothesis
StreamsIn (Feats.lean) at every layout that the verifier's function layout returns under the
library's switches. The feature of a limb by the verifier's rule is the library's (place_eq_feat,
xb_eq_feat, Johnson/Road/FormsKeysFits.lean); the library's feature lies below the matrix's number
of features (feat_lt, Inst/Model/FF/IndexFacts.lean), which is the layout's (feat_total,
Johnson/Road/FormsKeysAddr.lean); and the layout rounds that number up to whole columns of all
parts. Statements and proofs.

  `ceil_cover`      a number is at most its quotient by w, rounded up, times w.
  `cap_stream`      a matrix of the residual stream holds xl d features.
  `cap_af`          the parts of the matrix af hold its features in use.
  **`streamsIn_of_laid`**   StreamsIn from the library's facts on a layout.
  **`streamsIn_of_plan`**   StreamsIn from K4Plan.

Not shown here. That a plan with the public facts K4Plan exists: no example is known. The library's
five limbs stand in the statement StreamsIn itself: the law leans on the switch xl = 5 (Switches).
No property is claimed.
-/
import Johnson.Road.K4.C.Feats
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanClauses
import Johnson.Road.FormsKeysAddr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Pub)
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim Arr)
open OnBytes.Desc.First.K4.Honest (tensorOf)

/-- A number is at most its quotient by w, rounded up, times w. -/
theorem ceil_cover (a : ℕ) {w : ℕ} (hw : 0 < w) : a ≤ (a + w - 1) / w * w :=
  (ceil_le_iff hw).mp (Nat.le_refl _)

variable {y : Lay}

/-- A matrix of the residual stream holds xl d features. -/
theorem cap_stream (L2 : Laid2 y) : y.h.xl * y.h.d ≤ partsM y 4 * colsM y 4 * fcM y 4 := by
  have hx : y.h.lt ≤ y.h.lmx := Nat.le_trans (Nat.le_of_lt L2.lt_la) L2.la_x
  have hu : 0 < 2 ^ y.h.lmx / 2 ^ y.h.lt :=
    Nat.div_pos (Nat.pow_le_pow_right (by decide) hx) (Nat.two_pow_pos _)
  show y.h.xl * y.h.d ≤ 1 * y.kxb * (y.mxb / y.T)
  rw [L2.kxb, L2.mxb, L2.T, Nat.one_mul, roundUp_div _ hu]
  exact ceil_cover _ hu

/-- The parts of the matrix af hold its features in use. -/
theorem cap_af (L2 : Laid2 y) : y.feat.getD 0 0 ≤ partsM y 0 * colsM y 0 * fcM y 0 := by
  have hu : 0 < 2 ^ y.h.lmaf / 2 ^ y.h.lt :=
    Nat.div_pos (Nat.pow_le_pow_right (by decide) L2.lt_af) (Nat.two_pow_pos _)
  have hw : 0 < y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt) :=
    Nat.mul_pos (Nat.pos_of_ne_zero L2.NAf0) hu
  show y.feat.getD 0 0 ≤ y.parts.getD 0 0 * y.kcol.getD 0 0 * (y.mrow.getD 0 0 / y.T)
  rw [L2.feat0, L2.parts0, L2.kcol0, L2.mrow0, L2.T, roundUp_div _ hw]
  have h := ceil_cover ((offsOf y.h).getD 0 0) hw
  calc (offsOf y.h).getD 0 0
      ≤ ((offsOf y.h).getD 0 0 + y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt) - 1) /
          (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt)) * (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt)) := h
    _ = y.h.NAf * (((offsOf y.h).getD 0 0 + y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt) - 1) /
          (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt))) * (2 ^ y.h.lmaf / 2 ^ y.h.lt) := by ring

/-- **THE FEATURES OF THE STREAMS' LIMBS LIE INSIDE THEIR MATRICES**, from the library's facts on a
layout. -/
theorem streamsIn_of_laid (L : Laid y) (L2 : Laid2 y) (S : Switches y.h) {D : Dim}
    (Z : Sized y.h D) (hNI : y.NI = D.nNu) : StreamsIn y where
  first := fun l hl j hj => by
    refine ⟨by decide, ?_⟩
    rw [(xb_eq_feat L Z l 0 j).1]
    have h1 : Inst.Model.FFSeg.feat D .x0 l 0 j < Inst.Model.FFSeg.nFeatMx D .xin :=
      Inst.Model.FFSeg.IndexFacts.feat_lt D (X := Arr.x0) hl Nat.one_pos
        (by show j < D.P.d; rw [Z.d]; exact hj)
    rw [← (feat_total L2 S Z).2.2.2.2.2.1] at h1
    exact Nat.lt_of_lt_of_le h1 (cap_stream L2)
  inner := fun l hl i hi j hj => by
    obtain ⟨ten, hT, _⟩ := ten_of L S Arr.xs (Or.inl rfl)
    have e : tensorOf y "xs" = ten := by
      unfold tensorOf
      have hT' : y.T_ "xs" = some ten := hT
      rw [hT']
      rfl
    obtain ⟨e1, e2⟩ := place_eq_feat L S Z Arr.xs (Or.inl rfl) hT l i j
    rw [e, e1, e2]
    have hN : D.nNu = 2 * D.nl := rfl
    have h1 : Inst.Model.FFSeg.feat D .xs l i j < Inst.Model.FFSeg.nFeatMx D .af :=
      Inst.Model.FFSeg.IndexFacts.feat_lt D (X := Arr.xs) hl
        (by show i < 2 * D.nl - 1; omega) (by show j < D.P.d; rw [Z.d]; exact hj)
    rw [← (feat_total L2 S Z).1] at h1
    exact ⟨by decide, Nat.lt_of_lt_of_le h1 (cap_af L2)⟩

/-- **StreamsIn AT EVERY PLAN WITH THE PUBLIC FACTS K4Plan.** -/
theorem streamsIn_of_plan {hS : Layer.Shape} {pc : List (List String)} {P : Pub} {g : ℕ}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) : StreamsIn P.y := by
  obtain ⟨hsh, L⟩ := laid_of_layout A.lay A.sw.p3
  have Ls := laySizes_of_layout A.lay
  exact streamsIn_of_laid L (laid2_of_layout A.lay) (by rw [hsh]; exact A.sw)
    (by rw [hsh]; exact A.sized) (by rw [Ls.NI, nNu_tie A.sized])

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ceil_cover
#print axioms OnBytes.Road.K4.C.cap_stream
#print axioms OnBytes.Road.K4.C.cap_af
#print axioms OnBytes.Road.K4.C.streamsIn_of_laid
#print axioms OnBytes.Road.K4.C.streamsIn_of_plan
