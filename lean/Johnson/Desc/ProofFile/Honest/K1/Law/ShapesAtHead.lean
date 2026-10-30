-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ShapesAtHead.lean: ShapesFit (Johnson/HonestTrace/PackedJoins.lean) UNDER THE HEAD, AT EACH OF THE 25 SEGMENTS: the plan's matrices
have the sizes' shapes. Public data alone: the head's views are the written ones (views_at_head); on these the test is one fact by Lean's kernel.

  shapesW, shapesW_ok, shapesW_bent   the test on the written views; a control that it can fail
  shapesFit_at_head                   the statement

NO PROPERTY IS CLAIMED.
-/
import Johnson.HonestTrace.U3Fit.MatsAtHead
import Johnson.HonestTrace.PackedJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes.HonestTrace
open OnBytes.HonestTrace.U3.Fit
open ProofFile.Honest.K3 (tlOf)
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- Each written view has the sizes' shape of its number. -/
def shapesW (d : ℕ) : Bool :=
  (List.range 25).all fun l => ((viewsW.getD l []).zipIdx).all fun v =>
    Sz.ref.shapeNo l v.2 == (v.1.2.2.1 + d, v.1.2.2.2)

set_option maxRecDepth 1000000 in
theorem shapesW_ok : shapesW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test can fail. -/
theorem shapesW_bent : shapesW 1 = false := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The plan's matrices have the sizes' shapes, at each segment.** hNM: the record's count is its
list's. -/
theorem shapesFit_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l < 25)
    (hNM : (tlOf G.W l).NM ≤ (tlOf G.W l).mats.size) : ShapesFit (tlOf G.W l) Sz.ref l := by
  intro μ hμ
  have hm : μ < (tlOf G.W l).mats.size := Nat.lt_of_lt_of_le hμ hNM
  have hv : ((viewsOf G.W).getD l [])[μ]? = some (matView ((tlOf G.W l).mats[μ])) := by
    rw [views_getD G.W hl, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hm]
    rfl
  rw [views_at_head h hG] at hv
  have hw := List.all_eq_true.1 (List.all_eq_true.1 shapesW_ok l (List.mem_range.2 hl))
    (matView ((tlOf G.W l).mats[μ]), μ)
    (List.mem_zipIdx_iff_getElem?.2 (by simpa using hv))
  have e : (tlOf G.W l).mats.getD μ {} = (tlOf G.W l).mats[μ] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm]
    rfl
  rw [e]
  exact eq_of_beq hw

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.shapesW_ok
#print axioms ProofFile.Honest.K1.shapesW_bent
#print axioms ProofFile.Honest.K1.shapesFit_at_head
