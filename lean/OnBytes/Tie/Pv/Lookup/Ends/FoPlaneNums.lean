-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneNums.lean.
The two conditions on public numbers of Fo.HeadLookAll
(OnBytes/Tie/Pv/Lookup/Ends/FoPassedHeadAll.lean) and Fo.AttLookAll
(OnBytes/Tie/Pv/Lookup/Ends/FoPassedAttAll.lean), from a test.

States:
  planeMatHB s Y mats, planeMatAB P: tests on public numbers: the layout's (the plan's) record of
    the lookup is what Forest.shape makes of its calls (Fo.madeB,
    OnBytes/Tie/Pv/Lookup/Ends/FoShapesBDefs.lean); the planes' matrix has its rows in one block of
    2^lmbH (2^lmb); it has at least the planes' columns.
  head_plane_nums, att_plane_nums: where the test holds, a run of Head.hear (of Attention.hear) that
    returns gives the two conditions at the shape of the lookup's record that it returns.
Limit: that the test holds at a model's numbers is a matter of a run
(OnBytes/Tie/Pv/Lookup/Test/FoPlaneNumsTest.lean: at the library's example).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShapes
import OnBytes.Tie.Pv.Lookup.Port.FoReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun Cb.Fo

/-- The test at the head. -/
def planeMatHB (s : Head.Shape) (Y : Head.HL) (mats : Array TMat) : Bool :=
  madeB Y.cl s.LIDB Y.fs && decide ((mats.getD (s.NHf + 1 + 1) {}).m / 2 ^ s.lmbH = 1) &&
    decide (planeCols Y.fs s.lmbH ≤ (mats.getD (s.NHf + 1 + 1) {}).k)

/-- The test at attention. -/
def planeMatAB (P : Attention.Plan) : Bool :=
  madeB (P.S.calls.map (·.call)) P.lid P.fs &&
    decide ((P.mats.getD (P.S.cf.NAs + 2) {}).m / 2 ^ P.S.cf.lmb = 1) &&
    decide (planeCols P.fs P.S.cf.lmb ≤ (P.mats.getD (P.S.cf.NAs + 2) {}).k)

theorem head_plane_nums {s : Head.Shape} {Y : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {plain : Array E} {F G : Fork} {c c' : Ctx} {x : Head.Heard}
    (hB : planeMatHB s Y hp.tl.mats = true)
    (hr : Head.hear s Y hp cov plain F c = .ok ((x, G), c')) :
    (hp.tl.mats.getD (s.NHf + 1 + 1) {}).m / 2 ^ s.lmbH = 1 ∧
      planeCols x.g1.shape s.lmbH ≤ (hp.tl.mats.getD (s.NHf + 1 + 1) {}).k := by
  simp only [planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  rw [h_shape_is s Y hp cov plain F G c c' x hr (made_of_test b1)]
  exact ⟨b2, b3⟩

theorem att_plane_nums {P : Attention.Plan} {F G : Fork} {c c' : Ctx} {f : Attention.First}
    (hB : planeMatAB P = true) (hr : Attention.hear P F c = .ok ((f, G), c')) :
    (P.mats.getD (P.S.cf.NAs + 2) {}).m / 2 ^ P.S.cf.lmb = 1 ∧
      planeCols f.g.shape P.S.cf.lmb ≤ (P.mats.getD (P.S.cf.NAs + 2) {}).k := by
  simp only [planeMatAB, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  rw [a_shape_is P F G c c' f hr (made_of_test b1)]
  exact ⟨b2, b3⟩

end Fo
