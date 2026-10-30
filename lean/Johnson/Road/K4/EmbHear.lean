-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbHear.lean: what a return of K4's hearing in the first group says of the letters
that the claim on the stream that comes in reads: the group's number, the layout, and the two points
that are drawn in the first group alone.

  `emb_hear`: where `hear` returns over the plain engine in the first group: the environment's group
    is 0 and its layout the public one; the embedding's point ZE is what the tape's second round
    drew, ls + lt elements; its point on the blocks tkh is what the third round drew, lPd - ls
    elements.
  `emb_hear_sizes`: the two arrays' sizes.
Limits. One direction: from a return. What the drawn elements are is not said. Nothing on soundness
or on hiding.


-/
import OnBytes.Desc.First.K4.MergeClaims
import OnBytes.Desc.First.K4.NormsCalls
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.P1.TapeCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (drawnOf point_spec)

/-- **Where the hearing returns in the first group.** -/
theorem emb_hear {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t0 u : Tape}
    {o : Own} (hg : (g == 0) = true) (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    o.v.g = 0 ∧ o.v.y = P.y ∧
      o.H.ZE = (drawnOf (t0.drop 1)).toArray ∧
      (drawnOf (t0.drop 1)).length = P.y.ls + P.y.h.lt ∧
      o.H.tkh = (drawnOf ((t0.drop 1).drop 1)).toArray ∧
      (drawnOf ((t0.drop 1).drop 1)).length = P.y.lPd - P.y.ls := by
  obtain ⟨-, ey, -, eg, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, -⟩ :=
    hear_parts h
  obtain ⟨tT, G1', u1', row, p', -, -, -, b4⟩ := hearTerms_calls h2
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, c1, c2, c3, -⟩ :=
    hearNorms_calls h1
  have c1' : Fl.point .zero P.y.h.lt F t0 = some (H1.PV, F1, t1) := c1
  obtain ⟨rfl, w0, d0, e0, -, -⟩ := point_spec c1'
  simp only [hg, if_true] at c2 c3
  have c2' : Fl.point .zero (P.y.ls + P.y.h.lt) F t1 = some (H1.ZE, F2, t2) := c2
  obtain ⟨rfl, w1, d1, e1, l1, a1⟩ := point_spec c2'
  have c3' : Fl.point .zero (P.y.lPd - P.y.ls) F t2 = some (H1.tkh, F3, t3) := c3
  obtain ⟨rfl, w2, d2, e2, l2, a2⟩ := point_spec c3'
  have z1 : drawnOf (t0.drop 1) = d1 := by
    rw [e0, e1]
    rfl
  have z2 : drawnOf ((t0.drop 1).drop 1) = d2 := by
    rw [e0, e1, e2]
    rfl
  have g0 : g = 0 := by simpa using hg
  refine ⟨eg.trans g0, ey, ?_, ?_, ?_, ?_⟩
  · rw [b4, z1]
    exact a1
  · rw [z1]
    exact l1
  · rw [b4, z2]
    exact a2
  · rw [z2]
    exact l2

/-- The sizes of the two points. -/
theorem emb_hear_sizes {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (hg : (g == 0) = true)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    o.H.ZE.size = P.y.ls + P.y.h.lt ∧ o.H.tkh.size = P.y.lPd - P.y.ls := by
  obtain ⟨-, -, a1, l1, a2, l2⟩ := emb_hear hg h
  refine ⟨?_, ?_⟩
  · rw [a1, List.size_toArray]
    exact l1
  · rw [a2, List.size_toArray]
    exact l2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.emb_hear
#print axioms OnBytes.Road.K4.emb_hear_sizes
