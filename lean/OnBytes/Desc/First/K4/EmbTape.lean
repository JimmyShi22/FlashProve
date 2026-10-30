-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/EmbTape.lean: the first stretch of the layers' own rounds, `hearNorms`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl` (K4/Plain.lean), IN THE FIRST
GROUP: the two points ZE and tkh that it hands back ARE WHAT ROUNDS 1 AND 2 OF THE TAPE DREW. One
statement and its proof.

`hearNorms_tape` (NormsTape.lean) walks past these two rounds to count them, and does not say what
they drew. Here that is said, each point as a FUNCTION OF THE TAPE. No new argument:
`hearNorms_calls` (NormsCalls.lean), `point_spec` (OnBytes/Desc/First/P1/BatchPoint.lean),
`drop_next` (NormsTape.lean).

  `drawnAt t k`: the elements that round number k of the tape t drew; none if the tape has no such
    round.
  `hearNorms_emb_tape`: if `hearNorms engFl P g fo F t` returns (H, G, u) and g is 0, then H.ZE is
    `(drawnAt t 1).toArray`, of P.y.ls + P.y.h.lt elements, and H.tkh is `(drawnAt t 2).toArray`, of
    P.y.lPd - P.y.ls elements.

One direction: from a return. Nothing is said of what the points mean.
-/
import OnBytes.Desc.First.K4.NormsTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
open OnBytes.Desc.First.P1 (point_spec)

/-- What round number k of the tape drew; nothing if there is no such round. -/
def drawnAt (t : Tape) (k : Nat) : List E := ((t.drop k).head?.map (·.drawn)).getD []

theorem drawnAt_cons {t u : Tape} {k : Nat} {r : FlatRound} (h : t.drop k = r :: u) :
    drawnAt t k = r.drawn := by
  unfold drawnAt
  rw [h]
  rfl

/-- **In the first group the two points are what rounds 1 and 2 of the tape drew.** -/
theorem hearNorms_emb_tape {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (h : hearNorms engFl P g fo F t = some (H, G, u)) (hg : (g == 0) = true) :
    H.ZE = (drawnAt t 1).toArray ∧ (drawnAt t 1).length = P.y.ls + P.y.h.lt ∧
      H.tkh = (drawnAt t 2).toArray ∧ (drawnAt t 2).length = P.y.lPd - P.y.ls := by
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, c1, c2, c3, _⟩ :=
    hearNorms_calls h
  have c1' : Fl.point .zero P.y.h.lt F t = some (H.PV, F1, t1) := c1
  obtain ⟨rfl, w0, d0, e0, _, _⟩ := point_spec c1'
  have p0 : t = t.drop 0 := rfl
  have p1 : t1 = t.drop (0 + 1) := drop_next p0 e0
  simp only [hg, if_true] at c2 c3
  have c2' : Fl.point .zero (P.y.ls + P.y.h.lt) F t1 = some (H.ZE, F2, t2) := c2
  obtain ⟨rfl, w1, d1, e1, l1, hZ⟩ := point_spec c2'
  have c3' : Fl.point .zero (P.y.lPd - P.y.ls) F t2 = some (H.tkh, F3, t3) := c3
  obtain ⟨rfl, w2, d2, e2, l2, hT⟩ := point_spec c3'
  have p2 : t2 = t.drop (0 + 1 + 1) := drop_next p1 e1
  have q1 : drawnAt t 1 = d1 := drawnAt_cons (k := 1) (u := t2) (by rw [← e1]; exact p1.symm)
  have q2 : drawnAt t 2 = d2 := drawnAt_cons (k := 2) (u := t3) (by rw [← e2]; exact p2.symm)
  rw [q1, q2]
  exact ⟨hZ, l1, hT, l2⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hearNorms_emb_tape
