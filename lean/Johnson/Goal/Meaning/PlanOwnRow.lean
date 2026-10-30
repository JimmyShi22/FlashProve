-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PlanOwnRow.lean: the library's stated row row_glue_plan_A
(OnBytes/Tie/Pv/Tail/GlueRows.lean), to the letter; and all twelve sizes of an attention sub-proof's
own rounds against its plan, wherever publicOf returns.

Johnson/Goal/Meaning/PlanOwn.lean has the row's conclusion under two more premises (profile 4; a
group below the number of groups), by steps of its own. The library's Fo.Pub.public_A
(OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean) says more under the row's own premises: a member a of
X.A is a plan a0 that Attention.plan has made, but for one field of its seam. So:

  glue_plan_A_row   row_glue_plan_A: at every profile and every g.
  own_of_public     wherever publicOf returns X and X.A[g]? = some a: the eleven equations
                    OwnOfShape a (Johnson/Goal/Meaning/PlanOwn.lean), with no premise on scope or on
                    g.
  own_rows          the twelfth field, rows: the library's Fo.Pub.public_A_rows, named here beside
                    the eleven.

What is not claimed. Nothing on what a block does with these numbers. Nothing on soundness.
-/
import Johnson.Goal.Meaning.PlanOwn
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Tail.GlueRows

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)

/-- **The row, to the letter.** -/
theorem glue_plan_A_row : OnBytes.Tie.Pv.Tail.GlueRows.row_glue_plan_A := by
  intro pol KL layout X h g a ha
  obtain ⟨_, _, cf, a0, _, _, _, m2, e, _, _⟩ := Fo.Pub.public_A h g a ha
  exact ⟨_, _, cf, a0, m2, by rw [e], by rw [e]⟩

/-- **Wherever publicOf returns: eleven sizes of the own rounds are the shape's.** -/
theorem own_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) {g : ℕ} {a : Attention.Plan} (ha : X.A[g]? = some a) :
    OwnOfShape a := by
  obtain ⟨_, _, _, P0, hp, eS, eO⟩ := glue_plan_A_row pol KL lay X h g a ha
  have O := plan_own hp
  exact ⟨by rw [eO, eS]; exact O.lt, by rw [eO, eS]; exact O.lgk, by rw [eO, eS]; exact O.pairs,
    by rw [eO, eS]; exact O.Lam, by rw [eO, eS]; exact O.planeMessages,
    by rw [eO, eS]; exact O.score, by rw [eO, eS]; exact O.e, by rw [eO, eS]; exact O.valueM,
    by rw [eO, eS]; exact O.valueD, by rw [eO, eS]; exact O.attained, by rw [eO, eS]; exact O.bits⟩

/-- The twelfth: the rows of the batching round. -/
theorem own_rows {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) {g : ℕ} {a : Attention.Plan} (ha : X.A[g]? = some a) :
    a.own.rows = a.nLin +
      a.seam.tl.equationsF (Attention.tableReads a.S (Attention.Counts.of a.S)) :=
  Fo.Pub.public_A_rows h g a ha

end Meaning

#print axioms Meaning.glue_plan_A_row
#print axioms Meaning.own_of_public
#print axioms Meaning.own_rows
