-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ShapesReadOfArms.lean: THE 25 EQUATIONS OF `ShapesRead` ON THE SUB-PROOFS'
ROUTINES, FROM THE 26 ARMS; and the structure put together at what `shapesWith` returns.
(`ShapesRead`: Johnson/AtFull/Made/Gates.lean: all that the planner's six gates read
of the run's shapes and of the first plan.) Two small closed facts and joinings. A law file; no
running text imports it. Nothing on codes.

Why. The first gate calls `x.sub.plan j m`: closures over the whole public part. By `plan_at_arms`
(Johnson/AtFull/Rows/ArmRounds.lean) these are closed terms where the arms are the written ones; the
25 links have four distinct arms; each arm's count stands in a file of its own
(Johnson/AtFull/Rows/CountHead, CountAtt, CountLayerFirst, CountLayer).

  `moments_full`, `four_pairs`: closed facts on the written lists. `count_at`: at each link the
    written arm's rounds send the written number.
  `scalars_of_arms`: armsB X = true ⊢ `ShapesRead.scalars`, to the letter, at x.sub :=
    subproofsWith X rl.
  `shapesRead_of_arms`: the structure, at x := ⟨subproofsWith X rl, lay, ids, sh, rc⟩. OF ITS FIVE
    FIELDS ONE IS THE WORK: scalars ← armsB. pending ← NGr = 12. checks ← rc = `checksFull`, which
    asks more than the field (from `rangeChecks_written`, RangeChecksReturn.lean). identifiers AND
    lists: THE PREMISE IS THE FIELD: handed through.

Limits. EVERY PREMISE IS A PREMISE: armsB is shown at no files. THE FIRST GATE DOES NOT HANG ON
armsB ALONE: its other premise, on the first plan's lists, is handed through here, and the first
plan is itself made by running the same routines. The premises of `rangeChecks_written` are a debt
beside armsB. THE COST LIES BENEATH: the four files of counts (their heads have the measures).
`scalarsFull`, `checksFull`, `listsFull` were copied off a run (their files' heads). The full size
alone. Nothing on soundness.

-/
import Johnson.AtFull.Made.Gates
import Johnson.AtFull.Made.RangeChecksReturn
import Johnson.AtFull.Rows.CountHead
import Johnson.AtFull.Rows.CountAtt
import Johnson.AtFull.Rows.CountLayerFirst
import Johnson.AtFull.Rows.CountLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model.Verify AtFull.Rows
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.PlanWritten.Joined (writtenSized)

/-! ## 1 Closed facts on the written lists -/

set_option maxRecDepth 1000000 in
/-- The written request has 25 links, and each has three moments. -/
theorem moments_full : writtenSized.proof.request.link.length = 25 ∧
    (writtenSized.proof.request.link.all fun x => momentsOf x == 3) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the 25 links has one of four written arms, and with it that arm's written count. -/
theorem four_pairs : ∀ j, j < 25 →
    (armAtW j = armAtW 0 ∧ scalarsFull.getD j 0 = 4059) ∨
    (armAtW j = armAtW 1 ∧ scalarsFull.getD j 0 = 4190) ∨
    (armAtW j = armAtW 2 ∧ scalarsFull.getD j 0 = 4058) ∨
    (armAtW j = armAtW 24 ∧ scalarsFull.getD j 0 = 3570) := by
  decide +kernel

/-- **At each of the 25 links the written arm's rounds send the written number of scalars.** -/
theorem count_at (j : Nat) (hj : j < 25) : armCount (armAtW j) = .ok (scalarsFull.getD j 0) := by
  rcases four_pairs j hj with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
    exact count_layerFirst
  · rw [e1, e2]
    exact count_att
  · rw [e1, e2]
    exact count_layer
  · rw [e1, e2]
    exact count_head

/-! ## 2 The 25 equations, from the arms -/

/-- The count hangs on the number of moments and on the routine. -/
theorem count_congr (s : Setting) (n : Nat) (f g : Nat → Planning Unit) (h1 : n = 3)
    (h2 : f = g) :
    scalarsOf s (forEach (List.range n) f) = scalarsOf s (forEach (List.range 3) g) := by
  rw [h1, h2]

/-- At a link below 25 and any entry with three moments. -/
theorem count_gen {X : Public} (ha : armsB X = true) (rl : List ReqLink) (j : Nat) (h25 : j < 25)
    (x : ReqLink) (hx : momentsOf x = 3) :
    scalarsOf writtenSized.proof.set
      (forEach (List.range (momentsOf x)) fun m => (subproofsWith X rl).plan j m) =
        .ok (scalarsFull.getD j 0) :=
  (count_congr _ _ _ (fun m => armRounds (armAtW j) m) hx
    (funext fun m => plan_at_arms ha rl j (Nat.lt_succ_of_lt h25) m)).trans (count_at j h25)

/-- **`ShapesRead.scalars`, to the letter, at x.sub := subproofsWith X rl, from armsB.** -/
theorem scalars_of_arms {X : Public} (ha : armsB X = true) (rl : List ReqLink) :
    ∀ j (hj : j < writtenSized.proof.request.link.length) (hj' : j < scalarsFull.length),
      scalarsOf writtenSized.proof.set
        (forEach (List.range (momentsOf writtenSized.proof.request.link[j])) fun m =>
          (subproofsWith X rl).plan j m) = .ok scalarsFull[j] := by
  intro j hj hj'
  have h25 : j < 25 := by
    rw [moments_full.1] at hj
    exact hj
  have e := count_gen ha rl j h25 (writtenSized.proof.request.link[j]'hj)
    (eq_of_beq (List.all_eq_true.1 moments_full.2 _ (List.getElem_mem hj)))
  rw [List.getD_eq_getElem scalarsFull 0 hj'] at e
  exact e

/-! ## 3 The structure, put together -/

/-- **`ShapesRead` at what `shapesWith` returns.** scalars from the arms; pending from the number of
groups; checks from the written list; identifiers and lists are handed through. -/
theorem shapesRead_of_arms {X : Public} {rl : List ReqLink} {lay : ReqLayout} {ids : List Nat}
    {sh : Plan.Shape} {rc : List RangeCheck} {first : Params.Planned} (hN : X.NGr = 12)
    (ha : armsB X = true) (hi : ids.length = 25) (hc : rc = checksFull)
    (hl : listsOf first = listsFull) :
    ShapesRead { sub := subproofsWith X rl, layout := lay, identifiers := ids, ranges := sh,
                 rangeChecks := rc } first where
  pending := by
    show X.NGr + 1 = 13
    rw [hN]
  identifiers := hi
  checks := by
    show rc.map rangeCheckBits = _
    rw [hc]
  lists := hl
  scalars := scalars_of_arms ha rl

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.moments_full
#print axioms Johnson.AtFull.Made.four_pairs
#print axioms Johnson.AtFull.Made.count_at
#print axioms Johnson.AtFull.Made.count_congr
#print axioms Johnson.AtFull.Made.count_gen
#print axioms Johnson.AtFull.Made.scalars_of_arms
#print axioms Johnson.AtFull.Made.shapesRead_of_arms
