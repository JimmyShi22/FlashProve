-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`Johnson/G/PackLitArms.lean`: at every sampled message of the library's full-size list `Johnson.G.packFullLit`, the
decoding radius lies within the Johnson bound and at or beyond half the message's distance.

The list `Johnson.G.packFullLit` is written out in the library. It has 119 entries (the library calls them sendings)
with 207 sampled messages in all, each with a decoding radius `e`. A message's distance is `Johnson.Pack.dOf`: the
distance of the mask rows' code if the message has no main row, of the main rows' code if it has no mask row, and the
smaller of the two if it has both.

What this file proves.
* `every_message_is_within_johnson_and_at_or_beyond_half`: for every message of the list, its out-of-domain sample has
  one answer, one of the cases `CaseE`, `CaseF` holds, the pad fits (`PadFits`), the radius meets the library's
  Johnson condition `Cb.InJohnson` at length `2 ^ aOf` and distance `dOf`, and `dOf ≤ 2 * e`.
* `every_message_meets`: every message of the list meets `Johnson.Pack.MeetsAt`, the condition of the library's
  statement on sendings, at the distance `dOf` and the list bound `lOf`.
* `checker_tests_the_johnson_condition`: for any codes, shape and radius, if the library's checker `meetsB` returns
  true, then the first four clauses above hold.
* `cases_apart`: `CaseE` (the pad lies in a row over the extension field) and `CaseF` (the whole message is over the
  base field) exclude each other.
* `all_at_or_beyond_half_the_distance`, `all_have_a_row`, `counts`: evaluated on the list by Lean's kernel: `dOf ≤ 2 *
  e` at every message; every message has a row; 119 entries, 207 messages, 122 in `CaseE`, 85 in `CaseF`.
* `at_or_beyond_can_fail`: the test `atOrBeyondHalf` is not vacuous: at the radius 0 it returns false at the first
  message.

What this file does not say.
* The list is a literal. That it is what the planner of the verifier on bytes computes from the public files is
  checked in the library by evaluation alone (`#guard packFullLit == packFull`, `Johnson/G/PackLit.lean`), at the
  three files of the shipped full-size example. Nothing here ties it to `VerifierAndGoals.storedPublicFiles`, to public files in scope, or
  to the protocol object `protocolAtFiles Z`. For its radii see `E2E/PackRadiiAreThePlans.lean`. The map from a message to its
  radius has the limits stated in `Johnson/G/PackList.lean`.
* Which lists the soundness theorem uses is not shown here.
* The list holds only the messages of sendings that carry an out-of-domain sample. The committed table is not among
  them; `E2E/SampleAndJohnsonInScope.lean` has its radius.
* The distance is `dOf`, as defined above. Of the larger of the two codes' distances, at a message with both kinds of
  rows, nothing is said.
* "Distance" is the library's number for a Reed-Solomon code as read at the message's length (`Johnson.Pack.distAt`):
  length less dimension plus 1, times the number of repeats. That it is the code's minimum distance, and no more than
  it, is not proved here.
* Nothing is said on which theorem bounds the soundness error of a proximity round.
-/
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.PackArms
open Johnson.G Johnson.Pack OnBytes Cb

section General
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape)

/-- **What the library's checker tests**: one answer to the message's sample, one of the two cases, room for the pad, and the Johnson condition at the shape's own distance. -/
theorem checker_tests_the_johnson_condition {e : ℕ} (h : meetsB cs s e = true) :
    s.answers = 1 ∧ (CaseE s ∨ CaseF s) ∧ PadFits cs s ∧ InJohnson (2 ^ aOf cs s) (dOf cs s) e := by
  unfold meetsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- The two cases exclude each other. -/
theorem cases_apart : ¬ (CaseE s ∧ CaseF s) := by
  rintro ⟨hE, hF⟩
  unfold CaseE at hE
  unfold CaseF at hF
  omega

end General

/-- The test: the radius is at least half the shape's distance. -/
def atOrBeyondHalf (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ) : Bool := decide (dOf cs s ≤ 2 * e)

set_option maxRecDepth 1000000 in
/-- **At all sampled messages of the full-size list the radius is at least half the distance.** By Lean's kernel. -/
theorem all_at_or_beyond_half_the_distance : (packFullLit.all fun x => x.2.all fun y => atOrBeyondHalf x.1 y.1 y.2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each has a row. -/
theorem all_have_a_row :
    (packFullLit.all fun x => x.2.all fun y => decide (y.1.mainRows ≠ 0 ∨ y.1.maskRows ≠ 0)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- 119 sendings; 207 sampled messages; 122 in the case over the extension field, 85 in the case over the base field. -/
theorem counts :
    packFullLit.length = 119 ∧ (packFullLit.map (·.2.length)).sum = 207 ∧
      (packFullLit.map fun x => (x.2.filter fun y => decide (CaseE y.1)).length).sum = 122 ∧
      (packFullLit.map fun x => (x.2.filter fun y => decide (CaseF y.1)).length).sum = 85 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test can fail: at the list's first message with the radius 0 it returns false. -/
theorem at_or_beyond_can_fail :
    ((packFullLit.head?.bind fun x => x.2.head?.map fun y => atOrBeyondHalf x.1 y.1 0) = some false) := by
  decide +kernel

/-- **THE STATEMENT: at every sampled message of the full-size list**: its out-of-domain sample has one answer; the radius lies within the Johnson condition at the shape's own distance, and
at or beyond half that distance. -/
theorem every_message_is_within_johnson_and_at_or_beyond_half :
    ∀ x ∈ packFullLit, ∀ y ∈ x.2,
      y.1.answers = 1 ∧ (CaseE y.1 ∨ CaseF y.1) ∧ PadFits x.1 y.1 ∧ InJohnson (2 ^ aOf x.1 y.1) (dOf x.1 y.1) y.2 ∧
        dOf x.1 y.1 ≤ 2 * y.2 := by
  intro x hx y hy
  obtain ⟨h1, h2, h3, h4⟩ := checker_tests_the_johnson_condition x.1 y.1
    (List.all_eq_true.1 (List.all_eq_true.1 packFullLit_meets x hx) y hy)
  exact ⟨h1, h2, h3, h4,
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 all_at_or_beyond_half_the_distance x hx) y hy)⟩

/-- The condition of the statement on sendings holds of each, at its own distance and the library's list bound (the library's packFullLit_meets). -/
theorem every_message_meets :
    ∀ x ∈ packFullLit, ∀ y ∈ x.2, MeetsAt x.1 y.1 y.2 (dOf x.1 y.1) (lOf x.1 y.1 y.2) := by
  intro x hx y hy
  exact meetsB_sound x.1 y.1 y.2
    (List.all_eq_true.1 (List.all_eq_true.1 packFullLit_meets x hx) y hy)

end Johnson.G.PackArms

#print axioms Johnson.G.PackArms.checker_tests_the_johnson_condition
#print axioms Johnson.G.PackArms.cases_apart
#print axioms Johnson.G.PackArms.all_at_or_beyond_half_the_distance
#print axioms Johnson.G.PackArms.all_have_a_row
#print axioms Johnson.G.PackArms.counts
#print axioms Johnson.G.PackArms.at_or_beyond_can_fail
#print axioms Johnson.G.PackArms.every_message_is_within_johnson_and_at_or_beyond_half
#print axioms Johnson.G.PackArms.every_message_meets
#check @Johnson.G.PackArms.every_message_is_within_johnson_and_at_or_beyond_half
