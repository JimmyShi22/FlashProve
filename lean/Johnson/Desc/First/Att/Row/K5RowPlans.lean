-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowPlans.lean: **KIND K5's ROW OF "THE FOURTEEN", STRAIGHT AT THE
TWELVE PLANS**: where the ground's attention segments are the twelve, the public data have a plan at
each group, ONE BOOL ACCEPTS AT EACH PLAN, and "before" is the written one at each group: (i) the
kind's lot returns its twelve sub-protocols · (ii) each has the columns of its row of the written
cut · (iii) each one's test on the plan is true. The three conjuncts are those of k5_row
(Johnson/Desc/First/Att/Row/K5Row.lean), sign for sign. NOTHING IS EVALUATED; NO WRITTEN VALUE IS
NAMED.
TWO ROADS, NOT AN ELDER AND A NEWER. k5_row asks seven equations by field between each plan and
written values: just what the lot reads. Here the Bool is asked at the plan itself and these
equations fall away; k5_row follows from this theorem. BUT A KERNEL CAN DECIDE k5LotB (P g) ONLY AT
A CLOSED P g, AND THEN THE PREMISE plan IS AN EQUATION OF WHOLE PLANS, fields that the lot never
reads among them: more than what it pays. It suits a payer who has each plan as the value of a
closed term (a twin of the planner's run: none was among the files written with this one). k5LotB's
third conjunct is the TWIN of the claims' tests (claimsOkAtT,
Johnson/Desc/First/Att/Row/K5DryTwin.lean), which is cut for the kernel: its four steps, and then
the whole, were decided by the kernel at literals made up for the probes (probes, made for
no build of the library); at no plan of any public file. claimsOkAtO_T there says that it is the
lot's own test.

Main names (namespace H2K5.Row). (k5LotB IS NOT P1K2.k5PlanB, Johnson/P1K2R/PlanBools.lean: that is
a test on the public part at a segment, for kind K2's law.)
  **k5LotB a**: the rounds' number off a.own is 162 · the test on a.own · claimsOkAtT a.
    k5LotB_gives: its parts, the third as claimsOkAtO a = true.
  **k5_row_plans** · **k5_row_plans_alone** (at the seat: IM.LaidAlone, Johnson/IMR/SeatForm.lean).
IS IT EMPTY HERE? IMPLICATIONS. THAT k5LotB ACCEPTS AT ANY PLAN OF ANY PUBLIC FILE IS NOT SHOWN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowSeat
import Johnson.Desc.First.Att.Row.K5DryTwin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.PlanWritten (cutOf toldRounds)

/-- **The Bool at a plan.** -/
def k5LotB (a : Attention.Plan) : Bool := decide (nRounds a.own = 162) && planOkOwn a.own && claimsOkAtT a

/-- What its accept says. -/
theorem k5LotB_gives {a : Attention.Plan} (h : k5LotB a = true) : nRounds a.own = 162 ∧ planOkOwn a.own = true ∧ claimsOkAtO a = true := by
  unfold k5LotB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, (claimsOkAtO_T a).trans h.2⟩

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : ℕ → Attention.Plan}

/-- **THE ROW, STRAIGHT AT THE TWELVE PLANS.** -/
theorem k5_row_plans (places : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g))
    (plan : ∀ g, g < 12 → G.W.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hb : ∀ g, g < 12 → H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)]) :
    H2K5.k5OwnN Z G = (List.range 12).map (the_block Z G P) ∧
      (∀ g, g < 12 →
        (the_block Z G P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G P g).rounds.length = 162 ∧
          (the_block Z G P g).oracles.length = 162 ∧ toldRounds (the_block Z G P g) = [] ∧
          (the_block Z G P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G P g).planOk = true := by
  refine ⟨k5OwnN_at Z G P places plan, fun g hg => ⟨rfl, ?_, ?_, ?_, ?_⟩, fun g hg => ?_⟩
  · exact (blockAt_rounds (W := G.W) (l := 2 * g + 1) (p := P g)).trans (k5LotB_gives (hB g hg)).1
  · exact (blockAt_oracles (W := G.W) (l := 2 * g + 1) (p := P g)).trans (k5LotB_gives (hB g hg)).1
  · exact blockAt_told (W := G.W) (l := 2 * g + 1) (p := P g)
  · show (H2K5.k5Before? Z ("A" ++ toString g)).getD [] = _
    rw [hb g hg]
    rfl
  · show ((planOk (parAt G.W (2 * g + 1) (P g) _) && claimsOkAtO (P g)) && (H2K5.k5Before? Z ("A" ++ toString g)).isSome) = true
    rw [planOk_own, (k5LotB_gives (hB g hg)).2.1, (k5LotB_gives (hB g hg)).2.2, hb g hg]
    rfl

/-- **The like at the seat.** -/
theorem k5_row_plans_alone (places : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g))
    (plan : ∀ g, g < 12 → G.W.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hb : ∀ g, g < 12 → H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)]) {g : ℕ} (hg : g < 12) {same : S → S → Bool}
    {b : Block S ProofFile.Cl} {name : String} {a : Place} (la : IM.LaidAlone same b (the_block Z G P g) name a) :
    cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 * g)])] ∧ b.planOk = true := by
  obtain ⟨-, h2, h3⟩ := k5_row_plans places plan hB hb
  obtain ⟨-, r, o, t, bf⟩ := h2 g hg
  refine ⟨?_, (IM.alone_planOk la).trans (h3 g hg)⟩
  have ht : toldRounds b = toldRounds (the_block Z G P g) := by
    unfold toldRounds
    rw [IM.alone_oracles la]
  show [(b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)] = _
  rw [IM.alone_name la, IM.alone_place la, IM.alone_rounds la, IM.alone_oracles la, ht, IM.alone_before la, r, o, t, bf]

end H2K5.Row

#print axioms H2K5.Row.k5LotB_gives
#print axioms H2K5.Row.k5_row_plans
#print axioms H2K5.Row.k5_row_plans_alone
