-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowFront.lean: **KIND K5's ROW OF "THE FOURTEEN", WHERE THE FRONT OF
THE PROOF FILE's IOP's MAKER HAS RETURNED THE PUBLIC PART: THE ROW's WHOLE LEDGER IN ONE THEOREM's
BINDERS.** A joining: calls alone. NOTHING IS EVALUATED.
THE BINDERS, AND WHOSE EACH IS TO PAY: hS · hR: the goals' scope; the public files are read · hZ:
the front's return (ProofFile.pubPlain … = .ok Z) · hG: the seat's ground is made
(ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀): no lot's · plan: the public part's own public data
have a plan at each of the twelve groups (Z.p.X.A[g]? = some (P g)) · hB: one Bool accepts at each
plan (k5LotB, Johnson/Desc/First/Att/Row/K5RowPlans.lean) · hc · hD: two equations by field of Z
against written values (Johnson/Desc/First/Att/Row/K5BeforeWritten.lean).
THE END: k5_row_plans' three conjuncts: (i) the kind's lot returns its twelve sub-protocols ·
(ii) each has the columns of its row of the written cut · (iii) each one's test on the plan is true.

Main names (namespace H2K5.Row): **k5_row_front** · **k5_row_front_alone** (at the seat:
IM.LaidAlone, Johnson/IMR/SeatForm.lean; the name and the place are the seat's letters).
OF plan THE HALF "there is a plan at each g below 12" IS ALREADY A THEOREM (IM.ground_tails,
Johnson/IMR/K8Seat.lean, from hS · hR · hZ · hG): what is owed is WHICH plan stands there: P is a
letter that plan pins, for a payer who holds the plans as closed terms.
WHAT THE ROW's SENTENCE ASKS AND THIS FILE LEAVES OUTSIDE: the name and the place at the seat
(the seat's letters: the payer of the spots owes them) · THAT G₀ IS THE GROUND WHICH THE SEAT HANDS
THE LOT: said by reading in K5RowSeat.lean's head; no lemma ties the chain's maker's own call to
blankBy's value: whoever joins the fourteen rows owes it.
IS IT EMPTY HERE? AN IMPLICATION. NONE OF hZ · hG · plan · hB · hc · hD IS SHOWN AT ANY PUBLIC
FILES. The payers of hD stand under the head: not for a member of
the head (K5BeforeWritten.lean, its head).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowPlans
import Johnson.Desc.First.Att.Row.K5BeforeWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutOf toldRounds)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : ℕ → Attention.Plan}

/-- The plans at the ground, off the public part's. -/
theorem plan_at_ground (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (g : ℕ) (hg : g < 12) :
    G₀.W.A[g]? = some (P g) := by
  rw [ground_W hG]
  exact plan g hg

/-- **THE ROW, WHERE THE FRONT HAS RETURNED.** -/
theorem k5_row_front (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hc : (Z.cuts.map fun c => (c.look, c.take)) = cutPairsW) (hD : Z.D.1.map (·.entry) = P5T.esFull.1) :
    H2K5.k5OwnN Z G₀ = (List.range 12).map (the_block Z G₀ P) ∧
      (∀ g, g < 12 →
        (the_block Z G₀ P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G₀ P g).rounds.length = 162 ∧
          (the_block Z G₀ P g).oracles.length = 162 ∧ toldRounds (the_block Z G₀ P g) = [] ∧
          (the_block Z G₀ P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G₀ P g).planOk = true :=
  k5_row_plans (k5Places_scope hS hR hZ hG) (plan_at_ground hG plan) hB (k5Before_of_pairs hc hD)

/-- **The like at the seat.** -/
theorem k5_row_front_alone (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hc : (Z.cuts.map fun c => (c.look, c.take)) = cutPairsW) (hD : Z.D.1.map (·.entry) = P5T.esFull.1) {g : ℕ} (hg : g < 12) {same : S → S → Bool}
    {b : Block S ProofFile.Cl} {name : String} {a : Place} (la : IM.LaidAlone same b (the_block Z G₀ P g) name a) :
    cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 * g)])] ∧ b.planOk = true :=
  k5_row_plans_alone (k5Places_scope hS hR hZ hG) (plan_at_ground hG plan) hB (k5Before_of_pairs hc hD) hg la

end H2K5.Row

#print axioms H2K5.Row.plan_at_ground
#print axioms H2K5.Row.k5_row_front
#print axioms H2K5.Row.k5_row_front_alone
