-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowMade.lean: **KIND K5's ROW OF "THE FOURTEEN": ITS LEDGER AT SEVEN
BINDERS.** The row where the front of the proof file's IOP's maker has returned (k5_row_front,
Johnson/Desc/First/Att/Row/K5RowFront.lean), with its two equations by field on the public part paid
by hc_made | hD_made (Johnson/Desc/First/Att/Row/K5FrontOne.lean) from the front's return and ONE
equation on the planner's three lists. A joining: one call each. NOTHING IS EVALUATED.
THE SEVEN: hS · hR: the goals' scope; the public files are read · hZ: the front's return · hG: the
seat's ground is made: no lot's · plan: the public part's own public data have the plan P g at each
of the twelve groups · hB: one Bool accepts at each plan (k5LotB) · hm: the planner's three lists
for the proof file are the written ones
(Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]).

Main names (namespace H2K5.Row):
  **k5_row_made**: the seven → (i) the kind's lot returns its twelve sub-protocols · (ii) each has
    the columns of its row of the written cut · (iii) each one's test on the plan is true.
  **k5_row_made_alone**: the like at the seat (IM.LaidAlone, Johnson/IMR/SeatForm.lean; the name and
    the place are the seat's letters).
  **k5_lot_skel_made**: the lot's skeleton is the written one (in the form ProofFile.Sk.lotSk,
    Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean: by k5_lot_skel,
    Johnson/Desc/First/Att/Row/K5RowSkel.lean), from the same seven.
OF plan THE HALF "there is a plan at each g below 12" IS ALREADY A THEOREM (IM.ground_tails,
Johnson/IMR/K8Seat.lean, from hS · hR · hZ · hG): what is owed is WHICH plan stands there.
IS IT EMPTY HERE? IMPLICATIONS. NONE OF hZ · hG · plan · hB · hm IS SHOWN AT ANY PUBLIC FILES;
hS · hR are the goals' own premises: of them this file shows nothing either.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowFront
import Johnson.Desc.First.Att.Row.K5RowSkel
import Johnson.Desc.First.Att.Row.K5FrontOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutOf toldRounds)
open VerifiableInference.Number.ByRuns (proofThree)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : ℕ → Attention.Plan}

/-- **THE ROW, AT SEVEN BINDERS.** -/
theorem k5_row_made (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    H2K5.k5OwnN Z G₀ = (List.range 12).map (the_block Z G₀ P) ∧
      (∀ g, g < 12 →
        (the_block Z G₀ P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G₀ P g).rounds.length = 162 ∧
          (the_block Z G₀ P g).oracles.length = 162 ∧ toldRounds (the_block Z G₀ P g) = [] ∧
          (the_block Z G₀ P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G₀ P g).planOk = true :=
  k5_row_front hS hR hZ hG plan hB (hc_made hZ hm) (hD_made hZ hm)

/-- **The like at the seat.** -/
theorem k5_row_made_alone (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) {g : ℕ} (hg : g < 12) {same : S → S → Bool}
    {b : Block S ProofFile.Cl} {name : String} {a : Place} (la : IM.LaidAlone same b (the_block Z G₀ P g) name a) :
    cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 * g)])] ∧ b.planOk = true :=
  k5_row_front_alone hS hR hZ hG plan hB (hc_made hZ hm) (hD_made hZ hm) hg la

/-- **The lot's skeleton is the written one, from the same seven.** -/
theorem k5_lot_skel_made (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ProofFile.Sk.lotSk G₀ (H2K5.lotN Z) =
      { name := "K5: the attention segments' own rounds", letters := false, still := [], blocks := (List.range 12).map k5SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } :=
  k5_lot_skel (k5Places_scope hS hR hZ hG) (plan_at_ground hG plan) hB (k5Before_of_pairs (hc_made hZ hm) (hD_made hZ hm))

end H2K5.Row

#print axioms H2K5.Row.k5_row_made
#print axioms H2K5.Row.k5_row_made_alone
#print axioms H2K5.Row.k5_lot_skel_made
