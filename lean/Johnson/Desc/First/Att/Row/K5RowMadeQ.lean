-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowMadeQ.lean: **KIND K5's ROW OF "THE FOURTEEN": THE BINDER
"ONE Bool ACCEPTS AT EACH PLAN" OF k5_row_made (Johnson/Desc/First/Att/Row/K5RowMade.lean) IN THREE
SMALLER ONES.** A joining: calls alone. NOTHING IS EVALUATED.
k5LotB a follows from four parts (k5LotB_of_Q, Johnson/Desc/First/Att/Row/K5LotNoPad.lean). One of
them, "the padding keys are 0", is paid here by another file's general law on the maker's text
(padKeyOk_row, Johnson/Desc/First/Att/Row/K5PadKeyOk.lean) from two binders that the row has anyhow:
the front's return and the plan at the group. LEFT: h₁ · h₂: two facts on the plan's field own alone
(as reported, its own_twin (declared nowhere in this library) makes them one closed
fact at a literal: not seen here) · h₄: claimsOkAtQ at the plan
(Johnson/Desc/First/Att/Row/K5DryNoPad.lean): THE ONE WALK: what it costs Lean's kernel where the
plan is no written value is not touched by this file.

Main names (namespace H2K5.Row):
  k5LotB_row: the Bool at a plan of the public part that the front returns, from h₁ · h₂ · h₄.
  **k5_row_madeQ** · **k5_row_madeQ_alone** · **k5_lot_skel_madeQ**: k5_row_made |
    k5_row_made_alone | k5_lot_skel_made with h₁ · h₂ · h₄ in hB's place.
IS IT EMPTY HERE? IMPLICATIONS. NONE OF hZ · hG · plan · h₁ · h₂ · h₄ · hm IS SHOWN AT ANY PUBLIC
FILES; hS · hR are the goals' own premises: of them this file shows nothing either.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowMade
import Johnson.Desc.First.Att.Row.K5LotNoPad
import Johnson.Desc.First.Att.Row.K5PadKeyOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (claimsOkAtQ)
open VerifiableInference.PlanWritten (cutOf toldRounds)
open VerifiableInference.Number.ByRuns (proofThree)

/-- The Bool at a plan of the public part that the front returns. -/
theorem k5LotB_row {pol lay KL : ByteArray} {Z : ProofFile.Pub} {g : ℕ} {a : Attention.Plan} (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (ha : Z.p.X.A[g]? = some a) (h₁ : nRounds a.own = 162) (h₂ : planOkOwn a.own = true) (h₄ : claimsOkAtQ a = true) : k5LotB a = true :=
  k5LotB_of_Q h₁ h₂ (padKeyOk_row hZ ha) h₄

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : ℕ → Attention.Plan}

/-- **THE ROW, WITH THE Bool A PLAN IN THREE SMALLER BINDERS.** -/
theorem k5_row_madeQ (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (h₁ : ∀ g, g < 12 → nRounds (P g).own = 162)
    (h₂ : ∀ g, g < 12 → planOkOwn (P g).own = true) (h₄ : ∀ g, g < 12 → claimsOkAtQ (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    H2K5.k5OwnN Z G₀ = (List.range 12).map (the_block Z G₀ P) ∧
      (∀ g, g < 12 →
        (the_block Z G₀ P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G₀ P g).rounds.length = 162 ∧
          (the_block Z G₀ P g).oracles.length = 162 ∧ toldRounds (the_block Z G₀ P g) = [] ∧
          (the_block Z G₀ P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G₀ P g).planOk = true :=
  k5_row_made hS hR hZ hG plan (fun g hg => k5LotB_row hZ (plan g hg) (h₁ g hg) (h₂ g hg) (h₄ g hg)) hm

/-- **The like at the seat.** -/
theorem k5_row_madeQ_alone (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (h₁ : ∀ g, g < 12 → nRounds (P g).own = 162)
    (h₂ : ∀ g, g < 12 → planOkOwn (P g).own = true) (h₄ : ∀ g, g < 12 → claimsOkAtQ (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) {g : ℕ} (hg : g < 12) {same : S → S → Bool}
    {b : Block S ProofFile.Cl} {name : String} {a : Place} (la : IM.LaidAlone same b (the_block Z G₀ P g) name a) :
    cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 * g)])] ∧ b.planOk = true :=
  k5_row_made_alone hS hR hZ hG plan (fun g hg => k5LotB_row hZ (plan g hg) (h₁ g hg) (h₂ g hg) (h₄ g hg)) hm hg la

/-- **The lot's skeleton is the written one, from the same binders.** -/
theorem k5_lot_skel_madeQ (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (plan : ∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) (h₁ : ∀ g, g < 12 → nRounds (P g).own = 162)
    (h₂ : ∀ g, g < 12 → planOkOwn (P g).own = true) (h₄ : ∀ g, g < 12 → claimsOkAtQ (P g) = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ProofFile.Sk.lotSk G₀ (H2K5.lotN Z) =
      { name := "K5: the attention segments' own rounds", letters := false, still := [], blocks := (List.range 12).map k5SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } :=
  k5_lot_skel_made hS hR hZ hG plan (fun g hg => k5LotB_row hZ (plan g hg) (h₁ g hg) (h₂ g hg) (h₄ g hg)) hm

end H2K5.Row

#print axioms H2K5.Row.k5LotB_row
#print axioms H2K5.Row.k5_row_madeQ
#print axioms H2K5.Row.k5_row_madeQ_alone
#print axioms H2K5.Row.k5_lot_skel_madeQ
