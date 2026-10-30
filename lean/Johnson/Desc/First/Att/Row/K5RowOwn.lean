-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowOwn.lean: **KIND K5's ROW OF "THE FOURTEEN" WITHOUT THE BINDER
plan.** In k5_row_madeQ (Johnson/Desc/First/Att/Row/K5RowMadeQ.lean) P is a free letter that the
binder plan pins (Z.p.X.A[g]? = some (P g)). That a plan stands at each g below 12 is already a
theorem (IM.ground_tails, Johnson/IMR/K8Seat.lean, from hS · hR · hZ · hG). So plan falls, and the
three facts on a plan are asked OF WHATEVER PLAN STANDS THERE. A joining: calls, and one choice.
NOTHING IS EVALUATED.
THE EIGHT BINDERS: hS · hR · hZ · hG · h₁ · h₂ · h₄ (each: at every g below 12 and every a with
Z.p.X.A[g]? = some a) · hm.

Main names (namespace H2K5.Row):
  k5_plans_exist: from hS · hR · hZ · hG: there is P with Z.p.X.A[g]? = some (P g) at every
    g below 12. No default plan is used: P is chosen.
  **k5_row_own**: the eight → there is such a P, and the row's three conjuncts hold at it.
  **k5_lot_skel_own**: the eight → the lot's skeleton is the written one: NO P STANDS IN ITS END.
IS IT EMPTY HERE? IMPLICATIONS. NONE OF hZ · hG · h₁ · h₂ · h₄ · hm IS SHOWN AT ANY PUBLIC FILES;
hS · hR are the goals' own premises: of them this file shows nothing either. h₄ IS STILL A WALK AT
EACH PLAN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowMadeQ
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P (claimsOkAtQ)
open VerifiableInference.PlanWritten (toldRounds)
open VerifiableInference.Number.ByRuns (proofThree)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **A plan stands at each of the twelve groups of the public part's own public data.** -/
theorem k5_plans_exist (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) : ∃ P : ℕ → Attention.Plan, ∀ g, g < 12 → Z.p.X.A[g]? = some (P g) := by
  have ex : ∀ g, g < 12 → ∃ a, Z.p.X.A[g]? = some a := by
    intro g hg
    obtain ⟨_, a, _, _, _, ha, _⟩ := (IM.ground_tails hS hR hZ hG).1 g hg
    exact ⟨a, by rw [← ground_W hG]; exact ha⟩
  refine ⟨fun g => if h : g < 12 then Classical.choose (ex g h) else Classical.choose (ex 0 (by omega)), fun g hg => ?_⟩
  simp only [dif_pos hg]
  exact Classical.choose_spec (ex g hg)

/-- **THE ROW, WITHOUT THE BINDER plan.** -/
theorem k5_row_own (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (h₁ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → nRounds a.own = 162)
    (h₂ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → planOkOwn a.own = true) (h₄ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → claimsOkAtQ a = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ∃ P : ℕ → Attention.Plan, (∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) ∧
      H2K5.k5OwnN Z G₀ = (List.range 12).map (the_block Z G₀ P) ∧
      (∀ g, g < 12 →
        (the_block Z G₀ P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G₀ P g).rounds.length = 162 ∧
          (the_block Z G₀ P g).oracles.length = 162 ∧ toldRounds (the_block Z G₀ P g) = [] ∧
          (the_block Z G₀ P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G₀ P g).planOk = true := by
  obtain ⟨P, plan⟩ := k5_plans_exist hS hR hZ hG
  exact ⟨P, plan, k5_row_madeQ hS hR hZ hG plan (fun g hg => h₁ g hg _ (plan g hg)) (fun g hg => h₂ g hg _ (plan g hg))
    (fun g hg => h₄ g hg _ (plan g hg)) hm⟩

/-- **THE LOT's SKELETON IS THE WRITTEN ONE, WITHOUT THE BINDER plan: NO P IN ITS END.** -/
theorem k5_lot_skel_own (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (h₁ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → nRounds a.own = 162)
    (h₂ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → planOkOwn a.own = true) (h₄ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → claimsOkAtQ a = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ProofFile.Sk.lotSk G₀ (H2K5.lotN Z) =
      { name := "K5: the attention segments' own rounds", letters := false, still := [], blocks := (List.range 12).map k5SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  obtain ⟨P, plan⟩ := k5_plans_exist hS hR hZ hG
  exact k5_lot_skel_madeQ hS hR hZ hG plan (fun g hg => h₁ g hg _ (plan g hg)) (fun g hg => h₂ g hg _ (plan g hg))
    (fun g hg => h₄ g hg _ (plan g hg)) hm

end H2K5.Row

#print axioms H2K5.Row.k5_plans_exist
#print axioms H2K5.Row.k5_row_own
#print axioms H2K5.Row.k5_lot_skel_own
