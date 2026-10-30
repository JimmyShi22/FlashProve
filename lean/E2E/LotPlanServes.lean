-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotPlanServes.lean: the plan at the run.



It says: at the offline prover of a description of the public files, in the goals' scope, where ready returns, the plan
serves the rounds (AtRunS's third clause, E2E/KeyAcceptPairs.lean).

How. The library's planServes (Honest/Law/PlanGives.lean) at its three premises. The statement has no protocolDataWellFormed, so KeyNamed
is not at hand: all three are had off the five returns of which offlineDescription is made.
  planOk     Johnson.KB4.key_planOk_in_scope                                   (E2E/LotPlanServesGround.lean: plan)
  rootedAll  the rows off the returns, then rootedAll_key's own proof, at atAll_value
                                                 (Ground: rows · E2E/LotPlanServesValue.lean: rootedAll_of_rows, atAll_offline)
  hst        the declared rounds are the written ones; each stored table that they declare has the item 0, the depth 32, the
             width 2048 (a closed line); the value's column is there below 2^32 with 2^11 entries
                                                 (Ground: decl, stored_decl, widths_of · Value: stored_offline)

What it does not say. The book B, the index w₀, the committer's coins rc, the instance x and the coins c are free letters.
«ready … = .ok R» is a premise: NO FILE THAT WE HAVE SEEN SHOWS THAT ready RETURNS AT THIS PROVER AT ANY BOOK 
(nearest: ready_bare, E2E/KeyStartsBare.lean, at a prover with no half). At
an index out of range it refuses. That offlineDescription returns in scope is a premise too. PlanServes is on what the
rounds declare and on the stored columns' presence and width: nothing on what a column holds, on what is sent or on whether
a verifier accepts.

Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
-- import E2E.OfflineAtParts   -- the lot's own line; LotPlanServes reads nothing of it (TiedOffline is LotOkStart's alone)
import E2E.KeyStandWalked
import E2E.LotPlanServesValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.HonestTerm.Lots
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyStandWalked (offlineValue)
open ProofFile.Honest
open VerifierAndGoals (PublicFiles InScope)

/-- **The plan.** -/
def LotPlanServes : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription} {B : ProverCoinCounts}, offlineDescription Z = .ok description →
    InScope Z = true → ∀ (w₀ : AtPublicFiles.AtFiles.FullSizeMatrix) (rc : (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst)
      (c : Coins B) R,
      ready (keyFileDescription description.source description.numbers description.later) B
        (keyProver (offlineValue (files := Z) description)) w₀ rc x c = .ok R →
      PlanServes (keyProver (offlineValue (files := Z) description)) w₀ rc R

/-- **The plan: it holds.** -/
theorem lotPlanServes : LotPlanServes := by
  unfold LotPlanServes
  intro Z description B hD scope w₀ rc x c R hR
  have h5 := AtPublicFiles.LotPlanGround.made5_of hD
  obtain ⟨r1, r2, r3⟩ := AtPublicFiles.LotPlanGround.rows scope h5
  have hk := AtPublicFiles.LotPlanGround.sized scope h5
  have hW : (OnBytes.linMessageW (AtPublicFiles.KeyValues.oneOf description.source).lin).isSome = true := by
    show (OnBytes.linMessageW description.source.Y.k.oneTime.lin).isSome = true
    rw [AtPublicFiles.LotPlanGround.lin scope h5]
    exact AtPublicFiles.LotPlanGround.w_written
  have hsp : (ProofFile.Honest.K14.planData (AtPublicFiles.KeySharedThread.parKey description.source
            description.later)).S.sharedSplitNeeded = true := by
    show description.source.chains.made.sized.key.once.shape.sharedSplitNeeded = true
    rw [hk]
    exact AtPublicFiles.LotPlanGround.split_written
  exact planServes hR (AtPublicFiles.LotPlanGround.plan scope h5)
    (AtPublicFiles.LotPlanGround.rootedAll_of_rows r1 r2 r3 _
      (AtPublicFiles.LotPlanGround.atAll_offline description hW hsp))
    (AtPublicFiles.LotPlanGround.widths_of (AtPublicFiles.LotPlanGround.decl scope h5) w₀ rc fun y hy =>
      AtPublicFiles.LotPlanGround.stored_offline description hk w₀ rc y hy)

end AtPublicFiles.AtFiles.HonestTerm.Lots

#print axioms AtPublicFiles.AtFiles.HonestTerm.Lots.lotPlanServes
