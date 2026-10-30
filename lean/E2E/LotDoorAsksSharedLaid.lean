-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotDoorAsksSharedLaid.lean: WHAT THE LAST CHAIN's DOOR ASKS OF THE SHARED CHAIN (AtPublicFiles.KeyLastChain.DoorAsks, E2E/KeyLastTerm.lean: one run, one state, the field, the letter's next), AT ITS LAST
BORDER 12, AT THE THREAD AND LETTER OF RECORD, WITH NO PREMISE LEFT ON ANY MEMBER.

  LotDoorAsksSharedLaid, lotDoorAsksSharedLaid   DoorAsks (valueThread tk rest Z₀ w x) (valueSaid tk rest Z₀ w x) 12, AT EVERY TIED INPUT, from: the offline description is returned, in scope,
                         protocolDataWellFormed, fullPub = some K₀

BY WHAT. doorAsksShared_of_owes (E2E/LotFieldShared.lean) with OwesS by sharedAll_at_value (E2E/LotJoinSharedAll.lean), OpensShared at ttValue by lotOpensSharedAtValue
(E2E/LotSharedAtValue.lean), NoStop at the value.

What it does not say. NO STAND of the thread at 12 is shown here: where there is none, state and field are empty. IT STANDS ON IOP's TRIAL, ON NO ROW (E2E/KeyOpensAll.lean and nineteen files
beneath, through E2E/LotOpensShared.lean), and on whatever sharedAll_at_value stands on. tk, rest, Z₀ stay letters. Nothing on acceptance. Nothing on soundness, completeness, hiding or binding.
No law over coins.
-/
import E2E.LotDoorAsksOwn
import E2E.LotJoinSharedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.KeyStandWalked.Lots
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription sourced_of_ok valueThread valueSaid sharedAll_at_value
  TiedAt)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValueHolds (noStop_value)
open AtPublicFiles.LotField (doorAsks_own)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub)

variable (Z d K₀) in
/-- **What the door asks of the shared chain, laid: no premise on a member.** -/
def LotDoorAsksSharedLaid : Prop :=
  offlineDescription Z = .ok d → InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi), TiedAt Z d w x →
      AtPublicFiles.KeyLastChain.DoorAsks (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 12

theorem lotDoorAsksSharedLaid : LotDoorAsksSharedLaid Z d K₀ tk rest Z₀ := by
  intro hd scope live hK w x ht
  have hs := sourced_of_ok live hd
  have hlen : (valueThread (d := d) tk rest Z₀ w x).bs.length = 12 := by
    rw [(AtPublicFiles.KeySharedQuiet.over_key _ _ _ _ _ _ _ _ _ _ _ _).bs]
    exact (AtPublicFiles.KeyThread.lengths scope hs.named).2.1
  exact doorAsks_own (doorAsksShared_of_owes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs.named.plan
    (lotOpensSharedAtValue _ _ _ tk rest _ _ Z₀ w.1 w.2.1 x hs scope hK)
    (noStop_value _ _ _ _ _ _ _ _ _ _ _ _ _).2.1 hlen
    (sharedAll_at_value tk rest Z₀ hd scope live hK w x ht fun _ _ _ => none).1)

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.lotDoorAsksSharedLaid
