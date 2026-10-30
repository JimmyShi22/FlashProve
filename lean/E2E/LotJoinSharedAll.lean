-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinSharedAll.lean: THE SHARED CHAIN WHOLE AT THE THREAD OF RECORD: at `valueThread`, `valueSaid` (E2E/LotJoinSharedAtValue.lean), at every tied input and every
fall: OwesS, SaidNext at every border, YesS: `shared_at_tied` (E2E/OfflineSharedAtTied.lean) with its four premises on the two proximity tests met by
`ten_at_value` and its laws on letters met as E2E/OfflineJoinLaws.lean meets them. A call.

  **`sharedAll_at_value`**.

Premises: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀. tk, rest, Z₀ stay letters.
Limits. Those of E2E/LotJoinSharedAtLots.lean: the content at 9 and 10 is ULaid.lean's trial, elsewhere the called files'; ThrS inside every sentence:
no stand is shown. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinSharedAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12.AtKey (keepsKey keepsKey_same keepsKey_zero keepsKey_eleven)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleNm_tenant)
open AtPublicFiles.KeyStandWalked.Lots (ttValue)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) joinSharedAllPad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) joinSharedAllRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) joinSharedAllRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub)

/-- **The shared chain whole, at the thread of record.** -/
theorem sharedAll_at_value (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z d w x) (fall : ℕ → St → List Fmt.Drawn → Option String) :
    OwesS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) ∧
      (∀ b, SaidNext (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) b) ∧
      YesS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) fall := by
  obtain ⟨o₉, o₁₀, y₉, y₁₀⟩ := ten_at_value tk rest Z₀ hd scope live hK₀ w x ht fall
  exact shared_at_tied hd scope live hK₀ AtPublicFiles.AtFiles.inRange WitLens.words idleNm (fun _ => idleMg) tk
    (ttValue Z d K₀) rest keepsKey (fun _ => True) Z₀ w x ht idleNm_tenant keepsKey_same
    (fun s s' h => (keepsKey_zero s s').1 h) (fun s s' h => (keepsKey_eleven s s').1 h)
    (fun _ => idle_cells) fall o₉ o₁₀ y₉ y₁₀

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.sharedAll_at_value
