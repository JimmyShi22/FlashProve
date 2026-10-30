-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OwnSayAtValue.lean: THE OWN TEST'S ROWS AT THE VALUE: the field own of FourSayAtStands (E2E/OfflineSayAtStand.lean), at U₃ := lastThread, S₃ := lastSaid
(E2E/OfflineLastTerms.lean): own_says_at_stand at the tie of the last thread (tie_at_last_thread_at_offline_senders).

What stays a premise: KeySourced, scope, fullPub = some K₀, hfit, and the offline description's letters. No stand is shown to exist here.
The statement speaks of words that depend on the pads.
This file says nothing on completeness, soundness or hiding.
Limit: NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The premises of this theorem read two kinds of coins: k (a run's coins) and, through the input, rc (the committer's randomness).
The stand ThrS reads k and the input, and under it stand the thread's invariants and what is said. The lending reads k and ties c.
The tie beneath reads k through the witness and through c. So this theorem may not be used as a step toward a statement about distributions over these coins.
-/
import E2E.OwnSayAtStand
import E2E.OfflineSayAtStand
import E2E.OfflineLastTerms
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnJoinAtOfflineSenders

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany)
open ProofFile.Honest.K14 (WitLens)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyLastChain (own_says_at_stand place_own)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.FirstH (LaterFill)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (d : OfflineDescription) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi)

/-- The own test stands at its written place. -/
theorem own_job_place (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    (ownJobAtFiles (Z := Z) d).toRun.toTest.p.place = ownTestPlace := by
  show (AtPublicFiles.KeyLay.pWK d.later).place = _
  rw [place_own hs scope]
  rfl

/-- **The own test's rows at the value.** -/
theorem own_sayAtStand (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey d.source d.numbers d.later (keyAtValue (Z := Z) Z₀ d) ℓ Nm Mg₀
      (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd
      (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x)).valid v → keyFits v.key QK.par.S.fold.index = true) :
    SayAtStand (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) (ownJobAtFiles (Z := Z) d).toRun.toTest
      (plainMany (ownJobAtFiles (Z := Z) d)) 2 ownTestPlace
      (ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)
        (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2) := by
  intro k st m₀ E₀ c hT hc
  rw [← own_job_place d hs scope] at hc
  exact own_says_at_stand K₀ d.source d.numbers d.later _ _ ℓ Nm Mg₀ _ rest Kp Vd _ w.1 w.2.1 x _ _ _ _ _ _ 6 11
    (fun _ => True) _ _ _ _ _ _ _ _ hs scope hfit (d_lin d x) (same_value d Q x)
    (ProofFile.Honest.K12.AtKey.plan_message_of_index_masks d.source)
    (ProofFile.Honest.K12.AtKey.plan_message_of_vector_w hs scope)
    (ProofFile.Honest.K12.AtKey.tie_at_last_thread_at_offline_senders d _ Q ℓ Nm Mg₀ _ rest Kp Vd _ w.1 w.2.1 x _ _ _ _ _ _
      6 11 (fun _ => True) _ _ _ hs scope hK₀ hfit (d_lin d x) rfl _) k st m₀ E₀ c hT hc

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.own_job_place
#print axioms AtPublicFiles.OfflineRows.own_sayAtStand
