-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFiveAtRanges.lean: THE FIVE STATEMENTS AT MEMBER 15, the key file's test on the ranges, AT THE REAL VALUE: at the first
chain's thread Th (E2E/FirstHSeat.lean) at the offline prover's own senders (offlineValue, E2E/KeyStandWalked.lean) and the
index's reader matrixReader, at every Q whose letter kind₁ at 15 is the test's own yes (RngYes). A call of IOP's
five_at_fill (Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesAtFillH.lean), with each of its premises on letters paid.

  rng_atValue     the senders' field rng is the test's half at the job rangesTestJob: by unfolding
  LotFiveAtRanges, fiveAtRanges   PlaysS, BehindS, ExchangeS, RidesPastS and AcceptedS at 15, at every letter Said and every fall

What is paid. hp : FirstPublic, by firstPublic_atValue (E2E/LotFirstPublicAtValue.lean) · hrng, by rfl · hq₁, hq₂ (kind₁ at 15
lies between RngYes and RngKept), by the premise on Q and IOP's rng_keeps.
What is left. KeySourced, InScope, fullPub = some K₀, and Q.kind₁ 15 = RngYes d.source d.numbers (rfl at kindFirst,
E2E/LotKindFirst.lean).

Limits. All five have the pair ThrS in front as a premise: no stand at 15 is shown. AT EVERY FALL, so also at the fall that
never speaks: AcceptedS then says that the test accepts at every list of challenges that fits, where the pair stands and the
play returns. In scope, at the written sizes. Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesAtFillH
import E2E.LotFirstPublicAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState)
open AtPublicFiles.KeyFile (In1)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.K12.AtKey (Five RngYes rng_keeps five_at_fill)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- The senders' field rng is the test's half at the job. -/
theorem rng_atValue {files : PublicFiles} (d : OfflineDescription) :
    (offlineValue (files := files) d).rng =
      proverSideOfProximityTest (rangesTestJob (X' := Unit) d.source d.numbers d.later
                         (matrixEntryOf (Rc := (protocolAtFiles files).EncodingRandomness) matrixReader) (multiplicitiesGroups d.source) 0) := rfl

/-- **The five at member 15, at the real value.** -/
def LotFiveAtRanges : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    Q.kind₁ 15 = RngYes d.source d.numbers →
    ∀ (Said : Nat → Coins (keyBook K₀) → Mid (In1 FullSizeMatrix (protocolAtFiles files).EncodingRandomness) Unit → Prop)
      (fall : Nat → FirstState → List Fmt.Drawn → Option String),
      Five (Th d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x)
        Said fall 15

theorem fiveAtRanges : LotFiveAtRanges := fun d _ _ _ _ hs scope hK hQ Said fall =>
  five_at_fill hs scope hK (firstPublic_atValue hs scope) (rng_atValue d)
    (fun _ _ h => hQ ▸ h) (fun _ _ h => rng_keeps hs (hQ ▸ h)) Said fall

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.rng_atValue
#print axioms AtPublicFiles.FirstH.Lots.fiveAtRanges
