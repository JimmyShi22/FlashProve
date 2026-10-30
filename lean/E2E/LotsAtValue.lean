-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotsAtValue.lean: three lots on the key file's first chain's thread T₁ (E2E/FirstHFill.lean) AT THE REAL
VALUE: at the offline prover's own senders (offlineValue, E2E/KeyStandWalked.lean) and the index's reader
matrixReader (E2E/KeyArgumentsAt.lean). Each lot takes FirstPublic as a premise; at the real value that premise is
met (firstPublic_atValue, E2E/LotFirstPublicAtValue.lean), so what is left is KeySourced, InScope and
fullPub = some K₀. Calls alone.

  ThValue         the thread at the value: the letters Q, w₀, rc, x stay
  LotOpensFirstAtValue, opensFirst_atValue   what the first chain opens
  LotMemberFourteenAtValue, memberFourteen_atValue   the five statements at member 14
  LotFitsAtValue, fitsAt_atValue   FitsAt at 4, 10, 14, 18

Limits. As the three lots' own heads. In scope, at the written sizes. No stand of T₁ is shown here: the five
statements at member 14 speak of every stand and are empty where there is none. Q stays a letter. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.LotOpensFirst
import E2E.LotMemberFourteen
import E2E.LotFirstPublicAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState)
open AtPublicFiles.KeyFile (In1)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- **The first chain's thread at the real value.** -/
noncomputable abbrev ThValue {files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi) :=
  Th d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x

/-- **What the first chain opens, at the real value.** -/
def LotOpensFirstAtValue : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    (∀ n, n < 20 → (ThValue d Q w₀ rc x).opensAvailable n = true) ∧
      (∀ n, n ≤ 19 → ∀ k m, DepthsAt (ThValue d Q w₀ rc x) n k m) ∧
      ∀ j, Fmt.TreeSource.own j ∉ (ThValue d Q w₀ rc x).taken

theorem opensFirst_atValue : LotOpensFirstAtValue := fun d Q w₀ rc x hs scope hK =>
  lot_opens_first _ d.source d.numbers d.later _ matrixReader Q w₀ rc x hs scope hK
    (firstPublic_atValue hs scope)

/-- **The five at member 14, at the real value.** -/
def LotMemberFourteenAtValue : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    ∀ (Said : Nat → Coins (keyBook K₀) → Mid (In1 FullSizeMatrix (protocolAtFiles files).EncodingRandomness) Unit → Prop)
      (fall : Nat → FirstState → List Fmt.Drawn → Option String),
      PlaysS (ThValue d Q w₀ rc x) Said 14 ∧ BehindS (ThValue d Q w₀ rc x) Said 14 ∧
        ExchangeS (ThValue d Q w₀ rc x) Said 14 ∧ RidesPastS (ThValue d Q w₀ rc x) Said 14 ∧
        AcceptedS (ThValue d Q w₀ rc x) Said fall 14

theorem memberFourteen_atValue : LotMemberFourteenAtValue := fun d Q w₀ rc x hs scope hK =>
  lotMemberFourteen _ d.source d.numbers d.later _ matrixReader Q w₀ rc x hs scope hK
    (firstPublic_atValue hs scope)

/-- **The fits, at the real value.** -/
def LotFitsAtValue : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    ∀ b ∈ [4, 10, 14, 18], FitsAt (ThValue d Q w₀ rc x) b

theorem fitsAt_atValue : LotFitsAtValue := fun d Q w₀ rc x hs scope hK =>
  lotFitsAt _ d.source d.numbers d.later _ matrixReader Q w₀ rc x hs scope hK
    (firstPublic_atValue hs scope)

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.opensFirst_atValue
#print axioms AtPublicFiles.FirstH.Lots.memberFourteen_atValue
#print axioms AtPublicFiles.FirstH.Lots.fitsAt_atValue
