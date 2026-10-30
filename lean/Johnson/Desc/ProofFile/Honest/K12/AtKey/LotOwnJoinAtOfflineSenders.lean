-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnJoinAtOfflineSenders.lean: THE TIE OF THE WORDS AT THE LAST THREAD (LotOwnJoinAtValue.lean) AT THE VERY PARTS THAT
THE OFFLINE PROVER IS HANDED: `AtPublicFiles.KeyLay.withTests (offlineSenders description) …` at `offlineTestParametersOnU`, `offlineTestOnOmega`,
`matrixEntryOf matrixReader`, `multiplicitiesGroups`, 0 (E2E/KeyArgumentsAt.lean's `prover_is_keyOf` names that term).

  `tie_at_last_thread_at_offline_senders`   THE TIE, behind `ThrS` at any letter and the lending

THE PREMISES, BY NAME: hs, scope, hK₀ · hfit, hd (`third_shaped`'s) · hw: the thread's input is the filling's instance.

Limits. LotOwnJoinAtValue.lean's, all of them: an instance of it. The filling's f, Q and the threads' other letters are free. That
`offlineDescription files` returns this description, and that `KeySourced` holds of it, are the caller's. NOT IN FRONT OF A LAW OVER
COINS. No stand is shown reached. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnJoinAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open OnBytes.Means (Words tableSize layoutOf)
open OnBytes.Slice (begun)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.AtFiles.HonestTerm (offlineSenders OfflineDescription offlineTestParametersOnU offlineTestOnOmega
  matrixReader)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key mlKey threadOwn)
open AtPublicFiles.FirstH (fillH LaterFill HCells HTab)
open ProofFile.Honest.Term (matrixInput tableCoins)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (plainMany)

variable {P₂ Wt₂ : Type} {K₀ : KeyPub} {Z files : VerifierAndGoals.PublicFiles} (description : OfflineDescription)
  (f : FullSizeMatrix → Weights) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : ℕ → St → St → Prop) (Vd₂ : Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey → Prop)
  (w₂ : Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi)
  (hs₁ : List (Placed (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : ℕ → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit → Prop)
  (Said₂ : ℕ → Coins (keyBook K₀) → Mid (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit → MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E))
  (n₁ n₂ : ℕ) (Vd : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit → Prop) (w : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit)

local notation "KT" => AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description)
  description.source description.numbers description.later (offlineTestParametersOnU description.later)
  (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0

local notation "LH" => fillH description.source description.numbers description.later
  (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0) f Q x

local notation "TO" => threadOwn description.source description.numbers description.later
  (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0)
  (fillH description.source description.numbers description.later
  (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0) f Q x)
  ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt
  (mlKey (val₁Key description.source (fillH description.source description.numbers description.later
  (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0) f Q x))) n₁ n₂ Vd w dfltT dfltM

local notation "AG" => jobAtKeyOwnTest
  (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0) description.source description.numbers description.later

/-- **THE TIE AT THE LAST THREAD, AT THE PARTS THAT THE OFFLINE PROVER IS HANDED.** The premises by name: this file's head.
NOT IN FRONT OF A LAW OVER COINS: LotOwnJoinTie.lean's head. -/
theorem tie_at_last_thread_at_offline_senders
    (hs : KeySourced Z description.source description.numbers description.later)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey description.source description.numbers description.later KT ℓ₂ Nm Mg₂ tb₂
      rest₂ Kp₂ Vd₂ w₂).valid v → keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hw : w = ⟨w₀, rc, x, ()⟩)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit → Prop) :
    ∀ k st m E (c : RowCoins [(firstPart (AG).toRun.toTest :
        Part (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit),
        restPart (AG).toRun.toTest]),
      ThrS TO Said 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (AG).toRun.toTest.p.place
        [(firstPart (AG).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit),
          restPart (AG).toRun.toTest] 0 = .ok c →
      ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key description.source LH) st
            (Thread.wit TO k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany AG m.st.input (frontOf m) (restCoins (AG).toRun.toTest c.2.1)) o pt i :=
  tie_at_last_thread_at_value _ matrixReader matrixInput.inRange matrixInput.dummy matrixReader
    (tableCoins files) description.source description.numbers description.later
    (offlineTestParametersOnU description.later) (offlineTestOnOmega description.later) (matrixEntryOf matrixReader)
    (multiplicitiesGroups description.source) 0 f Q ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁
    n₂ Vd w dfltT dfltM hs scope hK₀ hfit hd hw Said

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.tie_at_last_thread_at_offline_senders
