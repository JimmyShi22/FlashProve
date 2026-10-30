-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineLastTie.lean: THE FIELD `tie` OF `LastLeft` (E2E/OfflineLastFields.lean), in that field's own text: the premise htie of
`last_laid` (E2E/KeyLastLaid.lean) at the last chain's thread and letter as terms (`lastThread`, `lastSaid`,
E2E/OfflineLastTerms.lean): at every stand at the border 2, at the coins that the book lends the test's two parts, the thread's
words on the members' tables are the job's plain rows.

  `last_tie`   **the field**, from the field `fit`

A PLUG: one call of `tie_at_last_thread_at_offline_senders`
(Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnJoinAtOfflineSenders.lean). That law is stated at the parts
`withTests (offlineSenders d) …`; `lastThread` has `keyOf (pubKey Z₀ …) … (offlineValue d) …` in their place: Lean takes the two for one by
unfolding.

Limits. Those of that law. WORDS ARE TIED TO WORDS: nothing says that the rows taken in hold at them, and no stand is shown
reached. NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import E2E.OfflineLastFields
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnJoinAtOfflineSenders

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (plainMany askOf)
open OnBytes (TableKey)
open OnBytes.Means (tableSize layoutOf)
open OnBytes.Slice (begun frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (randK14 keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyLay (jobKWAt)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key)
open AtPublicFiles.FirstH (LaterFill tbH)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope)

local instance (priority := high) lastTiePads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lastTieRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lastTieRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (d : OfflineDescription) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **At every stand at the border 2 the thread's words are the job's plain rows.** -/
theorem last_tie (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (fit : ∀ w x, TiedAt Z d w x → ∀ v,
      (threadKey d.source d.numbers d.later (keyAtValue (Z := Z) Z₀ d) ℓ Nm Mg₀
        (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd
        (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x)).valid v → keyFits v.key QK.par.S.fold.index = true) :
    ∀ w x, TiedAt Z d w x → ∀ k st m E
      (c : RowCoins [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest]),
    ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)
      (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
    lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (lastJobAt (Z := Z) d).toRun.toTest.p.place
      [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest] 0 = .ok c →
    ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt,
      ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key d.source (fillAtValue d Q x)) st
            ((lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).wit k m.st.input
              (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany (lastJobAt (Z := Z) d) m.st.input (frontOf m) (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1)) o pt i :=
  fun w x ht =>
    ProofFile.Honest.K12.AtKey.tie_at_last_thread_at_offline_senders (Z := Z) (files := Z) d matrixReader Q ℓ Nm
      Mg₀ (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd
      (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x) w.1 w.2.1 x (keyProver (keyAtValue (Z := Z) Z₀ d)).first
      (tbH d.source d.numbers d.later (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) matrixReader Q) (S₁ w x)
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (dValue d x) (dtValue d Q x) 6 11
      (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x) hs scope hK₀ (fit w x ht) (d_lin d x)
      rfl (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.last_tie
