-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastAtValue.lean: THE THREE FIELDS `lastOwes`, `lastNext`, `lastYes` OF `TheLots` (E2E/OfflineJoin.lean) at `lastThread`, `lastSaid`
(E2E/OfflineLastTerms.lean), with four of the five premises of `LastLeft` (E2E/OfflineLastFields.lean) paid: what stays is the tie.

  `LastTie`             THE ONE PREMISE THAT STAYS, under a name: the field `tie` of `LastLeft`: at every tied input and every stand of
                        the last thread at the border 2 where the book lends the test's two parts their coins, the thread's
                        words are the job's plain rows
  `lastLeft_of_tie`     `LastLeft` from it: fit by `fit_at_tied` (E2E/OfflineLastFit.lean) · the three public equations by
                        `own_sendings_at_senders` (E2E/OfflineOwnSendingsAtSenders.lean) · hold by `holdField` (E2E/LotHoldField.lean) ·
                        wide by `last_wide` (E2E/OfflineLastWide.lean)
  `last_fields_of_tie`  the three fields from it

All the join's letters, Q and S₁ are free. Calls alone.

Limits. CONDITIONAL on `LastTie`: no member is shown here. `OwesS` and `YesS` speak of every stand of the thread: that the thread
stands at any border is not said here. Nothing on any property.
-/
import E2E.OfflineLastFields
import E2E.OfflineLastFit
import E2E.OfflineOwnSendingsAtSenders
import E2E.LotHoldField
import E2E.OfflineLastWide

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (plainMany)
open OnBytes (TableKey)
open OnBytes.Means (tableSize layoutOf)
open OnBytes.Slice (begun frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) lastAtValuePads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lastAtValueRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lastAtValueRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (d : OfflineDescription) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **THE ONE PREMISE THAT STAYS**: the field `tie` of `LastLeft`. -/
def LastTie : Prop :=
  ∀ w x, TiedAt Z d w x → ∀ k st m E
      (c : RowCoins [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest]),
    ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
    lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (lastJobAt (Z := Z) d).toRun.toTest.p.place
      [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest] 0 = .ok c →
    ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt,
      ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key d.source (fillAtValue d Q x)) st
            ((lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).wit k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany (lastJobAt (Z := Z) d) m.st.input (frontOf m)
              (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1)) o pt i

variable {ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁}

/-- **`LastLeft` from the tie.** -/
theorem lastLeft_of_tie (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) (tie : LastTie ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁) :
    LastLeft ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ where
  fit := fun w x ht v hv => fit_at_tied d (keyAtValue (Z := Z) Z₀ d) ℓ Nm Mg₀
    (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd w x ht v hv
  sentIndexMasks := (own_sendings_at_senders (files := Z) d hs scope).1
  sentW := (own_sendings_at_senders (files := Z) d hs scope).2.1
  shapeOmega := (own_sendings_at_senders (files := Z) d hs scope).2.2
  tie := tie
  hold := holdField ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ live hd scope hK₀
  wide := last_wide ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ hs scope hK₀

/-- **The three fields of `TheLots` at the last chain, from the tie.** -/
theorem last_fields_of_tie (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) (tie : LastTie ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁) :
    (∀ w x, TiedAt Z d w x → OwesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)) ∧
      (∀ w x, TiedAt Z d w x → ∀ b, SaidNext (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) b) ∧
      ∀ w x, TiedAt Z d w x →
        YesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (fallsBy [] (descOf d).second.blocksInOrder) :=
  last_fields hs scope hK₀ (lastLeft_of_tie live hd hs scope hK₀ tie)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.lastLeft_of_tie
#print axioms AtPublicFiles.OfflineRows.last_fields_of_tie
