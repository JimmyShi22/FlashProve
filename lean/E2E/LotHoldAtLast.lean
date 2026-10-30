-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A statement; proved in E2E/LotHoldAtLastProved.lean.
/-
E2E/LotHoldAtLast.lean: THE PREMISE hold OF last_done | last_laid (E2E/KeyLastDone.lean, E2E/KeyLastLaid.lean) AT THE LAST THREAD AT THE
VALUE (lastThread, lastSaid, E2E/OfflineLastTerms.lean): at a stand at border 2 of the last chain, where the book lends the own
test's two parts their coins, the three trees that the test reads stand among the tables at hand, at the sources taken 0 0,
taken 0 5, taken 1 1 (OldAt).

  ownJob          the own test's job at the offline prover's senders: the J of own_value (E2E/OfflineLastTerms.lean)
  LotHoldAtLast   THE STATEMENT: hold's text, letter for letter, at these terms

The road: tables_of_hand (E2E/OfflineTablesLaid.lean: from the thread's Hand at border 2 to TablesAreLaid) and lot_p3
(E2E/LotTreesSentBeforeOwnTestProved.lean: from TablesAreLaid to OldAt).
Limits. A definition: nothing is claimed. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineLastTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Lots
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest
open ProofFile.Honest.K12 (firstPart restPart restCoins OldAt frontOf)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLay (jobKWAt)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **The own test's job at the offline prover's senders.** -/
abbrev ownJob (Z : PublicFiles) (d : OfflineDescription) :=
  (jobKWAt d.source d.numbers d.later (offlineSenders (files := Z) d).idx
    (offlineSenders (files := Z) d).w (offlineSenders (files := Z) d).send id
    (ProofFile.Honest.K12.Light.askOf (offlineSenders (files := Z) d).send
      (fun w => (offlineSenders (files := Z) d).weights w.w₀)
      (fun w => AtPublicFiles.KeyFile.randK14 ((offlineSenders (files := Z) d).rand w.rc)))).toRun.toTest

/-- **hold at the last thread at the value.** -/
def LotHoldAtLast : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {P₁ Wt : Type}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    ∀ (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
      (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
        Place × Table)
      (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
      (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
      (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
      (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
      (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
        Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
      (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) k st m E
      (c : RowCoins [(firstPart (ownJob Z d) :
        Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit), restPart (ownJob Z d)]),
      ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)
        (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (ownJob Z d).p.place
        [(firstPart (ownJob Z d) :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit), restPart (ownJob Z d)]
        0 = .ok c →
      OldAt E ((ownJob Z d).trees₀ m.st.input (frontOf m) (restCoins (ownJob Z d) c.2.1).mem
        ((ownJob Z d).first m.st.input (frontOf m) (restCoins (ownJob Z d) c.2.1)))
        (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0))

end AtPublicFiles.AtFiles.HonestTerm.Lots

#print axioms AtPublicFiles.AtFiles.HonestTerm.Lots.LotHoldAtLast
