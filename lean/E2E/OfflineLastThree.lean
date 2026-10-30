-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastThree.lean: THE THREE FIELDS `lastOwes`, `lastNext`, `lastYes` OF `TheLots` (E2E/OfflineJoin.lean), to the letter, at the last chain's
thread and letter as terms (`lastThread`, `lastSaid`, E2E/OfflineLastTerms.lean): WITH NO PREMISE ON ANY THREAD.

  `lastTie_at_value`      `LastTie` (E2E/OfflineLastAtValue.lean), by `last_tie` (E2E/OfflineLastTie.lean) at `fit_at_tied` (E2E/OfflineLastFit.lean)
  `lastLeft_at_value`     `LastLeft` (E2E/OfflineLastFields.lean) whole
  `last_three_at_value`   **the three fields**

Premises: the public files are live and in scope; d is their description; `KeySourced`; the written book is made. All the
join's letters ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀, the filling's letter Q and the first chain's letter S₁ are free. Calls alone.

WHAT THE THREE FIELDS SAY AND DO NOT SAY. `OwesS`, `SaidNext` and `YesS` (Johnson/Desc/ProofFile/Honest/Thread/) speak of EVERY STAND of the last thread
with its letter: from a stand at a border the sub-protocol plays, the next border's sentence holds, and the step accepts. That
the thread stands at its first border is not said here: WHERE IT STANDS NOWHERE THE THREE ARE TRUE AND EMPTY. Its start looks for a pair
of stands of the two earlier threads at their borders 19 and 12 (`last_start_at_the_lots`, E2E/OfflineLastReadsTheLots.lean). That such a
pair stands, and that the door leads from it to the last thread's first border (`DoorBehindS`, in the field `run` of `TheLots`),
carries the weight, and is not shown here.

Limits. Those of the laws that are called. `last_tie` ties words to words at every stand and reads the input and the coins: NOT IN
FRONT OF A LAW OVER COINS: no later law may take these sentences as hypotheses on a run and then speak of the coins as sampled anew.
`holdField` and `last_wide` say which trees are at hand and how wide they are: nothing on what a table holds. Nothing on any property.
-/
import E2E.OfflineLastAtValue
import E2E.OfflineLastTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) lastThreePads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lastThreeRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lastThreeRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

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

/-- **The tie, at the offline prover's own senders.** -/
theorem lastTie_at_value (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) : LastTie ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ :=
  last_tie ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ hs scope hK₀ fun w x ht v hv =>
    fit_at_tied d (keyAtValue (Z := Z) Z₀ d) ℓ Nm Mg₀
      (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd w x ht v hv

/-- **`LastLeft` whole.** -/
theorem lastLeft_at_value (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) : LastLeft ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ :=
  lastLeft_of_tie live hd hs scope hK₀ (lastTie_at_value ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ hs scope hK₀)

/-- **THE THREE FIELDS OF `TheLots` AT THE LAST CHAIN.** -/
theorem last_three_at_value (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) :
    (∀ w x, TiedAt Z d w x → OwesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)) ∧
      (∀ w x, TiedAt Z d w x → ∀ b, SaidNext (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) b) ∧
      ∀ w x, TiedAt Z d w x →
        YesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (fallsBy [] (descOf d).second.blocksInOrder) :=
  last_fields_of_tie live hd hs scope hK₀ (lastTie_at_value ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ hs scope hK₀)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.lastTie_at_value
#print axioms AtPublicFiles.OfflineRows.lastLeft_at_value
#print axioms AtPublicFiles.OfflineRows.last_three_at_value
