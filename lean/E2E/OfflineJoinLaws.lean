-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineJoinLaws.lean: the last line of the join at the values of its letters: the laws on the letters are paid.

Why. `keyAccepts_of_lots` (E2E/OfflineJoin.lean) asks five laws in its premises. At the values that the shared thread is meant
to take they hold, each by its own line here. `hPin` and `Vd` at the input, which `run` spends, are stated too.

Main names.
  `idle_cells`: `CellsAlone` at `idleMg`. `idle_pin`: its stored table's pin holds everywhere.
  `keyOf_value`: `keyOf` of the offline value is that value: a `rfl` that the seam at the shared thread rests on.
  `offlineDebts_at_value`, `keyAccepts_at_value`: the join's two ends with no premise but the files' and `TheLots`.

What stays open. Every field of `TheLots`; and of `Kp` what it says at 9 and at 10, inside `testU`, `testOmega`. The last thread `U₃` carries the shared thread's letters inside it: the file that lays `U₃` passes these same values.

No law over coins. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.OfflineJoin
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeeps

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place Strs)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Common Coins Table)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.AtKey (keepsKey keepsKey_same keepsKey_zero keepsKey_eleven)
open AtPublicFiles.Bridge (KeyAccepts)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleNm_tenant)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open ProofFile.Honest.Term (tableCoins)
open AtPublicFiles.KeyStandWalked (offlineValue)

local instance (priority := high) instNonemptyPadZOfflineJoinLaws : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineJoinLaws : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineJoinLaws : Inhabited RunValue := ⟨fun _ => 0⟩

/-- The idle meaning's stored table's pin reads nothing. -/
theorem idle_cells : AtPublicFiles.KeySharedQuiet.CellsAlone idleMg := fun _ _ _ _ _ _ => trivial

/-- It holds everywhere. -/
theorem idle_pin (s : St) (y : Strs) (u : Words Cb.Gl.E) : idleMg.pinT s y u := trivial

/-- **The prover at the shared thread is the offline value.** -/
theorem keyOf_value (Z : PublicFiles) (description : OfflineDescription) (Z₀ : ProofFile.Pub) :
    AtPublicFiles.KeyStandMember.keyOf (AtPublicFiles.KeyFiveFields.pubKey Z₀ description.source.chains) description.source
        description.later (offlineValue (files := Z) description) matrixReader (tableCoins Z) =
      offlineValue (files := Z) description :=
  rfl

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}
  {K₀ : KeyPub}
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub)

/-- **The clause, at the values of the letters.** -/
theorem offlineDebts_at_value {U₁ : FirstFamily Z description (keyBook K₀)}
    {U₃ : LastFamily Z description (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (L : TheLots (Z := Z) WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀
      description U₁ U₃ S₁ S₃) :
    ∃ Tied TiedM, OfflineDebts Z (descOf description) (thePartsAt Z).book
      ((thePartsAt Z).prover description) runValueBytes runValueBytes
      (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_of_lots hr WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀ hd
    scope live hK₀ idleNm_tenant keepsKey_same (fun s s' h => (keepsKey_zero s s').1 h)
    (fun s s' h => (keepsKey_eleven s s').1 h) (fun _ => idle_cells) L

/-- **The last line, at the values of the letters.** -/
theorem keyAccepts_at_value {U₁ : FirstFamily Z description (keyBook K₀)}
    {U₃ : LastFamily Z description (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (L : TheLots (Z := Z) WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀
      description U₁ U₃ S₁ S₃) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf description) (thePartsAt Z).book
        ((thePartsAt Z).prover description) runValueBytes runValueBytes (offlineStart description))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_of_lots hr WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀ hd
    scope live hK₀ idleNm_tenant keepsKey_same (fun s s' h => (keepsKey_zero s s').1 h)
    (fun s s' h => (keepsKey_eleven s s').1 h) (fun _ => idle_cells) L

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.idle_cells
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyOf_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDebts_at_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyAccepts_at_value
