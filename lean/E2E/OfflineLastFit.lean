-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastFit.lean: AT A TIED INPUT THE INSTANCE's KEY HAS THE WRITTEN SIZES (`keyFits` at the written plan's index shape), and so
has the key of every input that the shared chain's thread at that instance counts as valid. This is the premise hfit of
`last_laid` (E2E/KeyLastLaid.lean) at a tied input.

  `keyFits_of_tied`     at a tied input of the offline file, at any senders: the key is the one written of the committer's sample
  `fit_at_tied`         at every valid input of `threadKey` … (`inK w.1 w.2.1 x`), whatever its other letters

By `keyFits_written` (E2E/OfflineOwnKeyFits.lean) and the field `key` of `Tied`.

Limits. On the key's sizes alone: nothing on what the key holds. `valid` is laid as «the input is this one, and Vd»: of Vd
nothing is read. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnKeyFits
import E2E.OfflineFromChains
import E2E.KeyStandOne

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
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.AtFiles (FullSizeMatrix Cz protocolAtFiles TiedOffline)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (AZ PadZ holdZ keyAt recAt pads_nonempty)
open VerifierAndGoals (PublicFiles)

local instance (priority := high) lastFitPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lastFitRunNonempty : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lastFitRunInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

/-- **The key of a tied input has the written sizes.** -/
theorem keyFits_of_tied {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {Q₂ Q₃ X₀ Xh Wk : Type}
    [Nonempty Q₂] [Inhabited Q₃] {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray}
    {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk} {ok : FullSizeMatrix → Prop}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : AtPublicFiles.AtFiles.KeyInst}
    (ht : TiedOffline Z X N P val₂ val₃ K ok w x) : keyFits x.key QK.par.S.fold.index = true := by
  have key := ht.key (Classical.arbitrary Q₂) default
  have e' : keyAt (recAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 w.2.2) = x.key := key
  rw [← e']
  exact keyFits_written _

/-- **So has the key of every valid input of the shared chain's thread at that instance.** -/
theorem fit_at_tied {Bk : ProverCoinCounts} {X₀ Xh Wk P₁ Wt : Type} (d : OfflineDescription)
    (K : KeyParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness X₀ Xh Wk) (ℓ : WitLens Wt) (Nm : NumbersS)
    (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
    (tb : Fmt.TreeSource → Coins Bk → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
    (rest : Coins Bk → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
    (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (ht : TiedAt Z d w x)
    (v : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey)
    (hv : (threadKey d.source d.numbers d.later K ℓ Nm Mg₀ tb rest Kp Vd
      (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x)).valid v) : keyFits v.key QK.par.S.fold.index = true := by
  obtain ⟨e, -⟩ : v = AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x ∧ Vd v := hv
  rw [e]
  exact keyFits_of_tied ht

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.keyFits_of_tied
#print axioms AtPublicFiles.OfflineRows.fit_at_tied
