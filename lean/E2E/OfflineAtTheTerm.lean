-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineAtTheTerm.lean: a value of `OfflineDebts` at the honest provers' own offline prover (`thePartsAt`) and the
served requests, from the debts at the pairs of the three chains. It is what `theProver_of_lists`
(E2E/CompleteAsIOPOffline.lean) asks of the offline prover.

Main names. `offlineDebts_at_term`, at given lists of falls. `offlineDebts_no_fall_at_term`, at none, the fall named.

What it pays. The prover's key and columns (`stored_at_description`), that no part stops, that a half stands at every
sub-protocol (`offlineSides_whole`), that the relation lies in range (`servedRequest_below`).

What stays open. As premises: `hM`, `hat`: the members' debts at the threads, and `hZero`, `hFalls` on the three lists
of falls. Their letters `U₁ U₂ U₃ S₁ S₂ S₃` are the payers'.

No law over coins is stated here. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.OfflineDebtsAtParts
import E2E.KeyOfflineSides
import E2E.KeyStoredAtValue
import E2E.KeyStandWalked
import E2E.CompleteAsIOPServedLaws

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open ProofFile.Honest (Fall Thread Local Common Coins Mid)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.KeyValueHolds (quietHalf_test quietHalf_needs)
open LPFD.Full (XF)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineAtTheTerm : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineAtTheTerm : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineAtTheTerm : Inhabited RunValue := ⟨fun _ => 0⟩

/-- A matrix in range passes the test that `ready` reads. -/
theorem matrixInRange_of {M : AtPublicFiles.AtFiles.FullSizeMatrix} (h : AtPublicFiles.AtFiles.inRange M) :
    ProofFile.Honest.Term.matrixInput.inRange M = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf M).isSome = true
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf
  rw [dif_pos h]
  rfl

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}

/-- **The value of `OfflineDebts` at the honest provers' offline prover, from the debts at the pairs.** -/
theorem offlineDebts_at_term {B : ProofFile.Honest.ProverCoinCounts} (hB : offlineProverCoinCounts = B)
    (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (f₁ : List (Fall (keyFileDescription description.source description.numbers description.later).S₁))
    (f₂ : List (Fall (keyFileDescription description.source description.numbers description.later).S₂))
    (f₃ : List (Fall (keyFileDescription description.source description.numbers description.later).S₃))
    {pF : ℝ≥0∞}
    (hZero : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z (keyFileDescription description.source description.numbers
                                           description.later) B
                  (keyProver (offlineValue (files := Z) description)) runValueBytes runValueBytes
                  (keyFirst description.source description.numbers description.later))
      (lettersZ Z allZeroDigest []).W
      (fallLists Z (val₂ := runValueBytes) (val₃ := runValueBytes)
        (offlineValue (files := Z) description) f₁ f₂ f₃))
    (hFalls : AtPublicFiles.KeyBridge.FallSmall (offlineProverWithEncodedTable Z (keyFileDescription description.source description.numbers
                                           description.later) B
                  (keyProver (offlineValue (files := Z) description)) runValueBytes runValueBytes
                  (keyFirst description.source description.numbers description.later))
      (fallLists Z (val₂ := runValueBytes) (val₃ := runValueBytes)
        (offlineValue (files := Z) description) f₁ f₂ f₃)
      (fun w a => TiedOffline Z description.source description.numbers description.later
        runValueBytes runValueBytes (offlineValue (files := Z) description) inRange w
        (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample a)) pF)
    {U₁ : FirstFamily Z description B} {U₂ : SharedFamily Z description B} {U₃ : LastFamily Z description B}
    {S₁ : OwnLetter Z B} {S₂ : SharedLetter Z B} {S₃ : OwnLetter Z B}
    (hM : ∀ w x, TiedOffline Z description.source description.numbers description.later
        runValueBytes runValueBytes (offlineValue (files := Z) description) inRange w x →
      (keyFileDescription description.source description.numbers description.later).okStart x = true →
      MembersS (keyFileDescription description.source description.numbers description.later)
        (bareSides (keyFileDescription description.source description.numbers description.later)
          B
          (keyProver (offlineValue (files := Z) description)) f₁ f₂ f₃)
        (keyProver (offlineValue (files := Z) description))
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B RunValue RunValue),
      TiedOffline Z description.source description.numbers description.later
        runValueBytes runValueBytes (offlineValue (files := Z) description) inRange w x →
      AtRunS (keyFileDescription description.source description.numbers description.later)
        (keyProver (offlineValue (files := Z) description))
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x c) :
    ∃ FT Tied TiedM, OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
      (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
      (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM 0 0 pF := by
  subst hB
  have sourced := sourced_of_ok live hd
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  have whole := offlineSides_whole scope live description hd
  rw [thePartsAt_of hd] at whole ⊢
  exact ⟨_, _, _, offlineDebts_at_parts Z scope live sourced.named inRange
    (fun _ _ h => ((AtPublicFiles.Committed.ryesZ_iff Z _ _).1 (servedRequest_below committerCoinCountLessOne Z scope hr h)).1)
    (fun i r it x => stored_at_description description hk i r it x)
    (noStopAll_keyProver _ (quietHalf_test _) (quietHalf_test _)
      (quietHalf_needs (quietHalf_test _)) (quietHalf_needs (quietHalf_test _)))
    whole.1 f₁ f₂ f₃ hZero hFalls hM hat⟩

/-- **The value of `OfflineDebts` at no fall.** The fall is the empty set at every input, named. -/
theorem offlineDebts_no_fall_at_term {B : ProofFile.Honest.ProverCoinCounts} (hB : offlineProverCoinCounts = B)
    (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {U₁ : FirstFamily Z description B} {U₂ : SharedFamily Z description B} {U₃ : LastFamily Z description B}
    {S₁ : OwnLetter Z B} {S₂ : SharedLetter Z B} {S₃ : OwnLetter Z B}
    (hM : ∀ w x, TiedOffline Z description.source description.numbers description.later
        runValueBytes runValueBytes (offlineValue (files := Z) description) inRange w x →
      (keyFileDescription description.source description.numbers description.later).okStart x = true →
      MembersS (keyFileDescription description.source description.numbers description.later)
        (bareSides (keyFileDescription description.source description.numbers description.later) B
          (keyProver (offlineValue (files := Z) description)) [] [] [])
        (keyProver (offlineValue (files := Z) description))
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B RunValue RunValue),
      TiedOffline Z description.source description.numbers description.later
        runValueBytes runValueBytes (offlineValue (files := Z) description) inRange w x →
      AtRunS (keyFileDescription description.source description.numbers description.later)
        (keyProver (offlineValue (files := Z) description))
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x c) :
    ∃ Tied TiedM, OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
      (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
      (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 := by
  subst hB
  have sourced := sourced_of_ok live hd
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  have whole := offlineSides_whole scope live description hd
  rw [thePartsAt_of hd] at whole ⊢
  exact ⟨_, _, offlineDebts_no_fall Z scope live sourced.named (Relation := ServedRequest committerCoinCountLessOne Z hr)
    inRange
    (fun _ _ h => ((AtPublicFiles.Committed.ryesZ_iff Z _ _).1 (servedRequest_below committerCoinCountLessOne Z scope hr h)).1)
    (fun i r it x => stored_at_description description hk i r it x)
    (noStopAll_keyProver _ (quietHalf_test _) (quietHalf_test _)
      (quietHalf_needs (quietHalf_test _)) (quietHalf_needs (quietHalf_test _)))
    whole.1 hM hat⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.matrixInRange_of
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDebts_at_term
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDebts_no_fall_at_term
