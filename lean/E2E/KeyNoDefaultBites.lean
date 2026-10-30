-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyNoDefaultBites.lean: in scope and live, the defaults that thePartsAt's terms fall to do not
bite. The list: lookAt, witAt (two lookups); baseAt, battAt
(a block at the place); batchedRowsSending (a message W); mainOf (a code at its number); T1's offlineTestOnOmega (a
test on Omega); offlineProverCoinCounts (fullPub is some).

  roundsInFront_isSome   a block at the place gives a number of rounds
  NoDefaultBites, noDefaultBites   the clauses; in scope and live they hold

Limits. Only these seven. What the terms called beneath carry (proximityTestParametersAt's noP12, recRanges' error arm,
bsOf's [], doorKW's idleT12, elemAt's 0) is not here. Nothing on any property.
-/
import E2E.KeyThePartsFacts
import E2E.KeyPlacesNamed
import E2E.KeyBookPassesNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open VerifiableInference.Desc (Block Place)
open AtPublicFiles.KeyValues (oneOf blocksOf placeAt)
open ProofFile.Honest (roundsInFront)
open Johnson.RunOne.Sound (rowsOf)

/-- A block at the place gives a number of rounds. -/
theorem roundsInFront_isSome {S Cl : Type} (a : Place) : ∀ (blocks : List (Block S Cl)),
    a ∈ (rowsOf blocks).map Prod.fst → (roundsInFront blocks a).isSome = true
  | [], h => by simp [rowsOf] at h
  | b :: blocks, h => by
    unfold roundsInFront
    by_cases e : (b.place == a) = true
    · rw [if_pos e]
      rfl
    · rw [if_neg e]
      have h' : a ∈ (rowsOf blocks).map Prod.fst := by
        simp only [rowsOf, List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact absurd (by rw [h]; simp) e
        · exact h
      have := roundsInFront_isSome a blocks h'
      cases hr : roundsInFront blocks a with
      | none => rw [hr] at this; cases this
      | some n => rfl

/-- **The clauses.** -/
structure NoDefaultBites (description : OfflineDescription) : Prop where
  lookups : (oneOf description.source).ranges.lookups.length = 2
  base : ∀ i, i < 2 →
    (roundsInFront (blocksOf description.source description.numbers) (placeAt i)).isSome = true
  batt : (roundsInFront (blocksOf description.source description.numbers)
    (⟨1, none, VerifiableInference.Desc.Key.pieces.batt, .K13⟩ : Place)).isSome = true
  hasW : (OnBytes.linMessageW (oneOf description.source).lin).isSome = true
  code : (oneOf description.source).ranges.message.shape.code <
    (oneOf description.source).codes.base.size
  omega : description.later.O.isSome = true
  book : AtPublicFiles.KeyBook.fullPub.isSome = true

variable {files : PublicFiles}

theorem written_lookups : Lk6.AtPlan.keyFull.ranges.x.lookups.length = 2 := by decide +kernel

theorem written_W : (OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape).isSome = true := by
  decide +kernel

theorem written_code : Lk6.AtPlan.keyFull.ranges.x.message.shape.code <
    Lk6.AtPlan.keyFull.codes.base.size := by decide +kernel

theorem written_omega : AtPublicFiles.AtFiles.Full.PF.O.isSome = true := by decide +kernel

/-- **In scope and live none of these bites.** -/
theorem noDefaultBites (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    NoDefaultBites description := by
  have sourced := sourced_of_ok live h
  obtain ⟨-, e1, e2, -, e4⟩ := AtPublicFiles.AtFiles.five_sourced sourced scope
  obtain ⟨r1, -, -⟩ := AtPublicFiles.KeyBook.places_named scope sourced.named
  have hb : ∀ a : Place, a ∈ AtPublicFiles.KeyBook.fullFirst.map Prod.fst →
      (roundsInFront (blocksOf description.source description.numbers) a).isSome = true := by
    intro a ha
    refine roundsInFront_isSome a _ ?_
    show a ∈ (rowsOf (keyFileDescription description.source description.numbers description.later).first.blocksInOrder).map
      Prod.fst
    rw [r1]
    exact ha
  refine ⟨?_, fun i hi => hb _ ?_, hb _ ?_, ?_, ?_, ?_, ?_⟩
  · show description.source.Y.k.oneTime.ranges.lookups.length = 2
    rw [e1]
    exact written_lookups
  · interval_cases i <;> decide +kernel
  · decide +kernel
  · show (OnBytes.linMessageW description.source.Y.k.oneTime.lin).isSome = true
    rw [e2]
    exact written_W
  · show description.source.Y.k.oneTime.ranges.message.shape.code <
      description.source.Y.k.oneTime.codes.base.size
    rw [e1, e4]
    exact written_code
  · rw [later_written scope live h]
    exact written_omega
  · obtain ⟨K, hK⟩ := AtPublicFiles.KeyBook.full_made
    rw [hK]
    rfl

end AtPublicFiles.AtFiles.HonestTerm
