-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFirstPublicAtValue.lean: FirstPublic (E2E/FirstHSeats.lean: what is public at the key file's three
sendings and the batching: a premise of the lots on the first chain's thread T₁) IS MET AT THE REAL VALUE, in
scope: at the offline prover's own senders (offlineValue, E2E/KeyStandWalked.lean) and the index's reader
matrixReader (E2E/KeyArgumentsAt.lean).

  w_message       in scope the shape has a message W
  LotSheetAtValue, sheetAt_atValue   SheetAt (E2E/FirstHPublic.lean) at the value: the six equations by rfl, the
                  seven places by atPlaces_value (E2E/KeyValueHolds.lean)
  LotFirstPublic, firstPublic_atValue   so FirstPublic there: one call of first_public (E2E/FirstHPublic.lean)
  LotFirstPublicAtFiles, firstPublic_atFiles   the same at whatever offlineDescription returns, where the test on
                  the public files says yes

Limits. In scope, at the written sizes. Public facts alone: nothing on a run, nothing on what a sender holds.
KeySourced is had where the test on the public files says yes (key_sourced, E2E/KeyPublic.lean): that test
and InScope stay premises. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.FirstHPublic
import E2E.KeyValueHolds
import E2E.KeyStandWalked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyValueHolds (atPlaces_value)
open AtPublicFiles.KeyValues (oneOf)
open VerifierAndGoals (PublicFiles InScope)

/-- In scope the shape has a message W. -/
theorem w_message {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (OnBytes.linMessageW (oneOf Xs).lin).isSome = true := by
  obtain ⟨bw, hw⟩ := w_there hs scope
  exact some_of_map (show (OnBytes.linMessageW (oneOf Xs).lin).map _ = some bw from hw)

/-- **The offline prover's own senders are the sheet's and stand at the first chain's places.** -/
def LotSheetAtValue : Prop :=
  ∀ {Z files : PublicFiles} {description : OfflineDescription},
    KeySourced Z description.source description.numbers description.later → InScope Z = true →
    SheetAt description.source description.numbers (offlineValue (files := files) description)
      matrixReader

theorem sheetAt_atValue : LotSheetAtValue := fun hs scope =>
  ⟨atPlaces_value _ _ _ _ _ _ _ _ _ _ _ _ _ (w_message hs scope), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **FirstPublic at the offline prover's own senders.** -/
def LotFirstPublic : Prop :=
  ∀ {Z files : PublicFiles} {description : OfflineDescription},
    KeySourced Z description.source description.numbers description.later → InScope Z = true →
    FirstPublic (Pl := description.later) description.source description.numbers
      (offlineValue (files := files) description) matrixReader

theorem firstPublic_atValue : LotFirstPublic := fun hs scope =>
  first_public hs scope (sheetAt_atValue hs scope)

/-- **The same at whatever description the three public files make**, where the test on them says yes. -/
def LotFirstPublicAtFiles : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription}, offlineDescription Z = .ok description →
    InScope Z = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true →
    FirstPublic (Pl := description.later) description.source description.numbers
      (offlineValue (files := Z) description) matrixReader

theorem firstPublic_atFiles : LotFirstPublicAtFiles := by
  intro Z d hd scope live
  obtain ⟨X, N, P, hs⟩ := AtPublicFiles.AtFiles.key_sourced Z live
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  have e : offlineDescription Z = .ok ⟨X, N, P⟩ := by
    simp only [offlineDescription, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]
  rw [hd] at e
  obtain rfl : d = ⟨X, N, P⟩ := Except.ok.inj e
  exact firstPublic_atValue hs scope

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.first_public
#print axioms AtPublicFiles.FirstH.Lots.w_message
#print axioms AtPublicFiles.FirstH.Lots.sheetAt_atValue
#print axioms AtPublicFiles.FirstH.Lots.firstPublic_atValue
#print axioms AtPublicFiles.FirstH.Lots.firstPublic_atFiles
