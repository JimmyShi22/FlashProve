-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotLookupsStated.lean: THE PREMISE LookupsStated (E2E/OfflineLaying.lean)
IS PAID at the offline prover's senders and the written book: each of the 935 + 920 parts of the two
lookups' rows states exactly what the book has for it.

  faces_of, faces_full   the book's faces are the faces of the sizes' own lookups: by the text of
                         KeyPub.of (E2E/KeyBook.lean); no evaluation. A TWIN: the same statement, with
                         the same proof, is the lookups' keyBookFacesAreTheLookupsFaces
                         (E2E/Lookup/Key/OneFaceUnderThreeNames.lean); it stands here
                         again because an import of that file was not at hand; one of the two goes
                         when both land
  face_at_full           so face number i of the written book is writtenFace i, at i = 0 and 1
  lookup_stands          the tie that E2E/KeyProver.lean's head leaves open («it holds only where look0,
                         look1 bear the book's faces»): a lookup at the book's place and at the
                         written face stands at the written book (LookupStandsAtTheKeyBook,
                         E2E/Lookup/Key/LookupSidePaysAtTheKeyBook.lean)
  lookupsStated_offline  LookupsStated at the senders at letters (AtPublicFiles.OfflineRows.offlineValue)

By what. The lookups' lookupRowStatesWhatTheKeyBookHas, a theorem general in the book's data
and the face, with no evaluation of the 1,855 parts; lookupsStandAtTheWrittenSizes (two faces, two
planes or more: one line to the kernel); face_of_one (E2E/OfflineLaidAtValue.lean).
Premises: KeySourced, scope, fullPub = some K₀.
Limits. On what the parts STATE (names and counts) alone: nothing on what a part sends, on whether it
plays, or on any verifier. The written sizes alone. Nothing on soundness, completeness, hiding or
binding.
-/
import E2E.OfflineLaidAtValue
import E2E.Lookup.Key.LookupSidePaysAtTheKeyBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open VerifiableInference.Desc.Key (Source LaterPlaces)
open VerifiableInference.Desc.K3 (faceOfLkp)
open OnBytes.Slice (GF)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull full_two OneFull lookPlace)
open AtPublicFiles.KeyValues (WitK oneOf)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open AtPublicFiles.Lookup.Key (LookupStandsAtTheKeyBook lookupRowStatesWhatTheKeyBookHas
  lookupsStandAtTheWrittenSizes)
open VerifierAndGoals (PublicFiles InScope)

/-! ## 1 The book's faces -/

/-- **The book's faces are the faces of the sizes' own lookups.** By the text of KeyPub.of. -/
theorem faces_of {z : OnBytes.Plan.KeySized} {a : Nat} {K : KeyPub} (h : KeyPub.of z a = some K) :
    K.faces = (OnBytes.Wf.lookupsOf z.ranges.x (OnBytes.Wf.matrixOf z.once.shape)).map faceOfLkp := by
  unfold KeyPub.of at h
  iterate 14 obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  rfl

theorem faces_full {K₀ : KeyPub} (hK : fullPub = some K₀) :
    K₀.faces = (OnBytes.Wf.lookupsOf keyFull.ranges.x
      (OnBytes.Wf.matrixOf keyFull.once.shape)).map faceOfLkp :=
  faces_of hK

/-- Face number i of the written book is the written face of that number. -/
theorem face_at_full {K₀ : KeyPub} (hK : fullPub = some K₀) (i : Nat) (hi : i < 2) :
    K₀.faces[i]? = some (writtenFace i) := by
  have two : K₀.faces.length = 2 := by simpa using of_atFull full_two hK
  rw [faces_full hK] at two ⊢
  rw [List.length_map] at two
  have hl : i < (OnBytes.Wf.lookupsOf keyFull.ranges.x
      (OnBytes.Wf.matrixOf keyFull.once.shape)).length := by omega
  unfold writtenFace
  rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

/-! ## 2 The offline prover's lookups stand at the book -/

/-- **A lookup that bears the book's place and the written face stands at the written book.** -/
theorem lookup_stands {K₀ : KeyPub} (hK : fullPub = some K₀) (i : Nat) (hi : i < 2) (a : K3.At)
    (hp : a.place = lookPlace i) (hf : a.face = writtenFace i) :
    LookupStandsAtTheKeyBook K₀ i a := by
  obtain ⟨two, faces⟩ := lookupsStandAtTheWrittenSizes K₀ hK
  obtain ⟨face, isFace, planes, -⟩ := faces i hi
  have e : face = writtenFace i := Option.some.inj (isFace.symm.trans (face_at_full hK i hi))
  exact ⟨hp, by rw [hf]; exact face_at_full hK i hi, two, by rw [hf, ← e]; exact planes⟩

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **LookupsStated at the offline prover's senders**, in scope, at the written book. -/
theorem lookupsStated_offline {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) :
    LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first) := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  have s0 := lookup_stands hK 0 (by omega)
    (offlineValue K' Xs N Pl f g inR d ent groups first).look0 rfl (face_of_one one 0)
  have s1 := lookup_stands hK 1 (by omega)
    (offlineValue K' Xs N Pl f g inR d ent groups first).look1 rfl (face_of_one one 1)
  exact ⟨fun i p hp => lookupRowStatesWhatTheKeyBookHas K₀ true 0 _ s0 _ _ _ i p hp,
    fun i p hp => lookupRowStatesWhatTheKeyBookHas K₀ true 1 _ s1 _ _ _ i p hp⟩

end Value

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.faces_of
#print axioms AtPublicFiles.OfflineRows.Lots.face_at_full
#print axioms AtPublicFiles.OfflineRows.Lots.lookup_stands
#print axioms AtPublicFiles.OfflineRows.Lots.lookupsStated_offline
