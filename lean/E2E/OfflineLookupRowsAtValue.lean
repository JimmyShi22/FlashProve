-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLookupRowsAtValue.lean: the share of `OwedRest.good` (E2E/OfflineClauses.lean) at the rows of
the key file's two lookups, in that field's own form (a member of the muted rows' first list, at the
muted rows' falls), and at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean).

  `lookup_rows_good_mute`   E2E/OfflineLookupRowsGood.lean's `lookup_rows_goodAt`, in the field's form
  `lookup_rows_at_value`    the same at `valueAt`: the places and the two faces are the value's own, by
                            unfolding; that the shape has a message W is read off the written sizes
  `lookup_rows_at_laid`     the same at `laidSimulators`, whatever the ten lists that are letters
  `lookup_rows_there`       A TEST OF EMPTINESS: the first list has a row at each of the two places, and
                            each has a side; `value_atPlaces` pays its premise at the value

The limits are those of E2E/OfflineLookupRowsGood.lean: the spender's half alone; what the lookups' parts
spend is taken as uniform, and that it is so is the field `fresh` at the two owners, which is neither
shown nor assumed here. Nothing on any property.
-/
import E2E.OfflineLookupRowsGood
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace)
open AtPublicFiles.KeyValues (WitK faceAt oneOf)
open AtPublicFiles.KeyValueHolds (valueAt atPlaces_value)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Letters
variable {W₀ Rc Wk : Type}

/-- **The two rows in the form of `OwedRest.good`'s first clause.** -/
theorem lookup_rows_good_mute {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hf0 : K.look0.face = faceAt Xs 0) (hf1 : K.look1.face = faceAt Xs 1) (S : OfflineSimulators)
    (h0 : S.lookup0 = K3.lookSims K.look0) (h1 : S.lookup1 = K3.lookSims K.look1)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first,
      (L.place = lookPlace 0 ∨ L.place = lookPlace 1) →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.falls₁ := by
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact lookup_rows_goodAt hs scope hK hB K hA hf0 hf1 S h0 h1 c L' hL' hp

/-- **A TEST OF EMPTINESS.** In scope, at letters that bear the first chain's places, the muted rows'
first list has a row at each of the two lookups' places, and that row has a side at the description's
first chain: so the sentence above speaks of two sides. -/
theorem lookup_rows_there {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) (i : Nat)
    (hi : i = 0 ∨ i = 1) :
    ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = lookPlace i ∧
      ((L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
        []).isSome = true := by
  obtain ⟨r1, -, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have hin : ∀ p ∈ ([lookPlace 0, lookPlace 1] : List Place),
      p ∈ AtPublicFiles.KeyBook.fullFirst.map (·.1) := by decide
  have hmem : ∀ h ∈ (keyProver K).first, h.place = lookPlace i →
      ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = lookPlace i ∧
        ((L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
          []).isSome = true := by
    intro h hh hp
    refine ⟨(rowOf h (S.byChain.first h.place) (c.first h.place)).mute,
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨h, hh, rfl⟩, rfl⟩, hp, ?_⟩
    refine side_isSome _ _ _ ?_
    show h.place ∈ _
    rw [hp, places_of_rows r1]
    rcases hi with rfl | rfl
    · exact hin _ (by simp)
    · exact hin _ (by simp)
  rcases hi with rfl | rfl
  · exact hmem (K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0)
      (by rw [AtPublicFiles.KeyFile.keyProver_first]; simp) hA.look0
  · exact hmem (K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1)
      (by rw [AtPublicFiles.KeyFile.keyProver_first]; simp) hA.look1

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- In scope the value bears the first chain's seven places. -/
theorem value_atPlaces {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtPlaces := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  refine atPlaces_value K' Xs N Pl f g inR d pU pO ent groups first ?_
  show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
  rw [el]
  decide +kernel

/-- **The two rows at the offline prover's own senders.** -/
theorem lookup_rows_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (S : OfflineSimulators)
    (h0 : S.lookup0 = K3.lookSims (valueAt K' Xs N Pl f g inR d pU pO ent groups first).look0)
    (h1 : S.lookup1 = K3.lookSims (valueAt K' Xs N Pl f g inR d pU pO ent groups first).look1)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.first,
      (L.place = lookPlace 0 ∨ L.place = lookPlace 1) →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                     (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.falls₁ :=
  lookup_rows_good_mute hs scope hK hB _
    (value_atPlaces K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl S h0 h1 c

/-- **The same at the laid simulators**, whatever the ten lists that are letters. -/
theorem lookup_rows_at_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.first,
      (L.place = lookPlace 0 ∨ L.place = lookPlace 1) →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                     (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                     (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.falls₁ :=
  lookup_rows_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB _ rfl rfl c

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.lookup_rows_good_mute
#print axioms AtPublicFiles.OfflineRows.value_atPlaces
#print axioms AtPublicFiles.OfflineRows.lookup_rows_at_value
#print axioms AtPublicFiles.OfflineRows.lookup_rows_at_laid
#print axioms AtPublicFiles.OfflineRows.lookup_rows_there
