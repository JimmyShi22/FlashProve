-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLookupRowsGood.lean: the field `good` of `OwedRest` (E2E/OfflineClauses.lean) at the rows of
the key file's two lookups: `goodAt` at the muted rows, at the key file's own description, at the
written book, in scope, at any letters K that bear the key file's places and the description's two
faces, and at any lists of simulators whose two lists for the lookups are `K3.lookSims`.

  `look_owns_none`   no part of a lookup is one of the six owners of the written book's entries
  `look_fits`        `Side.fits` at a lookup's row at owners, off the description's own test on its
                     plan: it reads no book, and so takes no premise on what the book states
  `look_beside`      a lookup's parts beside `K3.lookSims` are the zip of the two lists
  `lookup_rows_goodAt`   the two rows

What it leans on. `KeySourced`, scope, the written book. No premise on the book's entries at the
lookups' parts (`LookupsStated`, E2E/OfflineLaying.lean) is taken.

Limits. `A` and `B` are false at a muted row, so `plays` and `acc` are vacuous. `exact` is one part at a
time and the spender's half alone: it is over coins drawn uniformly for the stretches that the part
spends. THAT THESE STRETCHES ARE UNIFORM AND INDEPENDENT OF WHAT THEIR OWNERS SHOW IS NOT SHOWN AND NOT
ASSUMED HERE: it is the field `fresh` at the two owners, the sendings of the multiplicities and of the
index masks, at each of the lookups' parts that spends. `fresh` at the lookups' own parts holds because
no part spends their coins: they own none, and the field carries nothing there. The statements stand at
jobs right or wrong. Nothing on any property.
-/
import E2E.OfflineLookupFields
import E2E.OfflineMembersFits
import E2E.KeyPublic
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource lookupsOf)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace)
open AtPublicFiles.KeyValues (faceAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

/-- No part of a lookup is an owner of an entry of the written book: each of the six owners stands
outside the links. -/
theorem look_owns_none (i j : Nat) : (⟨⟨1, some i, 2, .K3⟩, j⟩ : Addr) ∉ bookOwners := by
  intro h
  have e := (by decide : ∀ a ∈ bookOwners, a.place.link = none) _ h
  exact absurd e (by simp)

section Fits
variable {V' W' Y' Pb Wk : Type}

/-- **A lookup's row at owners passes the frame's test on a side**, at the key file's sub-protocol. It
reads no book. -/
theorem look_fits {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hpl : (descriptionFromSource X N P).planOk = true) {i : Nat} (hi : i < (lookupsOf X.Y.k.oneTime).length)
    (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs Wk) (wit : W' → Wk) (a : K3.At)
    (hp : a.place = ⟨1, some i, 2, .K3⟩) (hface : a.face = faceAt X i)
    (fs : List (Fall (descriptionFromSource X N P).S₁))
    (σ : Side (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl V' W' Y' Pb)
    (hσ : Side.seated (descriptionFromSource X N P).first.blocksInOrder a.place
      ((K3.proverSideOfLookupInChain o R J wit a).parts.zip (K3.lookSims a)) fs = some σ) :
    σ.fits = true := by
  have hrow : σ.row = (K3.proverSideOfLookupInChain o R J wit a).parts.zip (K3.lookSims a) := by
    unfold Side.seated at hσ
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
    rfl
  have hbp : σ.block.place = a.place := OnBytes.SendSim.At.place_of_seated hσ
  have hbm : σ.block ∈ (descriptionFromSource X N P).first.blocksInOrder := OnBytes.SendSim.Seat.block_of_seated hσ
  obtain ⟨hok, es, e1, e2, e3⟩ := look_block X N P hpl hi hbm (hbp.trans hp)
  exact fits_owned o R J wit a hrow hbp es e1 e2 (by rw [hface]; exact e3) (by rw [hface]; exact hok)

/-- A lookup's parts beside its simulators are the zip of the two lists. -/
theorem look_beside (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs Wk) (wit : W' → Wk) (a : K3.At) :
    partsBeside (K3.proverSideOfLookupInChain (V₁ := V') (X₁ := Y') o R J wit a).parts (K3.lookSims (Pb := Pb) a) =
      (K3.proverSideOfLookupInChain (V₁ := V') (X₁ := Y') o R J wit a).parts.zip (K3.lookSims (Pb := Pb) a) := by
  refine partsBeside_eq_zip _ _ ?_
  have e := congrArg List.length (owned_seat_moves (V := V') (X := Y') o R J wit a)
  rw [List.length_map, List.length_map] at e
  rw [e, K3.lookSims_length]

end Fits

section Value
variable {W₀ Rc Wk : Type}

/-- **`goodAt` at the muted rows of the two lookups**: the share of `OwedRest.good` at rows 3 and 4 of
the first chain. The book is a letter that equals the written book, so that it serves at a constant. -/
theorem lookup_rows_goodAt {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hf0 : K.look0.face = faceAt Xs 0)
    (hf1 : K.look1.face = faceAt Xs 1) (S : OfflineSimulators)
    (h0 : S.lookup0 = K3.lookSims K.look0) (h1 : S.lookup1 = K3.lookSims K.look1)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first,
      (L.place = lookPlace 0 ∨ L.place = lookPlace 1) →
      (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 [] := by
  subst hB
  obtain ⟨-, er, el, -, -⟩ := five_sourced hs scope
  have hlen : (lookupsOf Xs.Y.k.oneTime).length = 2 := by
    unfold VerifiableInference.Desc.Key.lookupsOf
    rw [er, el]
    decide +kernel
  have apart : ∀ p : Place, p.link = none → ¬ (p = lookPlace 0 ∨ p = lookPlace 1) := by
    intro p hp h
    rcases h with rfl | rfl <;> cases hp
  intro L hL hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL
  have hp' : h.place = lookPlace 0 ∨ h.place = lookPlace 1 := hp
  rw [keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hp' (apart _ (by show K.idx.P.place.link = none; rw [hA.idx]))
  · exact absurd hp' (apart _ (by show K.msg.P.place.link = none; rw [hA.msg]))
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.look0.place
        (partsBeside (K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit
          K.look0).parts (S.byChain.first K.look0.place)) [] = some σ := hσ
    have es : S.byChain.first K.look0.place = K3.lookSims K.look0 := by
      rw [hA.look0]
      exact h0
    rw [es, look_beside] at hσ'
    exact look_row_good hs.named.plan (i := 0) (by omega) _ _ _ _ _ hA.look0 hf0 hK
      (by rw [hA.look0]; exact look_owns_none 0) [] σ hσ'
      (look_fits hs.named.plan (i := 0) (by omega) _ _ _ _ _ hA.look0 hf0 [] σ hσ') _ _ _ _ _ _ _
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.look1.place
        (partsBeside (K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit
          K.look1).parts (S.byChain.first K.look1.place)) [] = some σ := hσ
    have es : S.byChain.first K.look1.place = K3.lookSims K.look1 := by
      rw [hA.look1]
      exact h1
    rw [es, look_beside] at hσ'
    exact look_row_good hs.named.plan (i := 1) (by omega) _ _ _ _ _ hA.look1 hf1 hK
      (by rw [hA.look1]; exact look_owns_none 1) [] σ hσ'
      (look_fits hs.named.plan (i := 1) (by omega) _ _ _ _ _ hA.look1 hf1 [] σ hσ') _ _ _ _ _ _ _
  · exact absurd hp' (apart _ (by rw [hA.rng]))
  · exact absurd hp' (apart _ (by show (K13.k13Place K.batt).link = none; rw [hA.batt]))
  · exact absurd hp' (apart _ (by show K.w.P.place.link = none; rw [hA.w]))

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.look_owns_none
#print axioms AtPublicFiles.OfflineRows.look_fits
#print axioms AtPublicFiles.OfflineRows.look_beside
#print axioms AtPublicFiles.OfflineRows.lookup_rows_goodAt
