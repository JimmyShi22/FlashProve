-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLookupFields.lean: the fields `exact` and `fresh` at the rows of the key file's two lookups,
at the key file's own sub-protocols: the per-part sentences at 976 masked sumchecks and 879 quiet
parts (the numbers: E2E/OfflineLookupCounts.lean).

  `look_block`      the sub-protocol at a lookup's place: it declares the face's entries, bare, with no
                    oracle message, and the face passes its own test: off the description's test on
                    its plan
  `look_row_good`   `Good` at a lookup's row at owners, at the written book

Each sentence is one part at a time, the spender's half alone, at every job, right or wrong. It says
nothing on whether a job is the protocol's, and nothing of the owner of the stretches that a part
spends: that is `fresh` at the owner. This is not the sentence on the file. Nothing on any property.
-/
import E2E.OfflineMembers
import E2E.OfflineRowFields
import E2E.KeyFirstSends
import E2E.KeyFacesInDesc
import Johnson.SendSim.Seat.AtKeyStands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource firstChain lookupPlace lookupsOf lookupSeat)
open VerifiableInference.Desc.K3 (lookupKind entriesFit)
open AtPublicFiles.KeyFaces (fit_in_desc hear_mem mem_flat_of_link)
open OnBytes.SendSim.Seat (key_places_apart)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (faceAt lookAt)

section Blocks
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **The sub-protocol at lookup i's place**: it declares a list of entries, bare, with no oracle
message, and these are the face's; the face passes its own test. -/
theorem look_block (hp : (descriptionFromSource X N P).planOk = true) {i : Nat}
    (hi : i < (lookupsOf X.Y.k.oneTime).length) {b : Block _ _}
    (hb : b ∈ (descriptionFromSource X N P).first.blocksInOrder) (hpl : b.place = ⟨1, some i, 2, .K3⟩) :
    (faceAt X i).ok = true ∧ ∃ es : List Fmt.Entry, b.rounds = es.map declOf ∧
      b.oracles = es.map (fun _ => []) ∧ entriesFit (faceAt X i) es = true := by
  have hget : (lookupsOf X.Y.k.oneTime).getD i default = (lookupsOf X.Y.k.oneTime)[i] := by
    rw [List.getD_eq_getElem _ _ hi]
  have hy : ((lookupsOf X.Y.k.oneTime)[i], i) ∈ (lookupsOf X.Y.k.oneTime).zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp [hi]
  obtain ⟨hok, es, he, hf⟩ := fit_in_desc X N P hp _ hy
  have hm : lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set i (lookupsOf X.Y.k.oneTime)[i]) ∈
      (descriptionFromSource X N P).first.blocksInOrder :=
    mem_flat_of_link (firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N)
      (List.mem_map.2 ⟨_, hy, rfl⟩) (hear_mem X.Y.k.oneTime X.set i _)
  have e : b = lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (lookupPlace X.set i (lookupsOf X.Y.k.oneTime)[i]) :=
    List.inj_on_of_nodup_map (key_places_apart X N P) hb hm hpl
  have hface : faceAt X i = (lookupPlace X.set i (lookupsOf X.Y.k.oneTime)[i]).face := by
    unfold faceAt lookAt
    rw [hget]
    rfl
  rw [hface]
  refine ⟨hok, es, ?_, ?_, hf⟩
  · rw [e]
    show ((lookupPlace X.set i (lookupsOf X.Y.k.oneTime)[i]).entries.getD []).map _ = _
    rw [he]
    rfl
  · rw [e]
    show ((lookupPlace X.set i (lookupsOf X.Y.k.oneTime)[i]).entries.getD []).map _ = _
    rw [he]
    rfl

end Blocks

section Rows
variable {V' W' Y' Pb Wk : Type}

/-- **`Good` at a lookup's row at owners**, at the key file's sub-protocol at the written book: fits
given, exact at every On and bud, fresh because nobody spends its parts' coins. -/
theorem look_row_good {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hpl : (descriptionFromSource X N P).planOk = true) {i : Nat} (hi : i < (lookupsOf X.Y.k.oneTime).length)
    (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs Wk) (wit : W' → Wk) (a : K3.At)
    (hp : a.place = ⟨1, some i, 2, .K3⟩) (hface : a.face = faceAt X i) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (hown : ∀ j, (⟨a.place, j⟩ : Addr) ∉ bookOwners)
    (fs : List (Fall (descriptionFromSource X N P).S₁))
    (σ : Side (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl V' W' Y' Pb)
    (hσ : Side.seated (descriptionFromSource X N P).first.blocksInOrder a.place
      ((K3.proverSideOfLookupInChain o R J wit a).parts.zip (K3.lookSims a)) fs = some σ)
    (hf : σ.fits = true) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V' W' Pb)
    (ord : List Place) (chain firstTree : Nat)
    (On : (u : Member V' W' Y' Pb) → CsAll u.part.carries → Mid W' Y' → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    Good pre φ σ (keyBook K₀) ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud := by
  have hrow : σ.row = (K3.proverSideOfLookupInChain o R J wit a).parts.zip (K3.lookSims a) := by
    unfold Side.seated at hσ
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
    rfl
  have hbp : σ.block.place = a.place := OnBytes.SendSim.At.place_of_seated hσ
  have hbm : σ.block ∈ (descriptionFromSource X N P).first.blocksInOrder := OnBytes.SendSim.Seat.block_of_seated hσ
  obtain ⟨hok, es, e1, e2, e3⟩ := look_block X N P hpl hi hbm (hbp.trans hp)
  have hSt : RowStated a.face σ :=
    rowStated_owned o R J wit a hrow es e1 e2 (by rw [hface]; exact e3) (by rw [hface]; exact hok)
  refine good_of_row hf (k3_exact_owned φ o R J wit a hrow hSt chain firstTree On bud)
    (fresh_of_owns_none φ σ (keyBook K₀) ord bud fun u _ q => ?_)
  rw [hbp]
  exact spent_none hK (hown _) q

end Rows

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.look_block
#print axioms AtPublicFiles.OfflineRows.look_row_good
