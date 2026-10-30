--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyFacesInDesc.lean: THE KEY FILE'S DESCRIPTION'S OWN TEST ON THE PLAN GIVES, AT EACH OF ITS
LOOKUPS, WHAT THE HONEST SIDE OF A LOOKUP ASKS OF THE FACE AND THE ENTRIES: the face passes its own
test, the planner makes the place's entries, and these pass `entriesFit`. So these hold in scope
wherever the gate is open. Statements and proofs, by unfolding lists and by calls; nothing is
evaluated.

Why. That the planner makes a lookup's entries at the full size is a clause of the lookup's
sub-protocol's own test on the plan (E2E/KeyFacesFull.lean). A description's test on the plan asks
every sub-protocol's. This file cuts the one down to the other.

What is shown.
  `first_planOk`: where a description's tests on the plan pass (`FileDescription.planOk`,
    Johnson/Desc/Block.lean), every sub-protocol in its first chain's flat list passes its own: the
    library's `FileDescription.planOk_ok` (Johnson/Desc/RunLaws.lean). General: any description.
  `mem_flat_of_link`: a member of a link's flat list is a member of the chain's. General.
  `hear_mem`: the lookup's own sub-protocol (`K3.lookupKind` at `lookupPlace set i x`) is a member of
    its link's flat list (`lookupLink`, Johnson/Desc/Key/Link.lean).
  **`fit_in_desc`**: where `(Key.descriptionFromSource X N P).planOk = true`: at every lookup of the source's
    one-time chain, with its number: the face's test; the entries; `entriesFit`.
  **`fit_of_live`**: Z IN SCOPE AND THE GATE OPEN (`protocolDataWellFormed (asDescriptionFiles Z) = true`): there are D, X, N,
    P such that the key file's description is laid as `FK X N P`
    (Johnson/RunOne/Sound/KeyAtFK.lean), and that holds at every lookup of X: by `theLiveAt_made`
    (Johnson/Goal/Description/Live.lean) and `all_at_o` (Johnson/RunOne/Law/AllAtO.lean).

Limits.
- The source X is had by "there is" alone: no closed term.
- That the gate is open at any Z is not shown here.
- Nothing on any prover. Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyFacesFull
import Johnson.Desc.Key.Desc
import Johnson.Desc.RunLaws
import Johnson.RunOne.Law.AllAtO
import Johnson.Goal.Description.Live
import Johnson.Goal.Tie.ReadThruHead

set_option autoImplicit false

namespace AtPublicFiles.KeyFaces
open VerifiableInference.Desc (Block Chain Link FileDescription blocksOk)
open VerifiableInference.Desc.K3 (lookupKind entriesFit)
open VerifiableInference.Desc.Key (descriptionFromSource firstChain lookupLink lookupPlace lookupsOf lookupSeat
  Source LaterPlaces FirstState Claim)

/-! ## 1. General -/

theorem first_planOk {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    ∀ b ∈ F.first.blocksInOrder, b.planOk = true :=
  fun b hm => (((F.planOk_ok).1 h).blocks₁ b hm).1

theorem mem_flat_of_link {S Cl : Type} (c : Chain S Cl) {K : Link S Cl} (hK : K ∈ c.links)
    {b : Block S Cl} (hb : b ∈ K.blocksInOrder) : b ∈ c.blocksInOrder := by
  show b ∈ _ :: _ ++ c.links.flatMap Link.blocksInOrder ++ _ ++ _
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨K, hK, hb⟩)))

/-! ## 2. The key file's lookups -/

theorem hear_mem (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : ℕ)
    (x : VerifiableInference.Desc.Key.Lookup) :
    lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x) ∈
      (lookupLink one set i x).blocksInOrder := by
  show _ ∈ _ :: (lookupLink one set i x).hear ++ _ ++ _ ++ _
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))))

theorem fit_in_desc (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (h : (descriptionFromSource X N P).planOk = true) (y : VerifiableInference.Desc.Key.Lookup × ℕ)
    (hy : y ∈ (lookupsOf X.Y.k.oneTime).zipIdx) :
    (lookupPlace X.set y.2 y.1).face.ok = true ∧
      ∃ es, (lookupPlace X.set y.2 y.1).entries = some es ∧
        entriesFit (lookupPlace X.set y.2 y.1).face es = true := by
  have hm : lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set y.2 y.1) ∈
      (firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).blocksInOrder :=
    mem_flat_of_link _ (List.mem_map.2 ⟨y, hy, rfl⟩) (hear_mem X.Y.k.oneTime X.set y.2 y.1)
  have hp : (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set y.2 y.1)).planOk = true :=
    first_planOk h _ hm
  exact fit_of_planOk hp

/-! ## 3. In scope, with the gate open -/

theorem fit_of_live {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ D X N P, FlashProve.theKeyLaid (VerifierAndGoals.asDescriptionFiles Z) =
        .ok (D, (Johnson.RunOne.Sound.FK X N P).run) ∧
      ∀ y ∈ (lookupsOf X.Y.k.oneTime).zipIdx,
        (lookupPlace X.set y.2 y.1).face.ok = true ∧
          ∃ es, (lookupPlace X.set y.2 y.1).entries = some es ∧
            entriesFit (lookupPlace X.set y.2 y.1).face es = true := by
  obtain ⟨K, -, -, hK, -, -⟩ := FlashProve.theLiveAt_made OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) live
  obtain ⟨D, r⟩ := K
  obtain ⟨X, N, P, hp, -, hr, -⟩ := Johnson.RunOne.Law.AllAtO.all_at_o hZ hK
  subst hr
  exact ⟨D, X, N, P, hK, fun y hy => fit_in_desc X N P hp y hy⟩

end AtPublicFiles.KeyFaces

#print axioms AtPublicFiles.KeyFaces.first_planOk
#print axioms AtPublicFiles.KeyFaces.mem_flat_of_link
#print axioms AtPublicFiles.KeyFaces.hear_mem
#print axioms AtPublicFiles.KeyFaces.fit_in_desc
#print axioms AtPublicFiles.KeyFaces.fit_of_live
