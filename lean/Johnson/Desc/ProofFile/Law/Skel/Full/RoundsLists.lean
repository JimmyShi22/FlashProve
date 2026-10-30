-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/RoundsLists.lean: the laws on the sub-protocols' declared
rounds, at the full size, by the written table of lists: the first chain's declared rounds are the
written ones (`declProofFull.1`, Johnson/AtFull/ProofRows/WrittenProof.lean), where every
sub-protocol of the lots has no round or the list that the table `listAt`
(Johnson/AtFull/Rounds/ListAt.lean) gives at its spot's name. Statements and proofs.
  `flat_cut`          `flatW.map Skel.row = cutFirstFull`: off `cut_tie` (Full/Ties.lean)
  `flat_names`        the written skeletons' names are the written cut's
  `flat_counts`       their names and numbers of rounds are the written cut's: the premise of
                      `first_if` (Johnson/AtFull/Rounds/ListAtFits.lean)
  `first_decl_lists`  `c.blocksInOrder.flatMap (·.rounds) = declProofFull.1`
The premises of `first_decl_lists`. h₁ h₂ hs hB hL hR: as `back_at_full`'s (Full/Join.lean; hs is
named h₄ there). **wL: a row a lot: for each sub-protocol b of the lot and the spot p at b's place:
b has no round, or b's rounds are `listAt p.name`. wK: the like of what a lot's batching makes at a
spot's place, under that spot's name, at every gatherer.** h₄ h₅ hc: the sub-protocols at the
places, the chain and its skeletons: `back_at_full`'s conclusion.
Limits. wL AND wK ARE THE CONTENT: this law carries the places and the order alone. NOTHING IS PAID.
The first chain alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Rounds
import Johnson.Desc.ProofFile.Law.Skel.Full.Ties
import Johnson.Desc.ProofFile.Law.Skel.SkelLists
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.AtFull.Rounds.ListAtFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.PlanWritten (cutFirstFull sameRows_iff)
open Johnson.AtFull.Rounds (first_if)
open Johnson.AtFull.ProofRows (declProofFull)

theorem flat_cut : flatW.map Skel.row = cutFirstFull := (sameRows_iff _ _).1 cut_tie

theorem flat_names : flatW.map (·.name) = cutFirstFull.map (·.1) := by
  rw [← flat_cut, List.map_map]
  rfl

theorem flat_counts :
    (flatW.map fun k => (k.name, k.nRounds)) = cutFirstFull.map fun r => (r.1, r.2.2.1) := by
  rw [← flat_cut, List.map_map]
  rfl

theorem first_decl_lists (Z : Pub) (T : PureSeat) (B : PureBase) (Ls : List Lot)
    (h₁ : B.spots = spotsW) (h₂ : B.shape = shapeW) (hs : subsOf Z = subsW)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hL : T.lots = Ls) (hR : List.Forall₂ (RowAt B.G₀) Ls wsW)
    (wL : ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Lst Johnson.AtFull.Rounds.listAt p.name b.rounds)
    (wK : ∀ L ∈ T.lots, ∀ p ∈ B.spots, ∀ mk, L.batch B.G₀ p.place = some mk →
      ∀ g, Lst Johnson.AtFull.Rounds.listAt p.name (mk g).rounds)
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} (h₄ : (partsAt T B).base = .ok base)
    (h₅ : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c)
    (hc : c.blocksInOrder.map skel = flatW) : c.blocksInOrder.flatMap (·.rounds) = declProofFull.1 := by
  have hf : ∀ x ∈ framesSk B.shape (T.lots.map (lotSk B.G₀)), x.2.nRounds = 0 := by
    rw [h₂, hL, frames_of_rows (rows_join B.G₀ hR)]
    intro x hx
    exact eq_of_beq (List.all_eq_true.1 frames_full x hx)
  exact lists_are
    (back_good T B (lst_nil Johnson.AtFull.Rounds.listAt) Z hB wL (hK_of_spots h₁ wK)
      (fun p hp => ⟨p, hp, rfl⟩) (asked_are_spots h₁ hs) hf h₄ h₅)
    hc
    (first_if flatW (·.name) (·.nRounds) flat_counts)

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.flat_cut
#print axioms ProofFile.Sk.Full.flat_names
#print axioms ProofFile.Sk.Full.flat_counts
#print axioms ProofFile.Sk.Full.first_decl_lists
