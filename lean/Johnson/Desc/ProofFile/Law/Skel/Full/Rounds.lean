-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Rounds.lean: the laws on the sub-protocols' declared rounds, at
the full size: the first chain's declared rounds are D, where every sub-protocol of the lots has D's
window at its spot's start. Statements and proofs.
  `frames_of_rows`  `framesSk` at the lots' skeletons is `framesSk` at the written ones, from the
                    rows
  `first_decl`      `c.blocksInOrder.flatMap (·.rounds) = D`
The premises of `first_decl`. h₁ h₂ hs hB hL hR: as `back_at_full`'s (Full/Join.lean; hs is named h₄
there). hn: D has as many rounds as the written skeletons count. **wL: a row a lot: for each
sub-protocol b of the lot and the spot p at b's place, b's rounds are D's window of their own length
at `WW p.name`. wK: the like of what a lot's batching makes at a spot's place, under that spot's
name, at every gatherer.** h₄ h₅ hc: the sub-protocols at the places, the chain and its skeletons:
`back_at_full`'s conclusion.
Limits. wL AND wK ARE THE CONTENT: this law carries the places and the order alone. NOTHING IS PAID.
The first chain alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.TilesOk
import Johnson.Desc.ProofFile.Law.Skel.Full.FramesOk
import Johnson.Desc.ProofFile.Law.Skel.Full.AskedOk
import Johnson.Desc.ProofFile.Law.Skel.SkelRoundsParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem frames_of_rows {X : List LotSk} (h : X.map (lotW asW lsW) = wsW)
    (shape : List (String × Place)) : framesSk shape X = framesSk shape ksW := by
  have e : (X.map (lotW asW lsW)).map LotW.sk =
      (X.map (LotSk.cut lsW)).map (LotSk.cutB asW) := by
    simp only [List.map_map]
    exact List.map_congr_left fun k _ => sk_lotW _ _ k
  unfold ksW
  rw [← h, e, framesSk_cutB, framesSk_cut]

theorem first_decl (Z : Pub) (T : PureSeat) (B : PureBase) (Ls : List Lot)
    (D : List Fmt.DeclaredRound) (h₁ : B.spots = spotsW) (h₂ : B.shape = shapeW)
    (hs : subsOf Z = subsW)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hL : T.lots = Ls) (hR : List.Forall₂ (RowAt B.G₀) Ls wsW) (hn : totalW = D.length)
    (wL : ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Win D WW p.name b.rounds)
    (wK : ∀ L ∈ T.lots, ∀ p ∈ B.spots, ∀ mk, L.batch B.G₀ p.place = some mk →
      ∀ g, Win D WW p.name (mk g).rounds)
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} (h₄ : (partsAt T B).base = .ok base)
    (h₅ : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c)
    (hc : c.blocksInOrder.map skel = flatW) : c.blocksInOrder.flatMap (·.rounds) = D := by
  have hf : ∀ x ∈ framesSk B.shape (T.lots.map (lotSk B.G₀)), x.2.nRounds = 0 := by
    rw [h₂, hL, frames_of_rows (rows_join B.G₀ hR)]
    intro x hx
    exact eq_of_beq (List.all_eq_true.1 frames_full x hx)
  exact rounds_are
    (back_good T B (win_nil D WW) Z hB wL (hK_of_spots h₁ wK) (fun p hp => ⟨p, hp, rfl⟩)
      (asked_are_spots h₁ hs) hf h₄ h₅) hc tiles_full hn

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.frames_of_rows
#print axioms ProofFile.Sk.Full.first_decl
