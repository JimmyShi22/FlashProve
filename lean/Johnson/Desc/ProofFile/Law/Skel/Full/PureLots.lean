-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/PureLots.lean: TOOLS FOR THE JOINS AT `ProofFile.pureSeat`: from a
sentence a lot, by name, to "at every lot of `ProofFile.onlineFirstChainBlockTables Z`" (ProofFile/OnlineDescriptionBlocks.lean); and the
rounds' column's two premises (SkelRoundsParts.lean: hL, hK) in that form. Statements and proofs.
  `lots_all`     P at each of the thirteen lots by name and at the two of `p4Pure Z`: P at every lot
  `wK_pure`      hK (at the spots' places) at `onlineFirstChainBlockTables Z`, at every Q, from K9's lot's alone: twelve
                 supply no batching, by their texts; of the two of `p4Pure Z` it is a premise
  `wL_pure`      hL at `pureSeat o Z`, at every Q, from a sentence a lot at `nameW`
                 (Full/Names.lean)
  `good_at_pure` so Q holds of the name and the rounds of every block of the first chain's flat list
Limits. Q is a letter. NOTHING IS PAID: every sentence on a lot's blocks' rounds is a premise. The
full size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Fifteen
import Johnson.Desc.ProofFile.Law.Skel.Full.Names
import Johnson.Desc.ProofFile.Law.Skel.Full.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem lots_all {Z : Pub} {P : Lot → Prop} {L13 L14 : Lot} (hp : p4Pure Z = [L13, L14])
    (p0 : P (framesLot Z)) (p1 : P (k1Pure Z)) (p2 : P (k2Pure Z)) (p3 : P (K3Lot.lot Z))
    (p4 : P (k4Lot Z)) (p5 : P (H2K5.lotN Z)) (p6 : P (P1K8.lot Z)) (p7 : P (k9Ninth Z))
    (p8 : P (K11.lot Z)) (p9 : P (VerifiableInference.Desc.K12.lot Z))
    (p10 : P (VerifiableInference.Desc.K13.lot Z))
    (p11 : P (VerifiableInference.Desc.K13.lot4 Z))
    (p12 : P (VerifiableInference.Desc.K13.lotEnd Z)) (p13 : P L13) (p14 : P L14) :
    ∀ L ∈ onlineFirstChainBlockTables Z, P L := by
  intro L hL
  unfold onlineFirstChainBlockTables at hL
  rw [hp] at hL
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14

section
variable {Q : String → List Fmt.DeclaredRound → Prop}

/-- A lot that supplies no batching owes nothing to hK. -/
theorem wK_none {G : Ground} {L : Lot} {spots : List Spot} (h : ∀ a, L.batch G a = none) :
    ∀ p ∈ spots, ∀ mk, L.batch G p.place = some mk → ∀ g, Q p.name (mk g).rounds := by
  intro p _ mk e
  rw [h p.place] at e
  cases e

theorem wK_pure {Z : Pub} {G : Ground} {spots : List Spot} {L13 L14 : Lot}
    (hp : p4Pure Z = [L13, L14])
    (k9 : ∀ p ∈ spots, ∀ mk, (k9Ninth Z).batch G p.place = some mk →
      ∀ g, Q p.name (mk g).rounds)
    (n13 : ∀ a, L13.batch G a = none) (n14 : ∀ a, L14.batch G a = none) :
    ∀ L ∈ onlineFirstChainBlockTables Z, ∀ p ∈ spots, ∀ mk, L.batch G p.place = some mk →
      ∀ g, Q p.name (mk g).rounds :=
  lots_all hp (wK_none fun _ => rfl) (wK_none fun _ => rfl) (wK_none fun _ => rfl)
    (wK_none fun _ => rfl) (wK_none fun _ => rfl) (wK_none fun _ => rfl) (wK_none fun _ => rfl)
    k9 (wK_none fun _ => rfl) (wK_none fun _ => rfl) (wK_none fun _ => rfl)
    (wK_none fun _ => rfl) (wK_none fun _ => rfl) (wK_none n13) (wK_none n14)

theorem wL_pure (o : SecondHashFunctionArgument) {Z : Pub} {B : PureBase} (h₁ : B.spots = spotsW)
    (w : ∀ L ∈ onlineFirstChainBlockTables Z, ∀ b ∈ L.blocks B.G₀, Q (nameW b.place) b.rounds) :
    ∀ L ∈ (pureSeat o Z).lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Q p.name b.rounds :=
  rows_by_place (T := pureSeat o Z) h₁ w

/-- **Q at every block of the first chain's flat list, at `pureSeat o Z`.** -/
theorem good_at_pure (hQ : ∀ n, Q n []) (o : SecondHashFunctionArgument) (Z : Pub) (B : PureBase)
    (h₁ : B.spots = spotsW) (h₂ : B.shape = shapeW) (hs : subsOf Z = subsW)
    (hB : B.all = (onlineFirstChainBlockTables Z).map fun L => (L, L.blocks B.G₀))
    (hR : List.Forall₂ (RowAt B.G₀) (onlineFirstChainBlockTables Z) wsW)
    (w : ∀ L ∈ onlineFirstChainBlockTables Z, ∀ b ∈ L.blocks B.G₀, Q (nameW b.place) b.rounds)
    (wK : ∀ L ∈ onlineFirstChainBlockTables Z, ∀ p ∈ B.spots, ∀ mk, L.batch B.G₀ p.place = some mk →
      ∀ g, Q p.name (mk g).rounds)
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    (h₄ : (partsAt (pureSeat o Z) B).base = .ok base)
    (h₅ : chainBy Z base (partsAt (pureSeat o Z) B).frames (partsAt (pureSeat o Z) B).road =
      .ok c) : ∀ b ∈ c.blocksInOrder, Good Q b := by
  have hf : ∀ x ∈ framesSk B.shape ((pureSeat o Z).lots.map (lotSk B.G₀)), x.2.nRounds = 0 := by
    rw [h₂]
    show ∀ x ∈ framesSk shapeW ((onlineFirstChainBlockTables Z).map (lotSk B.G₀)), x.2.nRounds = 0
    rw [frames_of_rows (rows_join B.G₀ hR)]
    intro x hx
    exact eq_of_beq (List.all_eq_true.1 frames_full x hx)
  exact back_good (pureSeat o Z) B hQ Z hB (wL_pure o h₁ w)
    (hK_of_spots (T := pureSeat o Z) h₁ wK) (fun p hp => ⟨p, hp, rfl⟩) (asked_are_spots h₁ hs) hf
    h₄ h₅

end

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lots_all
#print axioms ProofFile.Sk.Full.wK_none
#print axioms ProofFile.Sk.Full.wK_pure
#print axioms ProofFile.Sk.Full.wL_pure
#print axioms ProofFile.Sk.Full.good_at_pure
