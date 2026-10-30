-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ClaimsNIs.lean: the proofs of the seven statements of
Honest/K11/Plays/ClaimsNStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The first three: by unfolding: the lookups' authors' full text of a lookup lays its field zk as
`keyPtsAt`'s. The fourth: under the head the chain's letter is what the library's maker of the chain
returns (`P5J.LaidAt.chain`); the kind's link is 24 (`headMergeAtFull`); the chain's places are the
written list (`P5J.At.places_paid`), in which piece 3 (K3) and piece 4 (K6) of link 24 stand first
at numbers 340 and 341; so the rounds found by place are those in front of these members (the three
lemmas of Honest/K11/InFront.lean); then the third. The three carried ones: the fourth rewrites the
new text into the elder one; then the elder lemma.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimsNStatement
import Johnson.Desc.ProofFile.Honest.K11.InFront
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontClaim
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatedAtHead
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.P5J.ChainFree
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)

/-- **The head's key points are the general text at 24 and 340.** -/
theorem keysAtLinkIsHead : KeysAtLinkIsHead := fun _ => rfl

/-- **The layers' key points are the general text at 2 g and 28 g + 3.** -/
theorem keysAtLinkIsLayers : KeysAtLinkIsLayers := fun _ _ _ _ _ _ => rfl

/-- **The elder claims are the general text at 24, 340 and 341.** -/
theorem headClaimsNIs : HeadClaimsNIs := fun _ _ _ => rfl

/-- **Under the head the text by place is the elder.** -/
theorem headClaimsByPlace_at_head : HeadClaimsByPlaceAtHead := by
  intro Z D r Zp Np cF x Bs h hB
  obtain ⟨Bs', _, _, hB', _, _, _, _, hfl, hlink⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  have hlen : 346 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hfl).1
  have hps : cF.blocksInOrder.map (·.place) = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have r0 := roundsInFrontIs _ _ cF.blocksInOrder ⟨1, some 24, 3, .K3⟩ 340
    (by rw [hps]; exact callsPlace_at_full) (by omega)
  have r1 := roundsInFrontIs _ _ cF.blocksInOrder ⟨1, some 24, 4, .K6⟩ 341
    (by rw [hps]; exact headOwnPlace_at_full) (by omega)
  unfold headClaimsByPlace
  rw [h.laid.chain]
  simp only [hlink, r0, r1]
  exact (headClaimsNIs cF Zp Bs'.G₀).symm

/-- **The last clause of the field front, at the text by place.** -/
theorem frontClaimByPlace_at_head : FrontClaimByPlaceAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    a claim hB
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x Bs h hB]
  exact frontClaim_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w k s m E Bs a claim hB

/-- **The structure, at the text by place.** -/
theorem k11SeatedByPlace_at_head : K11SeatedByPlaceAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs weights
    c₀ hB
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x Bs h hB]
  exact k11Seated_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w Bs weights c₀ hB

/-- **The kind's share of the exchange, at the text by place.** -/
theorem exchangeByPlace_at_head : ExchangeByPlaceAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs weights
    c₀ hB
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x Bs h hB]
  exact exchange_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w Bs weights c₀ hB

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.keysAtLinkIsHead
#print axioms ProofFile.Honest.K11.keysAtLinkIsLayers
#print axioms ProofFile.Honest.K11.headClaimsNIs
#print axioms ProofFile.Honest.K11.headClaimsByPlace_at_head
#print axioms ProofFile.Honest.K11.frontClaimByPlace_at_head
#print axioms ProofFile.Honest.K11.k11SeatedByPlace_at_head
#print axioms ProofFile.Honest.K11.exchangeByPlace_at_head
