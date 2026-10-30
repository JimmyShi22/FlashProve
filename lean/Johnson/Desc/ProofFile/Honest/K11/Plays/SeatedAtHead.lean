-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatedAtHead.lean: the proofs of `K11SeatedAtHead` and
`ExchangeAtHead` (Honest/K11/Plays/SeatedAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How: an assembly, field by field. member · head · link · hears · lay: `headMergeAtFull`
(Johnson/Desc/K11/Exchange/AtFull.lean) · colBits: `layAtHead` (TiesAtHead.lean of this folder) ·
rowsFit: `rowsFitAtHead` (Johnson/Desc/K11/Exchange/RowsFit.lean) · steps: `stepsOfHalfCoins`;
merged · wo: `mergedWo_at_head` (SeatFields.lean of this folder) · front: `frontS_at_head`
(FrontSAtHead.lean) and `frontClaim_at_head` (FrontClaim.lean) · pubTest: `pubTest_at_head`
(FrontAtHead.lean) · ties: `tiesAtHead` (TiesAtHead.lean). The second: `headMergeShareS`
(ShareS.lean of this folder) at the first.

Limits. Those of the statements. Through its imports it rests on nine evaluations in Lean's kernel
(`decide +kernel`) in files that the library's tree does not hold (seven in this kind's own, two in
the lookups' authors'), beside the library's own. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatedAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.TiesAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontClaim
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatFields
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareS
import Johnson.Desc.K11.Exchange.RowsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull rowsFitAtHead)

/-- **The kind's structure, whole, at the head's thread.** -/
theorem k11Seated_at_head : K11SeatedAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    weights c₀ hB hb hhalf hM hQ
  obtain ⟨Bs', Lk, name, hB', h1, h2, h3, h4, h5, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain ⟨hmg, hwo⟩ := mergedWo_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w
  have hst := stepsOfHalfCoins _ _ _ _ _ _ _ _ _ _ _ name IM.k11Place c₀ hhalf
  have hpt := pubTest_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w
  have hti := tiesAtHead Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w Bs weights _ hB hM hQ
  refine ⟨name, Lk, ?_⟩
  exact
    { member := h5
      steps := hst
      merged := hmg
      wo := hwo
      head := fun _ _ => h2
      link := fun _ _ => h1
      hears := h4
      lay := fun _ _ => h3
      colBits := fun _ _ => (layAtHead h hB).1
      rowsFit := fun _ _ => rowsFitAtHead Z D r Zp Np cF x h
      front := fun k s m E hT => by
        obtain ⟨a, claim, x0, b9, ha, hcl, hx, hb9, hLR, hfil, hun⟩ :=
          frontS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
            Kp w k s m E Bs hB hT
        exact ⟨a, claim, x0, b9, ha, hcl, hx, hb9, hLR, hfil, hun,
          frontClaim_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
            Rd Kp w k s m E Bs a claim hB hb hT ha hcl⟩
      pubTest := hpt
      ties := hti }

/-- **The frame's debt on the exchange at 346, at the two items that the member opens.** -/
theorem exchange_at_head : ExchangeAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    weights c₀ hB hb hhalf hM hQ
  obtain ⟨name, Lk, hK⟩ := k11Seated_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Bs weights c₀ hB hb hhalf hM hQ
  exact headMergeShareS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.k11Seated_at_head
#print axioms ProofFile.Honest.K11.exchange_at_head
