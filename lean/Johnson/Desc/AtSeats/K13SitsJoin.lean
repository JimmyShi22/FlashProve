-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.IMR.BackSeat
import Johnson.Desc.K13.Law.LotSits
/-
A JOINING OVER THE FILES BELOW IT: K13_sits AT THE PROOF FILE: the entries of the pure description's first chain at «M:3», «M:4» and the seal say yes
only where the blocks of which kind K13's laws speak say the same yes, at the plan's numbers whereOf Z. From the
seats (Johnson/IMR/BackSeat.lean: back_of · seal_of · back_numbers: THE ENTRY IS LaidAlone OVER A MEMBER OF K13's LOT) and the kind's own half
(Johnson/Desc/K13/Law/LotSits.lean: lot_under · lot4_under · lotEnd_under: A MEMBER OF THE LOT IS UnderR THE LAW's BLOCK). NO EQUATION ON THE MEMBER
IS SPENT: membership alone. NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S endAsks)
open ProofFile (Cl)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The flat list's turn of a block's test on the plan touches neither rounds nor decision. -/
theorem planOk_underR (b : Block S Cl) (p : Bool) : Block.UnderR { b with planOk := p } b :=
  ⟨rfl, fun _ _ _ _ h => h⟩

/-- **K13_sits at «M:3».** -/
theorem k13_sits_M3 (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ b, c.back[2]? = some b ∧ b.place = ⟨1, none, 3, .K13⟩ ∧ b.UnderR (atM3 (whereOf Z)) := by
  obtain ⟨_, _, ⟨b, b', hb, hm, _, hl⟩, _⟩ := IM.back_of O
  exact ⟨b, hb, IM.alone_place hl, (IM.alone_underR hl).trans (lot_under Z _ b' hm)⟩

/-- **K13_sits at «M:4».** msg: the message that the shape gives. -/
theorem k13_sits_M4 (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ b msg, c.back[3]? = some b ∧ b.place = ⟨1, none, 4, .K1⟩ ∧
      linMessageW Z.first.lin = some msg ∧
      b.UnderR (atM4 (whereOf Z) (K1.sendAtS
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))) := by
  obtain ⟨_, _, _, b, b', w, hb, hm, _, _, hl⟩ := IM.back_of O
  obtain ⟨msg, hmsg, hu⟩ := lot4_under Z _ b' hm
  exact ⟨b, msg, hb, IM.alone_place hl, hmsg, (IM.alone_underR hl).trans hu⟩

/-- **At the seal, under the premise that the plan's last spot is the seal's.** -/
theorem k13_sits_seal (O : IM.Open o pol lay KL F Z Bs base c A B) (hz : IM.SealLast Bs.spots) :
    c.last.place = ⟨1, none, 5, .frame⟩ ∧
      c.last.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks) := by
  obtain ⟨b', hm, _, hl⟩ := IM.seal_of O hz
  exact ⟨IM.alone_place hl, (IM.alone_underR hl).trans (lotEnd_under Z _ b' hm)⟩

/-- **The same of the description's flat list of blocks, in scope**: its entries number 355 and 356. -/
theorem k13_sits_flat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (∃ e, c.blocksInOrder[355]? = some e ∧ e.place = ⟨1, none, 3, .K13⟩ ∧ e.UnderR (atM3 (whereOf Z))) ∧
    (∃ e msg, c.blocksInOrder[356]? = some e ∧ e.place = ⟨1, none, 4, .K1⟩ ∧
      linMessageW Z.first.lin = some msg ∧
      e.UnderR (atM4 (whereOf Z) (K1.sendAtS
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)))) := by
  obtain ⟨b, hb, hp, hu⟩ := k13_sits_M3 O
  obtain ⟨b4, msg, hb4, hp4, hm, hu4⟩ := k13_sits_M4 O
  have hn := (IM.back_numbers hS hR O).1
  exact ⟨⟨_, hn 2 b hb, hp, (planOk_underR b _).trans hu⟩,
    ⟨_, msg, hn 3 b4 hb4, hp4, hm, (planOk_underR b4 _).trans hu4⟩⟩

end VerifiableInference.Desc.K13.Law
