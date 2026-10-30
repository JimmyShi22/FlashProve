-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13SitsJoin
import Johnson.IMR.SealSeat
import Johnson.Desc.ProofFile.Law.HeadSeal
/-
A JOINING OVER THE FILES BELOW IT: K13_sits AT THE SEAL, WITH NO PREMISE LEFT: the first chain's last block says yes only where the chain's end of
which the law speaks says the same yes. From k13_sits_seal | k13_sits_flat (Johnson/Desc/AtSeats/K13SitsJoin.lean),
seal_last (Johnson/IMR/SealSeat.lean: SealLast under the one closed sentence HeadSeal) and ProofFile.head_seal (that sentence, proved). NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (S endAsks)
open ProofFile (Cl)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K13_sits at the seal**: at every opening, at every o. -/
theorem k13_sits_sealed (O : IM.Open o pol lay KL F Z Bs base c A B) :
    c.last.place = ⟨1, none, 5, .frame⟩ ∧
      c.last.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks) :=
  k13_sits_seal O (IM.seal_last ProofFile.head_seal O)

/-- **And of the flat list's entry 357, in scope.** -/
theorem k13_sits_flat357 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ e, c.blocksInOrder[357]? = some e ∧ e.place = ⟨1, none, 5, .frame⟩ ∧
      e.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks) := by
  obtain ⟨hp, hu⟩ := k13_sits_sealed O
  exact ⟨_, (IM.back_numbers hS hR O).2, hp, (planOk_underR c.last _).trans hu⟩

end VerifiableInference.Desc.K13.Law
