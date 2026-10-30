-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WNumbersAtHead.lean: where the two K1 members of the last chain's test sit, by K1's own
reckoning, under the head: what the Script's tie at a member (tie_k1_first) and the record's seats
(seats_of_narrow) have to meet on.

  seats_written    the index-mask message and W's at the written plan: kernel evaluations
  seats_at_head    seatAtMember at numbers 2 and 356 under the head
  narrow_shapes    the closed shape's three members against the written sendings: kernel evaluations
  ells_written     the two written senders' codes' lengths: kernel evaluations

Limits.
- The full size and the format's second hash function alone.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WSeatsNarrow
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K1.Seated
import AtFullSide.K12.HeldAtHeadW
import Johnson.Desc.K1.Law.WordsAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc.K1 (parGF parWF)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open ProofFile.Honest.K12.AtFile (narrowW)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **By K1's own reckoning at the written plan.** An evaluation in Lean's kernel. -/
theorem seats_written :
    VerifiableInference.Desc.K1.seatOfMsg parGF (treesTold toldFull 2) (parGF.sent.size - 1) =
      (1, 0) ∧
    VerifiableInference.Desc.K1.seatOfMsg parWF (treesTold toldFull 356) 0 = (82, 0) := by
  decide +kernel

/-- **The closed shape's members against the written sendings.** An evaluation in Lean's kernel. -/
theorem narrow_shapes :
    (narrowW.st.oracles[4]?).map (·.shape) =
      some (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)) ∧
    (narrowW.st.oracles[197]?).map (·.shape) = some (Johnson.Prover.Send.shapeAt parWF 0) ∧
    (VerifiableInference.Desc.K1.realSized.any fun q =>
      decide ((narrowW.st.oracles[199]?).map (·.shape) =
        some ((Desc.K14.withOmega q.1.shape).getD 0 default).shape)) = true := by
  decide +kernel

/-- **The two written senders' codes' lengths, where their tables have a row.** An evaluation in Lean's
kernel. -/
theorem ells_written :
    (0 < (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).maskRows →
      (parGF.codes.mask.getD (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).maskCode
        default).ell =
      2 ^ (parGF.codes.mask.getD (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).maskCode
        default).logEll) ∧
    (0 < (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).mainRows →
      (parGF.codes.base.getD (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).code
        default).ell =
      2 ^ (parGF.codes.base.getD (Johnson.Prover.Send.shapeAt parGF (parGF.sent.size - 1)).code
        default).logEll) ∧
    (0 < (Johnson.Prover.Send.shapeAt parWF 0).mainRows →
      (parWF.codes.base.getD (Johnson.Prover.Send.shapeAt parWF 0).code default).ell =
      2 ^ (parWF.codes.base.getD (Johnson.Prover.Send.shapeAt parWF 0).code default).logEll) ∧
    (0 < (Johnson.Prover.Send.shapeAt parWF 0).maskRows →
      (parWF.codes.mask.getD (Johnson.Prover.Send.shapeAt parWF 0).maskCode default).ell =
      2 ^ (parWF.codes.mask.getD (Johnson.Prover.Send.shapeAt parWF 0).maskCode default).logEll) := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase}
  {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}

/-- **At the head's chain the two members' seats.** -/
theorem seats_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ProofFile.Honest.K1.seatAtMember cF.blocksInOrder 2 parGF (parGF.sent.size - 1) = (1, 0) ∧
    ProofFile.Honest.K1.seatAtMember cF.blocksInOrder 356 parWF 0 = (82, 0) := by
  unfold ProofFile.Honest.K1.seatAtMember
  rw [ProofFile.Honest.K2.Law.treesTo_at_head h O, ProofFile.Honest.K2.Law.treesTo_at_head h O]
  exact seats_written

end AtFullSide.K12

#print axioms AtFullSide.K12.seats_written
#print axioms AtFullSide.K12.narrow_shapes
#print axioms AtFullSide.K12.ells_written
#print axioms AtFullSide.K12.seats_at_head
