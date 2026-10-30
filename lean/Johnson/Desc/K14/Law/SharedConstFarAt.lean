-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFarAt.lean: IN THE GOALS' SCOPE THE THREE TENANTS OF THE SHARED
    CHAIN's
MESSAGES, AS THE SHARED TABLE's CONSTANT NAMES THEM AT A PROOF FILE's SEAT, ARE WRITTEN VALUES: the
shared chain's first tree has the written data's number (83: owed), and the two sendings' layouts of
    trees are made
at the written codes and the typed shape. So the three closed tests on the tenants (Sh.testsFar,
Johnson/Desc/K14/Law/SharedConstFar.lean) can be paid by an evaluation at written values.

  Sh.WrittenT1Owed     OWED, a closed fact, as a Prop by def: writtenPFull.t₁ = 83
  Sh.t₁_in_scope       Sh.t₁ (planAt Z N F) = writtenPFull.t₁, at whatever F the verifier makes,
                       where the written data are laid
  Sh.lay_in_scope      Sh.sentU, Sh.layU, Sh.layO at planAt: at codesFull2 and x.shape
  Sh.tenants_in_scope the tenant of each of the three messages, in those terms
HOW. Calls: counts_of_planOk (Johnson/Desc/Sound/SeamDesc.lean) · depth_in_scope
(Johnson/Desc/K12/Coin/GameAtFieldScope.lean) · Sh.laid_at · the equations on the public value
(Written).
What is not claimed. That the tests accept. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstScope
import Johnson.Desc.Sound.SeamDesc
import Johnson.Desc.K12.Coin.GameAtFieldScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.G (codesFull2 writtenPFull)
open VerifiableInference.Desc.K1 (realSized)

namespace Sh

/-- OWED: a closed fact: the written data's number of the first chain's trees. -/
def WrittenT1Owed : Prop := writtenPFull.t₁ = 83

/-- **The shared chain's first tree has the written data's number.** -/
theorem t₁_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    (hS : VerifierAndGoals.InScope S = true) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r))
    {F : FileDescription ProofFile.Inst} (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F) (Z : ProofFile.Pub)
    (N : H2U.Places4) : t₁ (planAt Z N F) = writtenPFull.t₁ := by
  obtain ⟨hp, _, hpin⟩ := laid_at hL hF
  have hD := (VerifiableInference.Desc.K12.Coin.depth_in_scope F S hS hpin).2
  exact (counts_of_planOk F "proof file" writtenPFull hp hD).1

/-- **The two sendings and their layouts of trees, at the written codes and the typed shape.** -/
theorem lay_in_scope {Xi : Type} {Z : ProofFile.Pub} {x : LinSized} (h : Written Z x) (N : H2U.Places4)
    (G : FileDescription Xi) :
    sentU (planAt Z N G) = (withU x.shape).getD #[] ∧
      layU (planAt Z N G) = (layTrees codesFull2 ((withU x.shape).getD #[])).getD default ∧
      layO (planAt Z N G) = (layTrees codesFull2 (withOmega x.shape)).getD default := by
  have eS : (planAt Z N G).Q.S = x.shape := h.shape
  have eC : (planAt Z N G).Q.codes = codesFull2 := h.codes
  refine ⟨?_, ?_, ?_⟩
  · unfold sentU
    rw [eS]
  · unfold layU sentU
    rw [eS, eC]
  · unfold layO
    rw [eS, eC]

/-- **The three tenants, in written terms.** -/
theorem tenants_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F) {Z : ProofFile.Pub} {x : LinSized}
    (h : Written Z x) (h83 : WrittenT1Owed) (N : H2U.Places4) (m : Msg2) :
    tenantSh (t₁ (planAt Z N F)) (layU (planAt Z N F)) (layO (planAt Z N F)) m =
      tenantSh 83 ((layTrees codesFull2 ((withU x.shape).getD #[])).getD default)
        ((layTrees codesFull2 (withOmega x.shape)).getD default) m := by
  rw [t₁_in_scope hS hL hF Z N, (lay_in_scope h N F).2.1, (lay_in_scope h N F).2.2, h83]

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.t₁_in_scope
#print axioms Desc.K14.Law.Sh.lay_in_scope
#print axioms Desc.K14.Law.Sh.tenants_in_scope
