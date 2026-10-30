-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFarPaid.lean: THE FIVE CLOSED TESTS THAT BUY THE FOLD FACT hfar AT A
PROOF FILE's SEAT (Sh.testsFar, Johnson/Desc/K14/Law/SharedConstFar.lean) ACCEPT IN THE GOALS'
    SCOPE,
AT THE WRITTEN LIST OF THE FIRST CHAIN's PLACES (LFull). A composition: no proof of its own.

  Sh.written_t₁_paid   Sh.WrittenT1Owed (Johnson/Desc/K14/Law/SharedConstFarAt.lean):
                       t1_written
  Sh.testsFar_in_scope **TestsFar o Z N B' cF LFull**
HOW. far_written (Johnson/Second/Seam/FarWritten.lean: the tests by Lean's kernel at
the written values) at D := Z.D · its five equations on Z by P5T.far_ties_in_scope
(Johnson/P5T/WrittenAtScope.lean) · the three tenants in its terms by Sh.tenants_in_scope.
IN FRONT: the scope · what the road, the maker and "the written data are laid" return · one pin of
    the
door (madePinnedAt) · the equations on the public value (Written Z x).
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstFarAt
import Johnson.Desc.K14.Law.SharedConstFar
import Johnson.Second.Seam.FarWritten
import Johnson.P5T.WrittenAtScope
import Johnson.HB.LLHARD.TreesWritten

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

open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K13.Law (LFull)

namespace Sh

/-- The closed fact that was owed. -/
theorem written_t₁_paid : WrittenT1Owed := Johnson.G.t1_written

variable {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Z : ProofFile.Pub}
  {x : LinSized}

/-- **The five closed tests accept in scope.** -/
theorem testsFar_in_scope (hS : VerifierAndGoals.InScope S = true)
    (hZ : ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made =
        true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) (N : H2U.Places4)
    (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (seatF o Z N B' cF))
    (hx : realSized = some (x, codesFull2)) (hW : Written Z x) :
    TestsFar o Z N B' cF LFull := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := P5T.far_ties_in_scope hS hZ hy hL
  obtain ⟨ht, hpl, hlen, _, _, _, _⟩ := Second.Seam.far_written (Z := Z) (D := Z.D) h1 h2 h3 h4 h5 x
      hx
  have hm : ∀ m : Msg2, P5T.foundLaterB Z Z.D (tenantSh (t₁ (planAt Z N (seatF o Z N B' cF)))
      (layU (planAt Z N (seatF o Z N B' cF))) (layO (planAt Z N (seatF o Z N B' cF))) m) = true :=
          by
    intro m
    rw [tenants_in_scope hS hL hF hW written_t₁_paid N m]
    refine ht _ ?_
    cases m <;> simp [Second.Seam.tenantsAt, Second.Seam.layUAt, Second.Seam.layOAt]
  simp only [TestsFar, testsFar, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨hm .oU, hm .oOmega, hm .oSp, hpl, hlen⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.written_t₁_paid
#print axioms Desc.K14.Law.Sh.testsFar_in_scope
