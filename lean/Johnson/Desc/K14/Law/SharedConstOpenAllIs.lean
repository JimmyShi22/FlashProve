-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstOpenAllIs.lean: THE SHARED TABLE's OPEN LETTERS AT THE CLOSED
CONSTANT, Sh.openAll h e, WRITTEN OUT: Sh.openAt AT THE FIVE OF THE FIRST TABLE, EACH BY ITS OWN
TERM. One theorem, by rfl.

WHY. Our closed theorems stand at O := Sh.openAll h e
(Johnson/Desc/K14/Law/SharedConstFirstAt.lean). Another file's filling of the same letters
(h.toAtMg.shOpen h.𝔇, FreeShared.lean) is shown in FreeBridge.lean (shOpen_is) to be Sh.openAt at
five written terms. This is one half of the equation of the two: Sh.openAll h e is Sh.openAt
at those very five, with the first table's meaning spelled mgAt h.toAtMg h.𝔇 (P5J.mgAtAll_is: rfl).
What is not claimed. The other half. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstFirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

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

open VerifiableInference.OnPublicFiles (kcReq)

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **Sh.openAll, written out.** -/
theorem openAll_is (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp
    Np (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    openAll h e = openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF h.plan.shape
      (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)
      { N₁ := P5J.At.N Zp cF, links := P5J.At.links, Mg₁ := P5J.mgAt h.toAtMg h.𝔇,
        smp₁ := e ▸ P5J.At.smp Zp, ms₁ := P5J.At.ms Zp Z.lay } := rfl

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.openAll_is
