-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstOpenAllFree.lean: THE TWO FILLINGS OF THE SHARED TABLE's OPEN
LETTERS AT THE CLOSED CONSTANT ARE ONE: Sh.openAll h e = h.toAtMg.shOpen h.𝔇. One theorem.

WHY. Our closed theorems stand at O := Sh.openAll h e
(Johnson/Desc/K14/Law/SharedConstFirstAt.lean); the filling at which the proof file's top is taken,
h.free, reads the same letters through h.toAtMg.shOpen h.𝔇 (Johnson/P5J/FreeShared.lean). Until the
two are one, the closed theorems pay no field there.
HOW. Sh.openAll_is (Johnson/Desc/K14/Law/SharedConstOpenAllIs.lean: by rfl) and P5J.shOpen_is
(Johnson/P5J/FreeBridge.lean: the first table's meaning by mgAt_is_mq, a theorem in the
goals' scope; the reader of samples by a cast over e) end at one and the same term.
What is not claimed. It is an equation of letters: it pays no law. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAllIs
import Johnson.P5J.FreeBridge

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

/-- **The two fillings are one.** -/
theorem openAll_is_free (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF
    o Zp Np (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    openAll h e = h.toAtMg.shOpen h.𝔇 :=
  (openAll_is h e).trans (congrArg (fun F => openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF
    h.plan.shape (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z) F)
    (P5J.shFirst_is h.toAtMg h.𝔇 e).symm)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.openAll_is_free
