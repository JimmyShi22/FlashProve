-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/ShOneDecAll.lean: "THE FIRST TABLE's DECODER IS MADE OF THE SHARED CHAIN's"
(Sh.OneDec, Johnson/Desc/K14/Law/SharedConstByMake.lean) AT THE SHARED TABLE's CONSTANT WITH ALL ITS
OPEN LETTERS CLOSED (Sh.openAll, Johnson/Desc/K14/Law/SharedConstFirstAt.lean). A corollary: one
call of oneDec_at (Johnson/Loose/H2K12/OneDecAt.lean), which has it at Sh.openAt₀ at every filling
of the other letters.

  Sh.oneDec_all        OneDec (planAt …) (openAll h e) (seatF …).start₂
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstFirstAt
import Johnson.Loose.H2K12.OneDecAt

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


namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **OneDec at the closed letters.** -/
theorem oneDec_all (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp
    Np (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    OneDec (planAt Zp Np (seatF o Zp Np (Desc.K14.Law.secondAt Zp Np) cF)) (openAll h e) (seatF o Zp
        Np (Desc.K14.Law.secondAt Zp Np) cF).start₂ :=
  H2K12.oneDec_at h (Desc.K14.Law.secondAt Zp Np) (fun _ _ => 0) (matN (frS.toDecR frZ 402653181)
      numsFull)
    (P5J.At.N Zp cF) P5J.At.links (e ▸ P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.oneDec_all
