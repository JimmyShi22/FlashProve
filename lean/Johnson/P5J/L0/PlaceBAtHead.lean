-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/PlaceBAtHead.lean: A JOINING; nothing is proved anew. THE FIELD placeB OF `LLT25.PlanCore₃`
(one of the fourteen that PlanCore.lean leaves by name) IS A THEOREM AT THE HEAD:
`H2K12.placeB_at_FL` (Johnson/Loose/H2K12/PlaceBAtW.lean) asks five of the fields that
`planPaid₃_at_head` (PlanAtHead.lean) pays: closed, ownMask, free0, dataIs, stretch.

  **`placeB_at_head`**: from the head, at the dB :: dt that the stretch is: the field placeB in its own
    text at `CoreJ`'s letters.
  `placeB_is_field`: Lean holds that text against the field (a `CoreJ` with this field laid in).
Limits. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). A test's accept is worth what the laws make of it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.L0.PlanAtHead
import Johnson.Loose.H2K12.PlaceBAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J.L0
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)
open LLT25

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The field placeB, at the head.** -/
theorem placeB_at_head (h : AtMg o Z D r Zp Np cF) (dB : RDT) (dt : List RDT)
    (hs : StretchJ o D Zp Np cF dB dt) :
    PlaceB (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).lastChainFirstTreeNumber)
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W)
      (VerifiableInference.Desc.numAt (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂ 2)
      (baseTwoAt (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF) (D.at frS.P.T.a) (c0 Zp) (c1 Np))
      dB dt = true := by
  have P := planPaid₃_at_head h ⟨default, 0, 0, 0, 0, default, default⟩ dB dt hs
  obtain ⟨ch, b₁, b₂, T, hcl⟩ := P.closed
  exact H2K12.placeB_at_FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF "proof file" (D.at frS.P.T.a)
    H2K.Member.rWFull ch b₁ b₂ T dB dt hcl P.ownMask P.free0 h.dataL hs

/-- Lean holds that text against the field. -/
theorem placeB_is_field (h : AtMg o Z D r Zp Np cF) (J : ShSeven) (dB : RDT) (dt : List RDT)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (hs : StretchJ o D Zp Np cF dB dt)
    (C : CoreJ o Z D Zp Np cF J dB dt Ld) : CoreJ o Z D Zp Np cF J dB dt Ld :=
  { C with placeB := placeB_at_head h dB dt hs }

end P5J.L0

#print axioms P5J.L0.placeB_at_head
#print axioms P5J.L0.placeB_is_field
