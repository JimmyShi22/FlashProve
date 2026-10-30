-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1L20R/FrameOfPub.lean:
THE KIND "frame" AT THE SEATED TERM FROM TWO FACTS ON PUBLIC DATA AND K9's CONDITION
ALONE: both other files' shares are laid in: the tie of the seal (seal_tie_atAll, by
FrameArmSealed.lean) and the fact kn on reachable states (kn_atAll, FrameKnAll.lean).

  frame_of_pub      h.Kind L KindName.frame from FramePub h and h.K9Cond L

Limits. FrameArm.lean's. FramePub h (stands24: one decidable fact; fence: a test with code; both on
public data) and h.K9Cond L are premises; none is shown here. Of the kind's 77 places the tie is
shown at 51; at 25 it is a part of h.K9Cond L; at 1 it is seal_tie_atAll, called through
FrameArmSealed.lean. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library
AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameArmSealed
import Johnson.P1L20R.FrameKnAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf fenceFit)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE KIND "frame" FROM TWO FACTS ON PUBLIC DATA AND K9's CONDITION.** -/
theorem frame_of_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FramePub h) (C9 : h.K9Cond L) : h.Kind L KindName.frame :=
  frame_arm_sealed h L q₁ q₂ q₃ W (kn_atAll h) C9

end

end P1L20

#print axioms P1L20.frame_of_pub
