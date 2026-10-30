-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameArmSealed.lean:
THE ARM OF THE KIND "frame" WITH THE SEAL'S TIE LAID IN: seal_tie_atAll
(Johnson/Desc/AtSeats/Seal357AtAll.lean) is handed to frame_arm
(FrameArm.lean) in the place of the premise SealFrom h L. Here Lean takes the one for the
other.

  seal_from_atAll   seal_tie_atAll h L q₁ q₂ q₃ is a SealFrom h L: the letters of the two files
                    (At.N Zp cF and (dmOf h).N; mgAtAll h and mgAll (dmOf h) mgBase; fullLinks and
                    linksFull; At.ps and flatPlacesOf linksFull true; the two spellings of the
                    frame of the data) are one by unfolding
  frame_arm_sealed  h.Kind L KindName.frame from FramePub h, the fact kn on reachable states and
                    h.K9Cond L

Limits. FrameArm.lean's. No premise is shown here. Of the kind's 77 places the tie is shown at 51;
at 25 it is a part of h.K9Cond L; at 1 it is seal_tie_atAll, called here. A member of the head is
proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameArm
import Johnson.Desc.AtSeats.Seal357AtAll

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

/-- **The tie of the seal (seal_tie_atAll) ends in the form that the arm takes.** -/
theorem seal_from_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) : SealFrom h L :=
  VerifiableInference.Desc.K13.Law.seal_tie_atAll h L q₁ q₂ q₃

/-- **THE ARM OF THE KIND "frame", THE SEAL'S TIE LAID IN.** -/
theorem frame_arm_sealed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FramePub h)
    (kn : ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
      KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2))
    (C9 : h.K9Cond L) : h.Kind L KindName.frame :=
  frame_arm h L q₁ q₂ q₃ W kn (seal_from_atAll h L q₁ q₂ q₃) C9

end

end P1L20

#print axioms P1L20.seal_from_atAll
#print axioms P1L20.frame_arm_sealed
