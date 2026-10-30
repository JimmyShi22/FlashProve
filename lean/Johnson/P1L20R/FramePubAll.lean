-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FramePubAll.lean:
a payment beneath the frame's frozen condition: FramePub h (FrameArm.lean) HOLDS UNDER
THE BUNDLE OF HYPOTHESES P5J.AtMgA ALONE; so the share of the kind "frame" on the first chain
follows from the batching kind's condition alone.

  fence_atAll       FramePub.fence: AtMg.fence (Johnson/P5T/FenceAtMg.lean), in FramePub's
                    letters
  framePub_atAll    FramePub h: with stands24_atAll (Stands24AtAll.lean)
  frame_of_k9       h.Kind L KindName.frame from h.K9Cond L (and the three lists' first members)

Limits. AtMg.fence rests on AtMg.pins: two of the verifier's entry tests on the public files
(madeRow, cutRow) accept at the bundle's own values; that follows from the bundle's field laid.asks
ONLY FROM the verifier's list of entry tests OF THIRTEEN ROWS ON (GLOSSARY.md; this library's list
has fourteen); at the earlier list of eight rows the lemma does not exist. Of the kind's 77 places
the tie is shown at 51; at 1 it is seal_tie_atAll, called; at 25 it is a part of the
premise h.K9Cond L, which k09_cond_of_head (Johnson/P5J/K09CondHead.lean) gives from the bundle and
the three lists' first members. A member of AtMgA is proved at storedPublicFiles and zGap alone (at secondHashFunction; side
library AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameOfPub
import Johnson.P1L20R.Stands24AtAll
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf fenceFit)
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- fenceFit accepts at the bundle's own numbers. -/
theorem fence_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true :=
  h.toAtMg.fence

/-- **The frame's two facts on public data hold under the bundle.** -/
theorem framePub_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : FramePub h :=
  ⟨stands24_atAll h, fence_atAll h⟩

/-- **The kind "frame" from the batching kind's condition**: 51 ties shown, 1 called, 25 out of
h.K9Cond L. -/
theorem frame_of_k9 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (C9 : h.K9Cond L) : h.Kind L KindName.frame :=
  frame_of_pub h L q₁ q₂ q₃ (framePub_atAll h) C9

end

end P1L20

#print axioms P1L20.fence_atAll
#print axioms P1L20.framePub_atAll
#print axioms P1L20.frame_of_k9
