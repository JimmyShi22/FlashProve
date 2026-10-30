-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameArm.lean:
the share of the kind "frame" on the first chain, in the form in which a kind's law is
counted under the bundle of hypotheses P5J.AtMgA: h.Kind L KindName.frame (Johnson/P5J/RowsAtAll.lean).

WHAT IS SHOWN, AND WHAT IS HANDED IN. The kind has 77 places on the first chain.
  51 places (the front, 25 "laid", 25 "cleared"): the tie is SHOWN, from FramePub h and kn.
  25 places (behind the batching): the tie is ASSUMED: it is a part of the premise h.K9Cond L, the
     batching kind's condition, whose fields hold this very sub-protocol's law and ties, link by
     link; k09_behindTies (Johnson/P5J/K09Behind.lean) only spells them as TiedAtR.
     k09_cond_of_head (Johnson/P5J/K09CondHead.lean) ends in K9Cond, from the bundle and the three
     lists' first members.
   1 place (357, the seal): the tie is HANDED IN as SealFrom h L.

  FramePub          two facts on public data:
                    stands24: the code switch behind the last segment is not of the sort "output
                    head"; fence: fenceFit accepts at the bundle's own numbers
  framePub_of_spots stands24 from the test spotsFitB and "the request's shape has 25 links"
  SealFrom          an implication: from two bounds on the base of the piece at 357 (the trees of
                    the index-mask message and of the message W lie below it): the tie at 357. The
                    two bounds are shown here, from fence (seal_low_atAll, FrameSealLow.lean)
  frame_arm         h.Kind L KindName.frame from FramePub h, kn, SealFrom h L and h.K9Cond L

kn is no test: it speaks of every state that some prover, honest or not, can reach: at the 51
numbers, where no check has failed: the verifier's table of trees is in order counted from tree 0,
it fits, and the carried rows name messages that have a place. It is a lemma elsewhere (kn_atAll).

"Public data": Zp and cF are what the maker returns off the three public files (h.laid.pub,
h.laid.value): no byte of a proof enters FramePub.

Limits. No premise is shown here. verify() runs neither test of FramePub. A member of AtMgA is
proved at the second hash function OnBytes.secondHashFunction, at the two written sets of public files
VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, in the side library (AtFullSide/Top/: headMember_zFull,
headMember_zGap); at other files or another hash none is shown. That a reached state on which no
check has failed meets the table's promise at one of the 51
borders; and that the sentence on the carried word (carryAtZ) is ever true behind a step: none is
shown anywhere in Lean: no example. At OnBytes.secondHashFunction alone. No soundness statement.

-/
import Johnson.P1L20R.FrameFourAll
import Johnson.P1L20R.FrameSealLow
import Johnson.P5J.K09Behind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf fenceFit)
open VerifiableInference.Desc.First.K2Caller (spotsFitB stands24)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's two facts on public data.** -/
structure FramePub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Prop where
  /-- the code switch behind the last segment (number 24) is not of the sort "output head" -/
  stands24 : (ProofFile.pAtK2 Zp 24).stands ≠ .head
  /-- a test with code: every OOD-sampled oracle message whose pin is open at a border lies in a
  tree that the sub-protocols in front of that border have announced -/
  fence : fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true

/-- FramePub from the test spotsFitB (no two code switches open one group, and each is of the sort
that its segment's number asks), "the request's shape has 25 links", and fenceFit's yes. -/
theorem framePub_of_spots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (spots : spotsFitB Zp = true) (links25 : Zp.s₀.check.frame.shape.link.length = 25)
    (fence : fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true) : FramePub h :=
  ⟨stands24 spots links25, fence⟩

/-- The seal's tie, as it is handed in: an implication from two bounds on the base of the piece at
357 to the tie at 357. -/
def SealFrom (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  (∀ q, (h.toAtMg.row L)[357]? = some q → (dmOf h).N.index.1 < Piece.base q) →
  (∀ q, (h.toAtMg.row L)[357]? = some q → (dmOf h).N.w.1 < Piece.base q) →
  ∀ q, (h.toAtMg.row L)[357]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch 357 (q.withMap (h.toAtMg.ex L 357))

set_option maxHeartbeats 4000000 in
/-- **The kind "frame" under AtMgA**: 51 ties shown; 25 out of h.K9Cond L; 1 out of SealFrom h L. -/
theorem frame_arm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FramePub h)
    (kn : ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
      KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2))
    (hSeal : SealFrom h L) (C9 : h.K9Cond L) : h.Kind L KindName.frame :=
  frame_kind_of7b h L q₁ q₂ q₃
    { low := fun k hk q hq => by
        obtain ⟨pk, hpk, -, -⟩ := idle_at hk
        exact low_atAll h L q₁ q₂ q₃ W.fence k
          (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hpk).1) q hq
      whole := ⟨D, (whole_atAll h L q₁ q₂ q₃).1,
        fun k _ q hq => (whole_atAll h L q₁ q₂ q₃).2 k q hq⟩
      fenceEnds := fun k hk q hq m hm _ =>
        fenceEnds_atAll h L q₁ q₂ q₃ W.stands24 k hk q hq m hm
      stands24 := W.stands24
      kn := kn
      sealTie := hSeal (fun q hq => (seal_low_atAll h L q₁ q₂ q₃ W.fence q hq).1)
        fun q hq => (seal_low_atAll h L q₁ q₂ q₃ W.fence q hq).2
      behindTies := P5J.k09_behindTies h L C9 }

end

end P1L20

#print axioms P1L20.framePub_of_spots
#print axioms P1L20.frame_arm
