-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/DescAt.lean: the joint: `ProofFile.onlineDescription` returns at the full
size, and the first chain's skeletons are the written ones: the two ends of
Johnson/AtFull/Desc/Ledger.lean (`baseOf_of_parts`, `descPure_of_parts`) with `back_at_pure`
(Full/Fifteen.lean) laid between them. One theorem: three calls.
  `desc_at_full`  ⊢ there is a chain c with `onlineDescription o pol lay KL = .ok (fileDescBy o
                  pureRoad.links Z A B (fun s => s) (startS Z) c)` and `c.blocksInOrder.map skel = flatW`
The premises, each in its step's own terms. p₁: the public part returns Z. q₁ q₂: the places and the
shape that are made of Z are the written ones (Full/Data.lean). q₃: the blank ground, which is made
of the segments' data for a request of zeros that covers its first position alone, is G. h₄: the
segments' sorts are the written ones. hp: the two lots of `p4Pure Z`, by name. r0 … r14: a row a
lot, at G (`RowAt`, Full/Ask.lean). s7 s13 s14: three lots' batchings have one skeleton at every
gatherer. hA hB: the two later seats' names and stand-ins are the written ones. rA rB: the two later
seats.
Limits. A JOINING: IT PAYS NO PREMISE. That the premises can be met together is not shown here. The
full size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Fifteen
import Johnson.Desc.ProofFile.Law.Skel.Full.Ties
import Johnson.AtFull.Desc.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem desc_at_full {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {G : Ground}
    {A : SharedSeat} {B : SecondSeat} {L13 L14 : Lot}
    (p₁ : pubPlain o pol lay KL = .ok Z)
    (q₁ : spotsOf Z.cuts = some spotsW) (q₂ : shapeOf Z = .ok shapeW)
    (q₃ : blankBy (pureSeat o Z).links Z = some G) (h₄ : subsOf Z = subsW)
    (hp : p4Pure Z = [L13, L14])
    (r0 : RowAt G (framesLot Z) lot0) (r1 : RowAt G (k1Pure Z) lot1)
    (r2 : RowAt G (k2Pure Z) lot2) (r3 : RowAt G (K3Lot.lot Z) lot3)
    (r4 : RowAt G (k4Lot Z) lot4) (r5 : RowAt G (H2K5.lotN Z) lot5)
    (r6 : RowAt G (P1K8.lot Z) lot6) (r7 : RowAt G (k9Ninth Z) lot7)
    (r8 : RowAt G (K11.lot Z) lot8)
    (r9 : RowAt G (VerifiableInference.Desc.K12.lot Z) lot9)
    (r10 : RowAt G (VerifiableInference.Desc.K13.lot Z) lot10)
    (r11 : RowAt G (VerifiableInference.Desc.K13.lot4 Z) lot11)
    (r12 : RowAt G (VerifiableInference.Desc.K13.lotEnd Z) lot12)
    (r13 : RowAt G L13 lot13) (r14 : RowAt G L14 lot14)
    (s7 : Steady G (k9Ninth Z)) (s13 : Steady G L13) (s14 : Steady G L14)
    (hA : ((onlineSharedChain Z).map fun A => (A.lot, A.standIns)) = sharedW)
    (hB : ((onlineLastChain Z).map fun A => (A.lot, A.standIns)) = secondW)
    (rA : onlineSharedChain Z = some A) (rB : onlineLastChain Z = some B) :
    ∃ c, onlineDescription o pol lay KL =
        .ok (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c) ∧
      c.blocksInOrder.map skel = flatW := by
  obtain ⟨Bs, r₁, e₁, e₂, e₃, e₄, e₅⟩ :=
    Johnson.AtFull.Desc.baseOf_of_parts (T := pureSeat o Z) q₁ q₂ q₃
  subst e₃
  have h₃ : Bs.batchAt = batchAtW := by
    rw [e₅, h₄]
    exact batchAt_tie.symm
  obtain ⟨r₂, r₃, base, r₄, -, c, r₅, hc⟩ :=
    back_at_pure o Z Bs e₁ e₂ h₃ h₄ e₄ hp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
      s7 s13 s14 hA hB
  exact ⟨c, Johnson.AtFull.Desc.descPure_of_parts p₁ r₁ r₂ r₃ r₄ r₅ rA rB, hc⟩

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.desc_at_full
