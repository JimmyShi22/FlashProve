-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Fifteen.lean: THE JOIN AT `ProofFile.pureSeat`: `back_at_full`
(Full/Join.lean) at the proof file's own lots (`ProofFile.onlineFirstChainBlockTables`, ProofFile/OnlineDescriptionBlocks.lean), FROM FIFTEEN
ROWS BY NAME. Statements and proofs.
  `rows_fifteen`   a row for each of `onlineFirstChainBlockTables Z`'s thirteen lots by name and for the two of
                   `p4Pure Z` gives `back_at_full`'s hR
  `steady_pure`    `Steady` at every lot of `onlineFirstChainBlockTables Z`, from K9's lot's and the two of `p4Pure Z`:
                   the other twelve supply no batching, by their texts
  `back_at_pure`   `back_at_full` at `pureSeat o Z`
WHAT STAYS A PREMISE of `back_at_pure`: h₁ … h₄ and hB on the base and the segments' sorts; hp:
which two lots `p4Pure Z` holds; r0 … r14: THE FIFTEEN ROWS; s7 s13 s14: `Steady` at three lots;
h₆ h₇: the two later seats' names and stand-ins.
Limits. NONE OF THESE IS PAID HERE. As Full/Join.lean's. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Join
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem rows_fifteen {Z : Pub} {G : Ground} {L13 L14 : Lot} (hp : p4Pure Z = [L13, L14])
    (r0 : RowAt G (framesLot Z) lot0) (r1 : RowAt G (k1Pure Z) lot1)
    (r2 : RowAt G (k2Pure Z) lot2) (r3 : RowAt G (K3Lot.lot Z) lot3)
    (r4 : RowAt G (k4Lot Z) lot4) (r5 : RowAt G (H2K5.lotN Z) lot5)
    (r6 : RowAt G (P1K8.lot Z) lot6) (r7 : RowAt G (k9Ninth Z) lot7)
    (r8 : RowAt G (K11.lot Z) lot8) (r9 : RowAt G (VerifiableInference.Desc.K12.lot Z) lot9)
    (r10 : RowAt G (VerifiableInference.Desc.K13.lot Z) lot10)
    (r11 : RowAt G (VerifiableInference.Desc.K13.lot4 Z) lot11)
    (r12 : RowAt G (VerifiableInference.Desc.K13.lotEnd Z) lot12)
    (r13 : RowAt G L13 lot13) (r14 : RowAt G L14 lot14) :
    List.Forall₂ (RowAt G) (onlineFirstChainBlockTables Z) wsW := by
  unfold onlineFirstChainBlockTables wsW
  rw [hp]
  exact .cons r0 (.cons r1 (.cons r2 (.cons r3 (.cons r4 (.cons r5 (.cons r6 (.cons r7 (.cons r8
    (.cons r9 (.cons r10 (.cons r11 (.cons r12 (.cons r13 (.cons r14 .nil))))))))))))))

theorem steady_pure {Z : Pub} {G : Ground} {L13 L14 : Lot} (hp : p4Pure Z = [L13, L14])
    (s7 : Steady G (k9Ninth Z)) (s13 : Steady G L13) (s14 : Steady G L14) :
    ∀ L ∈ onlineFirstChainBlockTables Z, Steady G L := by
  intro L hL
  unfold onlineFirstChainBlockTables at hL
  rw [hp] at hL
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact s7
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact steady_none G _ fun _ => rfl
  · exact s13
  · exact s14

theorem back_at_pure (o : SecondHashFunctionArgument) (Z : Pub) (B : PureBase) {L13 L14 : Lot}
    (h₁ : B.spots = spotsW) (h₂ : B.shape = shapeW) (h₃ : B.batchAt = batchAtW)
    (h₄ : subsOf Z = subsW)
    (hB : B.all = (onlineFirstChainBlockTables Z).map fun L => (L, L.blocks B.G₀))
    (hp : p4Pure Z = [L13, L14])
    (r0 : RowAt B.G₀ (framesLot Z) lot0) (r1 : RowAt B.G₀ (k1Pure Z) lot1)
    (r2 : RowAt B.G₀ (k2Pure Z) lot2) (r3 : RowAt B.G₀ (K3Lot.lot Z) lot3)
    (r4 : RowAt B.G₀ (k4Lot Z) lot4) (r5 : RowAt B.G₀ (H2K5.lotN Z) lot5)
    (r6 : RowAt B.G₀ (P1K8.lot Z) lot6) (r7 : RowAt B.G₀ (k9Ninth Z) lot7)
    (r8 : RowAt B.G₀ (K11.lot Z) lot8)
    (r9 : RowAt B.G₀ (VerifiableInference.Desc.K12.lot Z) lot9)
    (r10 : RowAt B.G₀ (VerifiableInference.Desc.K13.lot Z) lot10)
    (r11 : RowAt B.G₀ (VerifiableInference.Desc.K13.lot4 Z) lot11)
    (r12 : RowAt B.G₀ (VerifiableInference.Desc.K13.lotEnd Z) lot12)
    (r13 : RowAt B.G₀ L13 lot13) (r14 : RowAt B.G₀ L14 lot14)
    (s7 : Steady B.G₀ (k9Ninth Z)) (s13 : Steady B.G₀ L13) (s14 : Steady B.G₀ L14)
    (h₆ : ((onlineSharedChain Z).map fun A => (A.lot, A.standIns)) = sharedW)
    (h₇ : ((onlineLastChain Z).map fun A => (A.lot, A.standIns)) = secondW) :
    faultsAt (pureSeat o Z) B = [] ∧ lackingAt (pureSeat o Z) (partsAt (pureSeat o Z) B) = [] ∧
      ∃ base, (partsAt (pureSeat o Z) B).base = .ok base ∧ base.map skel = baseW ∧
        ∃ c, chainBy Z base (partsAt (pureSeat o Z) B).frames (partsAt (pureSeat o Z) B).road =
            .ok c ∧ c.blocksInOrder.map skel = flatW :=
  back_at_full Z (pureSeat o Z) B (onlineFirstChainBlockTables Z) h₁ h₂ h₃ h₄ hB rfl
    (rows_fifteen hp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
    (steady_pure hp s7 s13 s14) h₆ h₇

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.rows_fifteen
#print axioms ProofFile.Sk.Full.steady_pure
#print axioms ProofFile.Sk.Full.back_at_pure
