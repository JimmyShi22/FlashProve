-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AtWiderParts.lean: kind K14: UNDER THE LIBRARY's HEAD, THE HALVES
THAT THE FRAME's MAKER nowSharedBy (Honest/AtPureWiderAt.lean) LAYS AT THE PLACES OF THE SHARED
CHAIN's TWO SENDINGS HAVE AS THEIR ONE PART liftSend (witOf …) (sendingPart …), AT THE SENDING's
JOB; AND SO HAS THE SEATED SIDE WITH THAT PART AS ITS ROW. Statements with their proofs. No
definition.

Why. The laws on these sendings' coins (rowsServe_at_shared, Honest/K14/RowsAtShared.lean, and
sendings_fresh_of_tests, Honest/K14/FreshAtPure.lean: the fields exact and fresh of Good,
Honest/Side.lean) speak of a side whose row is [(liftSend wit (sendingPart (jobU A)), sim)], or the
like with jobOmega: the rows of sendingRows (Honest/K14/ExactRows.lean). THAT THE PART FOUND HERE IS
sendingRows' PART IS SEEN BY UNFOLDING witOf: NO STATEMENT HERE SAYS IT. AND THE LISTS PART:
rowsServe_at_shared speaks of sides off the description's own field shared, flat, at its own type of
claims; wider_side's side is taken off (seatN Zp Np).chain.blocksInOrder at the type Unit: NO STATEMENT HERE
JOINS THE TWO. nowSharedBy_at_head (Honest/K14/AtWiderShared.lean) says which list the maker
returns; here the half at each of the two places is read off that list, and held against the half of
the seated side with that row.

  wider_parts     **in the list that nowSharedBy returns, at every reader of the index, the half
                  that is found at ⟨2, none, 2, .K1⟩ has the one part liftSend (witOf …)
                  (sendingPart (jobU ⟨qAt Zp Np, 0⟩)), and the half found at ⟨2, none, 5, .K1⟩ the
                  like with jobOmega**: by sendHalves_eq (Honest/K14/SendingsPlay.lean); witOf
                  (Honest/K14/PaidAll.lean): the committed table's rows, whole, at that reader and
                  at the plan's item's pads and tails
  wider_side      **the side that Side.seated returns off the flat list of the library's seatN Zp Np
                  at such a place, with that part and any simulator as its row, has that found half
                  as its half** (Side.half): by seated_declares_plain
                  (Honest/K14/SendingsAtFilling.lean)

What is not claimed. That a filling's field for the shared chain is nowSharedBy's list, or that it
lays its sides by Side.seated. The other premises of the laws on these parts: on the book, on the
count of positions, on the stand. The full size alone. Nothing of a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.K14.PaidAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open Desc.K14 (St)
open Desc.K14.Law (seatN)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}

/-- **The halves that are found at the two sendings' places in the list that nowSharedBy returns**,
under the library's head, at every reader of the index. -/
theorem wider_parts (h : P5J.AtMgA o Z D r Zp Np cF x₀) (weights : W₀ → Weights) :
    ∃ hs, nowSharedBy weights Zp = .ok hs ∧
      (hs.find? fun g => g.place == sendPlace 2) = some
        { place := sendPlace 2
          parts := [liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
            (sendingPart (jobU ⟨qAt Zp Np, 0⟩))] } ∧
      (hs.find? fun g => g.place == sendPlace 5) = some
        { place := sendPlace 5
          parts := [liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
            (sendingPart (jobOmega ⟨qAt Zp Np, 0⟩))] } := by
  refine ⟨_, nowSharedBy_at_head h weights, ?_, ?_⟩
  · rw [sendHalves_eq]
    unfold proverSidesOfSharedRounds
    dsimp only
    rw [(sendings_at_head h).2.1]
    rfl
  · rw [sendHalves_eq]
    unfold proverSidesOfSharedRounds
    dsimp only
    rw [(sendings_at_head h).2.1]
    rfl

/-- **Under the library's head: the seated side with such a part as its row has the found half as
its half.** -/
theorem wider_side {Pb : Type} (h : P5J.AtMgA o Z D r Zp Np cF x₀) (weights : W₀ → Weights)
    (simU simO : Sim Pb) (fs : List (Fall St)) :
    (∃ σ : Side St Unit Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit Pb,
        Side.seated (seatN Zp Np).chain.blocksInOrder (sendPlace 2)
          [(liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
            (sendingPart (jobU ⟨qAt Zp Np, 0⟩)), simU)] fs = some σ ∧
        σ.half = { place := sendPlace 2
                   parts := [liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
                     (sendingPart (jobU ⟨qAt Zp Np, 0⟩))] }) ∧
      ∃ σ : Side St Unit Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit Pb,
        Side.seated (seatN Zp Np).chain.blocksInOrder (sendPlace 5)
          [(liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
            (sendingPart (jobOmega ⟨qAt Zp Np, 0⟩)), simO)] fs = some σ ∧
        σ.half = { place := sendPlace 5
                   parts := [liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
                     (sendingPart (jobOmega ⟨qAt Zp Np, 0⟩))] } := by
  obtain ⟨⟨σ₂, a2, r2, p2, -, -⟩, -⟩ := seated_declares_plain h 0
    [(liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
      (sendingPart (jobU ⟨qAt Zp Np, 0⟩)), simU)] fs
  obtain ⟨-, σ₅, a5, r5, p5, -, -⟩ := seated_declares_plain h 0
    [(liftSend (witOf (qAt Zp Np) weights (randNow (qAt Zp Np)))
      (sendingPart (jobOmega ⟨qAt Zp Np, 0⟩)), simO)] fs
  refine ⟨⟨σ₂, a2, ?_⟩, ⟨σ₅, a5, ?_⟩⟩
  · unfold Side.half
    rw [r2, p2]
    rfl
  · unfold Side.half
    rw [r5, p5]
    rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.wider_parts
#print axioms ProofFile.Honest.K14.wider_side
