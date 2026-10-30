-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsAtFilling.lean: kind K14: UNDER THE LIBRARY's HEAD THE
PLAN qAt Zp Np, AT WHICH Honest/K14/SendingsAtHead.lean AND SendingsSeated.lean SPEAK, IS THE PLAN
AT WHICH THE FRAME's TWO MAKERS OF THE SHARED CHAIN's HALVES LAY THE TWO SENDINGS' HALVES: nowShared
(Honest/SharedChainProverSides.lean), AND THE MAKER THAT GOES THROUGH THIS KIND's sixOf (Honest/K14/Six.lean);
and what the seated sides declare at the list that these makers' readers read. Statements with their
proofs: calls. No definition.

  filling_at_head **the filling's reader of the plan returns qAt Zp Np; its reader of the shared
                  chain returns the library's seatN Zp Np; and nowShared Zp returns the kind's own
                  proverSidesOfSharedRounds with proverSidesOfSharedSendings at the plan qAt Zp Np and the number 0 of the round
                  "LIN point"**: by readers_at and now_made (Honest/K14/AtFilling.lean),
                  made_of_plan (AtFillingMore.lean), plan2_at_head (PlanAtHead.lean) and the head's
                  own places
  linOk_at_head   under the head the library's test on the linear part's shape with its codes
                  accepts at qAt Zp Np: by the library's hlin_of_written
                  (Johnson/Flat/Last/RowZeroAtZReal.lean)
  six_at_head     **sixOf returns, at qAt Zp Np, the flat list of seatN Zp Np, EVERY reader of the
                  index and the plan's item's pads and tails: the kind's own proverSidesOfSharedRounds with proverSidesOfSharedSendings
                  at the plan qAt Zp Np and the number 0**: its three tests accept: by sixOf_flat
                  (Honest/K14/DataMade.lean), linOk_at_head and sendings_at_head
  sixBody_at_head **the same of the two readers and sixOf in one term. THE TERM IS WRITTEN OUT: it
                  is the body of the frame's nowSharedBy (Honest/AtPureWiderAt.lean), which is not
                  imported here**: that file stands over all kinds' halves. That the written term is
                  that body is not shown here
  seated_declares_plain   **seated_declares at the flat list of seatN Zp Np, not carried to another
                  type of claims**: the list that the filling's readers read (sharedInFront;
                  rowsNow, AtFilling.lean): by flatOf_plain (AtFilling.lean). (seated_declares_head
                  has the list carried to any type of claims: at the file's own type that is the
                  list of the shared chain's letters)

What is not claimed. THAT A FILLING's FIELD FOR THE SHARED CHAIN IS THE LIST OF ONE OF THESE TWO
MAKERS: no filling is imported. That a filling lays its SIDES for these two rows by Side.seated off
either list: the makers lay halves, no sides. By its own file's head nowShared is the halves of
K14's quiet rounds, of its round "SPLIT" and of the two sendings of the folded row and of Omega. The
other premises of the laws on these parts. Nothing of a run. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.AtFillingMore
import Johnson.Desc.ProofFile.Honest.K14.SendingsSeated
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead
import Johnson.Flat.Last.RowZeroAtZReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (St beforePointOf)
open Desc.K14.Law (seatN)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {o : ProofFile.SecondHashFunctionArgument}

/-- **Under the library's head: what the filling's two readers and nowShared return.** -/
theorem filling_at_head (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    p14At Zp = some (qAt Zp Np) ∧ onlineSharedChain Zp = some (seatN Zp Np) ∧
      nowShared Zp = .ok (proverSidesOfSharedRounds (planData (qAt Zp Np)) id ++
        proverSidesOfSharedSendings { P := qAt Zp Np, atPoint := 0 } id (randNow (qAt Zp Np))) := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨a, b⟩ := readers_at Zp Np h.laid.places
  exact ⟨a, b, now_made Zp Np h.laid.places (made_of_plan Zp Np hP)⟩

/-- Under the library's head the library's test on the linear part's shape with its codes accepts at
the shared chain's own parameters. -/
theorem linOk_at_head (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    OnBytes.linOk (qAt Zp Np).codes (qAt Zp Np).S = true := by
  obtain ⟨x, hx, W⟩ := Desc.K14.Law.Sh.written_of_made h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)
  exact VerifiableInference.OnPublicFiles.Last.hlin_of_written W hx (beforePointOf Np)

/-- **Under the library's head sixOf returns**, at the shared chain's own parameters, the flat list
of the library's seatN Zp Np, every reader of the index and the plan's item's pads and tails. -/
theorem six_at_head {W₀ Ky X : Type} (h : P5J.AtMgA o Z D r Zp Np cF x₀)
    (weights : W₀ → Weights) :
    (sixOf (qAt Zp Np) (seatN Zp Np).chain.blocksInOrder weights (randNow (qAt Zp Np)) :
        Except String (List (Placed Empty (Common W₀ IndexCommitterCoins Ky) X))) =
      .ok (proverSidesOfSharedRounds { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } weights ++
        proverSidesOfSharedSendings { P := qAt Zp Np, atPoint := 0 } weights (randNow (qAt Zp Np))) := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  exact sixOf_flat (flatOf_plain Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8
    (tests Np) last B.made) B.made (linOk_at_head h) (sendings_at_head h).1 weights
    (randNow (qAt Zp Np))

/-- **The same of the two readers and sixOf in one term**, written out: the body of the frame's
nowSharedBy, which is not imported here. -/
theorem sixBody_at_head {W₀ : Type} (h : P5J.AtMgA o Z D r Zp Np cF x₀)
    (weights : W₀ → Weights) :
    ((due? "the shared chain's own parameters" (p14At Zp)).bind fun P =>
      (due? "the shared chain's place in the description" (onlineSharedChain Zp)).bind fun s =>
        sixOf P s.chain.blocksInOrder weights fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩ :
        Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))) =
      .ok (proverSidesOfSharedRounds { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } weights ++
        proverSidesOfSharedSendings { P := qAt Zp Np, atPoint := 0 } weights (randNow (qAt Zp Np))) := by
  obtain ⟨a, b, -⟩ := filling_at_head h
  rw [a, b]
  exact six_at_head h weights

/-- **seated_declares under the library's head, at the flat list of the library's seatN Zp Np**,
which the filling's readers read. -/
theorem seated_declares_plain {X Pb V W : Type} (h : P5J.AtMgA o Z D r Zp Np cF x₀) (a : Nat)
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall St)) :
    (∃ σ : Side St Unit V W X Pb,
        Side.seated (seatN Zp Np).chain.blocksInOrder
          (sendPlace 2) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 2 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU ⟨qAt Zp Np, a⟩).Q ∧
        SendDeclared σ.block (jobU ⟨qAt Zp Np, a⟩)) ∧
      ∃ σ : Side St Unit V W X Pb,
        Side.seated (seatN Zp Np).chain.blocksInOrder
          (sendPlace 5) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 5 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega ⟨qAt Zp Np, a⟩).Q ∧
        SendDeclared σ.block (jobOmega ⟨qAt Zp Np, a⟩) := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  exact seated_declares (flatOf_plain Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7
    B.b8 (tests Np) last B.made) B.made a row fs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.filling_at_head
#print axioms ProofFile.Honest.K14.linOk_at_head
#print axioms ProofFile.Honest.K14.six_at_head
#print axioms ProofFile.Honest.K14.sixBody_at_head
#print axioms ProofFile.Honest.K14.seated_declares_plain
