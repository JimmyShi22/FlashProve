-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AcceptedAtHead.lean: the kind "the code switch" (K2): AT THE
SWITCH INTO A LATER GROUP (m < 23): THE VERIFIER's MEMBER AT ITS NUMBER ACCEPTS A PLAYED STEP: (1)
the sub-protocol that the description seats at number 14 (m + 1) + 2: its own step (`Block.step`)
says yes behind whatever half of two rounds has played it, wherever the columns that it reads are
laid, at a state that is reached there, under the head; (2) SO THE FRAME's DEBT "IT IS ACCEPTED",
ASKED FROM THE PAIR (`AcceptedS`, Honest/Thread/PaysS.lean), AT THE FRAME's OWN THREAD OF THE FIRST
CHAIN AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean) AND ITS LETTER `SaidOk`,
AT EVERY FALL. Two statements with their proofs: joins; no definition. `K2Seated` is not asked.

  `link_seat_step`       (1)
  `link_acceptedS_head`  (2)

By: `link_seat_yes` (Johnson/Desc/K2/Honest/Returns/SeatYes.lean) · `played_tests`
(Honest/K2/Law/PlayedTests.lean) · the frame's `step_iff_decide` (Honest/Law/Cut.lean),
`steps_one_half` (Honest/Law/Thread.lean), `thrS_reach_below` (Honest/Thread/ReachAtHead.lean).

THE PREMISES OF (2), ALL OF THEM: the head `P5J.AtMgA` and the opening · m < 23 · AT THE MEMBER's
PLACE THE PROVER's LIST OF HALVES FOR THE FIRST CHAIN (`Prover.first`: it is that thread's own list,
by make: the frame's `sits_head`) HAS A HALF, AND IT HAS TWO ROUNDS. Which half is not asked. That
the member's number lies within the flat list is the library's (`IM.flat_len_scope`,
Johnson/IMR/MemberOfGate.lean: 358 entries in the goals' scope): called. OF WHAT THE DEBT's OWN TEXT
HANDS OVER, TWO THINGS ARE NOT SPENT: that the chain does not stop and that the fall is silent: so
(2) holds at every fall, and whether or not the chain would stop.

WHAT IT DOES NOT SAY. THAT THE THREAD HAS A STAND AT THE MEMBER: by the frame's own word no member
of the head together with the thread's sentence is shown: WHERE THERE IS NO STAND THE DEBT IS PAID
FOR NOTHING. THE YES IS NO SIGN THAT A MESSAGE IS HONEST: it holds behind EVERY half of two rounds
that has played: of what the half sends at this step nothing is tested but its shape. That a half
plays, and that the columns are laid, is another debt (`PlaysS`). THAT THE KIND's ONE LOT's HALF IS
LAID AT THAT PLACE, WITH TWO ROUNDS, IN A PROVER THAT THE FRAME NAMES IS TYPED NOWHERE HERE. THE
STEP FROM `SaidOk` TO THE LETTER AT WHICH THE FRAME's FEED ASKS ITS DEBTS IS NOT MADE HERE (the
frame's `acceptedS_mono`, Honest/Thread/SaidMono.lean: not called). Returns/YesReached.lean's head
says the rest in five points.

Limits. THE LINKS ALONE: nothing at the two other sorts of place. ONE DEBT OF FIVE, at 23 of the
kind's 25 members. Of a sub-protocol's step: not of a verifier's program. THE FULL SIZE AND THE
FORMAT's EARLIER HASH ALONE. IT STANDS ON FILES OF THREE HOUSES THAT ARE IN NO SEALED LIBRARY: this
one's, twelve of the house that has the plan's numbers and `leafOk`, and the frame's own: each
graded in Returns/SeatYes.lean's head or in the heads that it names. A near relative at another
kind: the frame's own law with this end at that thread at twelve borders of the kind K5
(Honest/Thread/K5Feeds.lean). Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatYes
import Johnson.Desc.ProofFile.Honest.K2.Law.PlayedTests
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc (noDigest Block Chain Place OpenedColumn Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (link_seat_yes switchPlaceAt)
open VerifiableInference.Desc.Sound (below MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA F0T TS CellsM)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (lettersHead thrS_reach_below WtF Script)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **(1) The seated sub-protocol's own step.** -/
theorem link_seat_step (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (h23 : i < 23) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[14 * (i + 1) + 2]? = some b ∧
      b.place = switchPlaceAt (i + 1) ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (i + 1) + 2) (z, s) →
        ∀ {V W X : Type} (g : Placed V W X) (v : Option V) (c : RowCoins g.parts)
          (ds : List Fmt.Drawn) (m : Mid W X) (y : List Played × Mid W X) (chain ft : Nat)
          (stored : Nat → Nat → Option (List UInt64))
          (tree : Fmt.TreeSource → Option (Place × Table)) (cols : List OpenedColumn), g.rounds = 2 →
          play (g.steps b v c) ds [] m = .ok y → drawsFit b.rounds ds = true →
          fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols →
          ∃ t, b.step ft s (roundsOf y.1) cols = .ok (t, cols.length) := by
  obtain ⟨b, nm, Pp, n, hb, hpc, -, -, hro, hor, hyes⟩ := link_seat_yes h O h23
  refine ⟨b, hb, hpc, fun z s hr V W X g v c ds m y chain ft stored tree cols hg hy hd hc => ?_⟩
  have hg' : g.rounds = b.rounds.length := by
    rw [hg, hro]
    rfl
  have ho : b.oracles.length = b.rounds.length := by
    rw [hro, hor]
    rfl
  obtain ⟨R₁, R₂, e1, e2, hrf, hcols⟩ := played_tests _ hro hg' ho hy hd hc
  obtain ⟨t, ht⟩ := hyes z s hr (noDigest R₁) (noDigest R₂) ft R₁.drawn R₂.drawn cols rfl hrf
    hcols
  refine ⟨t, (step_iff_decide s t hg' ho hy hd hc).2 ?_⟩
  rw [e1, e2, hro]
  exact ht

/-- **(2) The debt, asked from the pair, at the frame's own thread at the head.** H … w: the letters
that the thread leaves free. -/
theorem link_acceptedS_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (h23 : i < 23) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {g : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hhalf : (H.first.find? fun a => a.place == switchPlaceAt (i + 1)) = some g)
    (hg : g.rounds = 2)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      (14 * (i + 1) + 2) := by
  obtain ⟨b, hb, hpc, hstep⟩ := link_seat_step h O h23
  intro blk hblk k s m E ds y cs hT hd _ _ hM
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  have hlen : 14 * (i + 1) + 2 ≤ cF.blocksInOrder.length := by
    rw [IM.flat_len_scope h.scope h.reads O]
    omega
  have hr := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  rw [← hpc] at hhalf
  obtain ⟨c, -, rfl⟩ := steps_one_half hhalf hl
  obtain ⟨t, ht⟩ := hstep _ s hr g _ c ds m y _ _ _ _ cs hg hy hd hc
  exact ⟨t, ⟨⟨_, hl, hy⟩, hc⟩, ht⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.link_seat_step
#print axioms ProofFile.Honest.K2.Law.link_acceptedS_head
