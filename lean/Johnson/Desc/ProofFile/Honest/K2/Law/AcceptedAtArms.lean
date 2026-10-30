-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AcceptedAtArms.lean: the kind "the code switch" (K2): AT ITS
TWO ARMS (339, the output head's switch; 353, behind the last segment): THE VERIFIER's MEMBER AT ITS
NUMBER ACCEPTS A PLAYED STEP: (1) the sub-protocol that the description seats there: its own step
(`Block.step`) says yes behind whatever half of two rounds has played it, wherever the columns that
it reads are laid, at a state that is reached there, under the head; (2) SO THE FRAME's DEBT "IT IS
ACCEPTED", ASKED FROM THE PAIR (`AcceptedS`, Honest/Thread/PaysS.lean), AT THE FRAME's OWN THREAD OF
THE FIRST CHAIN AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean) AND ITS LETTER
`SaidOk`, AT EVERY FALL. THE LIKE, AT THE ARMS, OF Honest/K2/Law/AcceptedAtHead.lean AT THE 23
LINKS: ITS TWO STATEMENTS AND THEIR PROOFS, WITH THE NUMBER AND THE PLACE TURNED. So this debt is
paid at all 25 members of the kind. Four statements with their proofs: joins; no definition.

  `head_seat_step`, `fin_seat_step` (1), at 339 and at 353
  `head_acceptedS_head`, `fin_acceptedS_head` (2), at 339 and at 353

By: `head_seat_laid`, `fin_seat_laid` (Johnson/Desc/K2/Honest/Returns/ArmsSeatYes.lean) ·
`played_tests` (Honest/K2/Law/PlayedTests.lean) · the frame's `step_iff_decide`
(Honest/Law/Cut.lean), `steps_one_half` (Honest/Law/Thread.lean), `thrS_reach_below`
(Honest/Thread/ReachAtHead.lean) · the library's `flat_len_scope` (Johnson/IMR/MemberOfGate.lean).

THE PREMISES OF (2), ALL OF THEM: the head `P5J.AtMgA` and the opening · AT THE MEMBER's PLACE THE
PROVER's LIST OF HALVES FOR THE FIRST CHAIN (`Prover.first`) HAS A HALF, AND IT HAS TWO ROUNDS.
Which half is not asked. OF WHAT THE DEBT's OWN TEXT HANDS OVER, TWO THINGS ARE NOT SPENT: that the
chain does not stop and that the fall is silent.

WHAT IT DOES NOT SAY. THAT THE THREAD HAS A STAND AT THE MEMBER: WHERE THERE IS NO STAND THE DEBT IS
PAID FOR NOTHING. THE YES IS NO SIGN THAT A MESSAGE IS HONEST: it holds behind EVERY half of two
rounds that has played: of what the half sends at this step nothing is tested but its shape. That a
half plays, and that the columns are laid, is another debt (`PlaysS`). THAT THE KIND's ONE LOT's
HALF IS LAID AT THAT PLACE, WITH TWO ROUNDS, IN A PROVER THAT THE FRAME NAMES IS TYPED NOWHERE HERE.
THE STEP FROM `SaidOk` TO THE LETTER AT WHICH THE FRAME's FEED ASKS ITS DEBTS IS NOT MADE HERE.

Limits. ONE DEBT OF FIVE, at 2 of the kind's 25 members. Of a sub-protocol's step: not of a
verifier's program. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. IT STANDS ON FILES THAT ARE
IN NO SEALED LIBRARY: this folder's and Johnson/Desc/K2/Honest/Returns/'s, files on the plan's
numbers, on `leafOk` and on what the arms look up that are not ours, and the frame's own: each
graded in Returns/ArmsSeatYes.lean's head or in the heads that it names. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.ArmsSeatYes
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
open VerifiableInference.Desc.K2.Honest.Returns (head_seat_laid fin_seat_laid headPlaceAt)
open VerifiableInference.Desc.Sound (below MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA F0T TS CellsM)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2PlaceF)
open ProofFile.Honest.FirstThread (lettersHead thrS_reach_below WtF Script)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **(1) The seated sub-protocol's own step, at 339.** -/
theorem head_seat_step (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[339]? = some b ∧ b.place = headPlaceAt ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s) →
        ∀ {V W X : Type} (g : Placed V W X) (v : Option V) (c : RowCoins g.parts)
          (ds : List Fmt.Drawn) (m : Mid W X) (y : List Played × Mid W X) (chain ft : Nat)
          (stored : Nat → Nat → Option (List UInt64))
          (tree : Fmt.TreeSource → Option (Place × Table)) (cols : List OpenedColumn), g.rounds = 2 →
          play (g.steps b v c) ds [] m = .ok y → drawsFit b.rounds ds = true →
          fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols →
          ∃ t, b.step ft s (roundsOf y.1) cols = .ok (t, cols.length) := by
  obtain ⟨b, nm, Pp, n, hb, hpc, -, -, hro, hor, hyes⟩ := head_seat_laid h O
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

/-- **(1) The same at 353.** -/
theorem fin_seat_step (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[353]? = some b ∧ b.place = k2PlaceF ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s) →
        ∀ {V W X : Type} (g : Placed V W X) (v : Option V) (c : RowCoins g.parts)
          (ds : List Fmt.Drawn) (m : Mid W X) (y : List Played × Mid W X) (chain ft : Nat)
          (stored : Nat → Nat → Option (List UInt64))
          (tree : Fmt.TreeSource → Option (Place × Table)) (cols : List OpenedColumn), g.rounds = 2 →
          play (g.steps b v c) ds [] m = .ok y → drawsFit b.rounds ds = true →
          fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols →
          ∃ t, b.step ft s (roundsOf y.1) cols = .ok (t, cols.length) := by
  obtain ⟨b, nm, Pp, n, hb, hpc, -, -, hro, hor, hyes⟩ := fin_seat_laid h O
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

/-- **(2) The debt, asked from the pair, at the frame's own thread at the head, at 339.** H … w: the
letters that the thread leaves free. -/
theorem head_acceptedS_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {g : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hhalf : (H.first.find? fun a => a.place == headPlaceAt) = some g)
    (hg : g.rounds = 2)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      339 := by
  obtain ⟨b, hb, hpc, hstep⟩ := head_seat_step h O
  intro blk hblk k s m E ds y cs hT hd _ _ hM
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  have hlen : 339 ≤ cF.blocksInOrder.length := by
    rw [IM.flat_len_scope h.scope h.reads O]
    omega
  have hr := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  rw [← hpc] at hhalf
  obtain ⟨c, -, rfl⟩ := steps_one_half hhalf hl
  obtain ⟨t, ht⟩ := hstep _ s hr g _ c ds m y _ _ _ _ cs hg hy hd hc
  exact ⟨t, ⟨⟨_, hl, hy⟩, hc⟩, ht⟩

/-- **(2) The same at 353.** -/
theorem fin_acceptedS_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {g : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hhalf : (H.first.find? fun a => a.place == k2PlaceF) = some g)
    (hg : g.rounds = 2)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      353 := by
  obtain ⟨b, hb, hpc, hstep⟩ := fin_seat_step h O
  intro blk hblk k s m E ds y cs hT hd _ _ hM
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  have hlen : 353 ≤ cF.blocksInOrder.length := by
    rw [IM.flat_len_scope h.scope h.reads O]
    omega
  have hr := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  rw [← hpc] at hhalf
  obtain ⟨c, -, rfl⟩ := steps_one_half hhalf hl
  obtain ⟨t, ht⟩ := hstep _ s hr g _ c ds m y _ _ _ _ cs hg hy hd hc
  exact ⟨t, ⟨⟨_, hl, hy⟩, hc⟩, ht⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.head_seat_step
#print axioms ProofFile.Honest.K2.Law.fin_seat_step
#print axioms ProofFile.Honest.K2.Law.head_acceptedS_head
#print axioms ProofFile.Honest.K2.Law.fin_acceptedS_head
