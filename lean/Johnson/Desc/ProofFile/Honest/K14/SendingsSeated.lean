-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsSeated.lean: kind K14: WHAT THE SIDE THAT Side.seated
(Honest/Side.lean) RETURNS AT THE PLACE OF ONE OF THE SHARED CHAIN's TWO SENDINGS DECLARES: the
place, K1's two rounds at the job's own parameters, and SendDeclared
(Honest/K14/SendingsPlay.lean). Statements with their proofs. No definition.

Why. The laws on the coins of these two parts take a side as a variable, under equations on its row
and on its sub-protocol's rounds, and SendDeclared. Here these are met at the side that is taken off
a description's own list by its place.

  seated_send     at a list that begins as the shared chain's flat list does (FlatOf,
                  Johnson/Desc/K14/Honest/FlatForm.lean): Side.seated returns at ⟨2, none, 2, .K1⟩
                  and at ⟨2, none, 5, .K1⟩; the row is the row handed in; the sub-protocol is like
                  the library's own second and fifth. (seated_own and seated_some,
                  Honest/K14/GoodSeated.lean, have the like at the kind's four own places)
  job_rounds      the library's own two sendings declare K1's two rounds, IN THE LETTERS OF jobU AND
                  jobOmega (Honest/K14/Sendings.lean). The library has the fact at its own letters
                  (blocks_rounds, Johnson/Desc/K14/Honest/ChainSteps.lean, which is called; also
                  sends_declare, Johnson/Desc/K14/Law/LedgerRowOfCut.lean, and send_rounds,
                  Johnson/RunOne/KeySeedIs2Piece.lean)
  seated_declares **so the seated side has the place, the rounds and SendDeclared**, by
                  send_declares and sendDeclared_like (Honest/K14/PaidAll.lean). GENERAL IN THE
                  PLAN, THE LIST, THE ROW, THE FALLS AND THE NUMBER a OF THE ROUND "LIN point"
  seated_declares_head   **under the library's head, at the shared chain's own flat list**, carried
                  to any type of claims: that the library makes its eight sub-protocols there is
                  Plan2's (plan2_at_head, Honest/K14/PlanAtHead.lean); the list's form is
                  flatOf_carried's (FlatForm.lean). (The list not carried:
                  seated_declares_plain, Honest/K14/SendingsAtFilling.lean)

What is not claimed. That a filling of the frame lays its sides for these two rows by Side.seated
off that list. What stands in the list behind its ninth member is free: a second member at one of
the two places is never seen. The other premises of the laws on these parts. Nothing of a run.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.GoodSeated
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.K14.Law.LedgerSeedRounds
import Johnson.Desc.K14.Honest.ChainSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (P14 St blocks chainOf)
open Desc.K14.Honest (FlatOf Like flatOf_carried)

variable {Cl X Pb V W : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- **What Side.seated makes at the two sendings' places** of a list that begins as the shared
chain's flat list does: it returns; the row as handed; the sub-protocol like the library's own. -/
theorem seated_send (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall St)) :
    (∃ σ : Side St Cl V W X Pb, Side.seated xs (sendPlace 2) row fs = some σ ∧ σ.row = row ∧
        Like σ.block b2) ∧
      ∃ σ : Side St Cl V W X Pb, Side.seated xs (sendPlace 5) row fs = some σ ∧ σ.row = row ∧
        Like σ.block b5 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, -, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, -⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, pU, -, pO⟩ := send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have q1 := l1.place.trans p1
  have q2 := l2.place.trans pU
  have q3 := l3.place.trans p3
  have q4 := l4.place.trans p4
  have q5 := l5.place.trans pO
  refine ⟨⟨{ block := x2, row := row, fall := fallOf fs (sendPlace 2) }, ?_, rfl, l2⟩,
    ⟨{ block := x5, row := row, fall := fallOf fs (sendPlace 5) }, ?_, rfl, l5⟩⟩
  · unfold Side.seated
    rw [List.find?_cons_of_neg (by rw [q0]; decide), List.find?_cons_of_neg (by rw [q1]; decide),
      List.find?_cons_of_pos (by rw [q2]; decide)]
    rfl
  · unfold Side.seated
    rw [List.find?_cons_of_neg (by rw [q0]; decide), List.find?_cons_of_neg (by rw [q1]; decide),
      List.find?_cons_of_neg (by rw [q2]; decide), List.find?_cons_of_neg (by rw [q3]; decide),
      List.find?_cons_of_neg (by rw [q4]; decide), List.find?_cons_of_pos (by rw [q5]; decide)]
    rfl

/-- The library's own two sendings declare K1's two rounds: the library's blocks_rounds, in the two
jobs' letters. -/
theorem job_rounds (P : P14) (a : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b2.rounds = VerifiableInference.Desc.K1.rounds (jobU ⟨P, a⟩).Q ∧
      b5.rounds = VerifiableInference.Desc.K1.rounds (jobOmega ⟨P, a⟩).Q := by
  obtain ⟨sentU, hU, -, -⟩ := Desc.K14.Law.two_sendings P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, e2, -, -, e5, -⟩ := Desc.K14.Honest.blocks_rounds P sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  have eU : (jobU ⟨P, a⟩).Q = Desc.K14.parK1 P 2 "o_u and the first mask" sentU := by
    show Desc.K14.parK1 P 2 "o_u and the first mask" ((Desc.K14.withU P.S).getD #[]) = _
    rw [hU]
    rfl
  exact ⟨by rw [eU]; exact e2, e5⟩

/-- **The side that Side.seated returns at a sending's place declares what the laws on that
sending's part ask**: the place, K1's two rounds at the job's own parameters, SendDeclared. At every
number a of the round "LIN point", every row and all falls. -/
theorem seated_declares (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (a : Nat)
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall St)) :
    (∃ σ : Side St Cl V W X Pb, Side.seated xs (sendPlace 2) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 2 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU ⟨P, a⟩).Q ∧
        SendDeclared σ.block (jobU ⟨P, a⟩)) ∧
      ∃ σ : Side St Cl V W X Pb, Side.seated xs (sendPlace 5) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 5 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega ⟨P, a⟩).Q ∧
        SendDeclared σ.block (jobOmega ⟨P, a⟩) := by
  obtain ⟨⟨σ₂, h2, r2, l2⟩, ⟨σ₅, h5, r5, l5⟩⟩ := seated_send (Pb := Pb) F hb row fs
  obtain ⟨dU, pU, dO, pO⟩ := send_declares P a b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨eU, eO⟩ := job_rounds P a b1 b2 b3 b4 b5 b6 b7 b8 hb
  exact ⟨⟨σ₂, h2, r2, l2.place.trans pU, l2.rounds.trans eU,
      sendDeclared_like l2.rounds l2.oracles dU⟩,
    ⟨σ₅, h5, r5, l5.place.trans pO, l5.rounds.trans eO,
      sendDeclared_like l5.rounds l5.oracles dO⟩⟩

/-- **The same under the library's head, at the shared chain's own flat list**, carried to any type
of claims. -/
theorem seated_declares_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) (a : Nat) (row : List (Part V W X × Sim Pb))
    (fs : List (Fall St)) :
    (∃ σ : Side St Cl V W X Pb,
        Side.seated ((chainOf Zp.p.chains (qAt Zp Np) (tests Np) last).retype (Cl' := Cl)).blocksInOrder
          (sendPlace 2) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 2 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU ⟨qAt Zp Np, a⟩).Q ∧
        SendDeclared σ.block (jobU ⟨qAt Zp Np, a⟩)) ∧
      ∃ σ : Side St Cl V W X Pb,
        Side.seated ((chainOf Zp.p.chains (qAt Zp Np) (tests Np) last).retype (Cl' := Cl)).blocksInOrder
          (sendPlace 5) row fs = some σ ∧ σ.row = row ∧
        σ.block.place = sendPlace 5 ∧
        σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega ⟨qAt Zp Np, a⟩).Q ∧
        SendDeclared σ.block (jobOmega ⟨qAt Zp Np, a⟩) := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  exact seated_declares (flatOf_carried (Cl := Cl) Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (tests Np) last B.made) B.made a row fs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.seated_send
#print axioms ProofFile.Honest.K14.job_rounds
#print axioms ProofFile.Honest.K14.seated_declares
#print axioms ProofFile.Honest.K14.seated_declares_head
