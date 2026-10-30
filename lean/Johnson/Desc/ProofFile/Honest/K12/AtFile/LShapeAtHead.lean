-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeAtHead.lean: the field `asks` of `FrontAtT`
(ClosingAtL.lean) under the library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`) at the planner's own
numbers of the first chain's closing proximity test and at the finish of the code switch that is
there. That the masks come early and the plan's test at one tree are paid; the 21 clauses of
`FitsAtL` follow from h5 (`fits_at_every_reached_record`).

  `asks_at_head`    the plan's test, `FrontAsksD` and `DataFront` at one plain data, at the job
                    patched at the stand with the verifier's record T

What is left, by name.
  h, hG, hf   the head; G is the blank ground; pl is the finish that `finishAt` returns there
  hReach, hEnter   s is reached at border 354, and the way into the test (`enterFinish`) returns T
            at s
  h5        five clauses on the shape of T (`frontFiveB`), at the written place
  hrows     the sender's text returns the rows R at the coins that the first stage reads
  hSay      the rows that the test takes in at T say their claims of these rows' words

By what. `p12_at_head` (Johnson/AtFull/Shape/TestNumbersAtHead.lean): the planner's numbers are the
written place. `planB_L_full` (AtFullSide/K12/RestTiesAtWL.lean). `frontAsksD_at_L`
(ClosingFront.lean), `claimsB_at_finish` (WFrontClaims.lean), `fits_at_every_reached_record`
(LSeatsLaw.lean), `dataFront_L` (ClosingData.lean).

Limits.
- h5, hrows and hSay are premises. None is shown at any state here. h5 is a test with code on the
  shape of T: it can say no.
- WHOEVER SPENDS THE CLAUSE AT A THREAD WANTS IT AT EVERY STAND (`acceptedS_at_L`, ClosingAtL.lean:
  its premise hs is over all stands). So h5, hrows and hSay are wanted at every stand. An
  evaluation at one run's record pays h5 at that record alone.
- Nothing says that a state is reached at border 354.
- The full size alone. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `asks_at_head` bears this label; the rule is at its home, the head
of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: hReach, hEnter, h5, hrows and hSay tie the
letters s, T and R to a run's coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeAsks
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LSeatsLaw
import Johnson.AtFull.Shape.TestNumbersAtHead
import AtFullSide.K12.RestTiesAtWL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Codes)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.First (Plain)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.K12 (TestCoins FrontAsksD DataFront PlainRows frontFiveB planB atStand recAtStand
  atStand_here frontAsksD_at_L)
open ProofFile.Honest.Sh (testSh)
open P5J (AtMgA)

variable {W₀ Rc Xi Tr X : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **The plan's test, `FrontAsksD` and `DataFront` at one plain data, at the job patched at the
stand with the verifier's record**: under the head, at the planner's numbers and the finish that is
there. -/
theorem asks_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (w : Local W₀ Rc Xi Tr)
    (fr : Front X) (C : TestCoins) {pI : ProofFile.InstPub} {s : S}
    (hReach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s)) {T : T12}
    (hEnter : enterFinish s = .ok T) (h5 : frontFiveB piLFull codesFull (testSh T) = true)
    {R : Johnson.Prover.Send.Rows}
    (hrows : carryRows D readers closing pl w (heardL fr) C.mem = .ok R)
    (hSay : ∀ G', T.st.groups[T.g]? = some G' →
      AllSay rdE (begun T.st T.g G') (runRows T.st G').toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G') (layoutOf T.st G')
          (plainL R ((jobL (H2U.p12OfMade Zp.made) door D readers closing pl).first w fr C)))) :
    ∃ (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (Rr : PlainRows),
      planB (atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T).p K
          Dp.ts.length = true ∧
        FrontAsksD (atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T) w fr K
          Dp ∧
        DataFront (atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T) w fr C
          Dp cc Rr := by
  have e : H2U.p12OfMade Zp.made = piLFull := Johnson.AtFull.Shape.p12_at_head h.toAtMg
  have eT : recAtStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T w fr = T :=
    atStand_here (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T
  have h5' : frontFiveB (H2U.p12OfMade Zp.made) codesFull (testSh T) = true := by
    rw [e]
    exact h5
  obtain ⟨Dp, A⟩ := frontAsksD_at_L h
    (atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T) w fr hReach hEnter eT
    (by show (H2U.p12OfMade Zp.made).early = true; rw [e]; decide) h5'
    (ProofFile.Honest.K12.AtFile.claimsB_at_finish h hReach hEnter h5')
  obtain ⟨s₁, u, Ly, H⟩ := fits_at_every_reached_record h hG hf hReach hEnter
    (atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) w fr T) w fr rfl eT A
  rw [atStand_jobL] at A H ⊢
  exact ⟨codesFull, Dp, _, _,
    planAtTrees_of_fits H (by show planB (H2U.p12OfMade Zp.made) codesFull 1 = true
                              rw [e]; exact Light.planB_L_full), A,
    dataFront_L (H2U.p12OfMade Zp.made) _ D readers closing pl w fr C hrows H
      (by rw [eT]; exact hSay)⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.asks_at_head
