-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeAsks.lean: at the first chain's closing proximity
test, the clause that asks for one table of codes, one plain data, columns and rows at which the
plan's test, `FrontAsksD` and `DataFront` hold together (the field `asks` of `FrontAtT`,
ClosingAtL.lean), at the job `jobL` patched at one stand with the verifier's record there.

  `atStand_jobL`     the job `jobL` patched at a stand is `jobL` at the patched door
  `asks_at_stand`    the clause, under the library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at the
                     record T that the way into the test (`enterFinish`) returns at a state reached
                     in front of the test

Hypotheses of `asks_at_stand`.
  h, hReach, hEnter   the head; s is reached at border 354; the way in returns T at s
  hEarly, hP   the test's parameters: the masks come early; the plan's test at one tree
  h5           five clauses on the shape of T (`frontFiveB`)
  hFits        `closingFitsAtShape` (LShapeTest.lean) at the thin shape of T
  hrows        the sender's text returns the rows R at the coins that the first stage reads
  hSay         the rows that the test takes in at T say their claims of these rows' words

The test on the open rows (`claimsB T`) is paid by `claimsB_at_finish` (WFrontClaims.lean).

Who calls it. LShapeAtHead.lean calls `atStand_jobL` alone; `asks_at_stand` has no caller.

Limits.
- hEarly, hP, h5, hFits, hrows and hSay are premises. None is shown at any state here.
- WHOEVER SPENDS THE CLAUSE AT A THREAD WANTS IT AT EVERY STAND (`acceptedS_at_L`, ClosingAtL.lean:
  its premise hs is over all stands). So h5, hFits, hrows and hSay are wanted at every stand: one
  stand at which one of them fails makes that premise false.
- Nothing says that a state is reached at border 354.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `asks_at_stand` bears this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: hReach, hEnter, h5, hFits, hrows and
hSay tie the letters s, T and R to a run's coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeFront
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingFront
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontClaims
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Codes)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12 T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.First (Plain)
open H2K.Member (codesFull)
open ProofFile.Honest.K12 (TestCoins FrontAsksD DataFront PlainRows frontFiveB planB atStand
  recAtStand atStand_here frontAsksD_at_L)
open ProofFile.Honest.Sh (testSh thinOf)
open P5J (AtMgA)

variable {W₀ Rc Xi Tr X : Type}

/-- **The job patched at a stand is the job at the patched door.** -/
theorem atStand_jobL (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (w : Local W₀ Rc Xi Tr) (fr : Front X) (T : T12) :
    atStand (jobL q door D readers closing p) w fr T =
      jobL q (recAtStand (jobL q door D readers closing p) w fr T) D readers closing p := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **The plan's test, `FrontAsksD` and `DataFront` at one plain data, at the job patched at the
stand with the verifier's record.** -/
theorem asks_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) (q : P12)
    (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (w : Local W₀ Rc Xi Tr) (fr : Front X) (C : TestCoins) {pI : ProofFile.InstPub} {s : S}
    (hReach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s)) {T : T12}
    (hEnter : enterFinish s = .ok T) (hEarly : q.early = true) (hP : planB q codesFull 1 = true)
    (h5 : frontFiveB q codesFull (testSh T) = true)
    (hFits : closingFitsAtShape q p (thinOf (testSh T)) = true)
    {R : Johnson.Prover.Send.Rows}
    (hrows : carryRows D readers closing p w (heardL fr) C.mem = .ok R)
    (hSay : ∀ G, T.st.groups[T.g]? = some G →
      AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G)
          (plainL R ((jobL q door D readers closing p).first w fr C)))) :
    ∃ (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (Rr : PlainRows),
      planB (atStand (jobL q door D readers closing p) w fr T).p K Dp.ts.length = true ∧
        FrontAsksD (atStand (jobL q door D readers closing p) w fr T) w fr K Dp ∧
        DataFront (atStand (jobL q door D readers closing p) w fr T) w fr C Dp cc Rr := by
  have e : recAtStand (jobL q door D readers closing p) w fr T w fr = T :=
    atStand_here (jobL q door D readers closing p) w fr T
  obtain ⟨Dp, S⟩ := frontAsksD_at_L h (atStand (jobL q door D readers closing p) w fr T) w fr hReach
    hEnter e hEarly h5 (ProofFile.Honest.K12.AtFile.claimsB_at_finish h hReach hEnter h5)
  rw [atStand_jobL] at S ⊢
  obtain ⟨cc, Rr, H⟩ := asks_of_shape q (recAtStand (jobL q door D readers closing p) w fr T) D
    readers closing p w fr C codesFull Dp (by rw [e]; exact hFits) hP S hrows
    (by rw [e]; exact hSay)
  exact ⟨codesFull, Dp, cc, Rr, H⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.atStand_jobL
#print axioms ProofFile.Honest.K12.AtProof.asks_at_stand
