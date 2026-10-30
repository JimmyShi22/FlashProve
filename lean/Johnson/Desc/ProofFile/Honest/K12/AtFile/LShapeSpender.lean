-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeSpender.lean: `asks_at_head` (LShapeAtHead.lean) in
the letters of its spender: `FrontAtT` (ClosingAtL.lean), what `acceptedS_at_L` asks at each stand
of the first chain's thread at the closing proximity test, at the job patched there.

  `frontAtT_asks_of_shape`   the field `asks` of `FrontAtT`, at a job J' that is `jobL` patched at
                               the stand m with the verifier's record T, at the coins c lent to J'
  `frontAtT_of_shape`          `FrontAtT` whole, its six other fields handed in

Hypotheses. Those of `asks_at_head`, at the input `m.st.input`, the front `frontOf m` and the coins
`restCoins J' c.2.1`; hJ: J' is the patched job. In `frontAtT_of_shape` besides: the fields agree,
opens, planOk, form, count and leaves of `FrontAtT`, each in its own words.

Limits.
- All limits of LShapeAtHead.lean hold here. h5, hrows and hSay are premises, and the spender wants
  them at every stand.
- That the thread's job is a `jobL`, and that the state at a stand is reached at border 354, are the
  caller's.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: both theorems bear this label; the rule is at its home, the head
of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: hReach, hEnter, h5, hrows, hSay and the
fields handed in tie the letters s, m, E, T, R and c to a run's coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingAtL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Codes)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K12 (T12 enterFinish proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.First (Plain)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.K12 (TestJob FrontAsksD DataFront PlainRows frontFiveB planB atStand FrontAtT
  firstPart restPart restCoins firstRd Agree OpensFit OldAt formPubB termLen)
open ProofFile.Honest.Sh (testSh)
open P5J (AtMgA)

variable {W₀ Rc Xi Tr X : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **The field `asks` of `FrontAtT`, in its own letters.** -/
theorem frontAtT_asks_of_shape (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (m : Mid (Local W₀ Rc Xi Tr) X) {pI : ProofFile.InstPub} {s : S}
    (hReach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s)) {T : T12}
    (hEnter : enterFinish s = .ok T) (J' : TestJob (Local W₀ Rc Xi Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) m.st.input
      (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'])
    (h5 : frontFiveB piLFull codesFull (testSh T) = true)
    {R : Johnson.Prover.Send.Rows}
    (hrows : carryRows D readers closing pl m.st.input (heardL (frontOf m))
      (restCoins J' c.2.1).mem = .ok R)
    (hSay : ∀ G', T.st.groups[T.g]? = some G' →
      AllSay rdE (begun T.st T.g G') (runRows T.st G').toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G') (layoutOf T.st G')
          (plainL R ((jobL (H2U.p12OfMade Zp.made) door D readers closing pl).first m.st.input
            (frontOf m) (restCoins J' c.2.1))))) :
    ∃ (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (Rr : PlainRows),
      planB J'.p K Dp.ts.length = true ∧ FrontAsksD J' m.st.input (frontOf m) K Dp ∧
        DataFront J' m.st.input (frontOf m) (restCoins J' c.2.1) Dp cc Rr := by
  subst hJ
  exact asks_at_head h hG hf door D readers closing m.st.input (frontOf m) _ hReach hEnter h5 hrows
    hSay

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **`FrontAtT` whole**, its six other fields handed in. -/
theorem frontAtT_of_shape (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (leave : S → T12 → Except String S) (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env)
    {pI : ProofFile.InstPub} {s : S}
    (hReach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s)) {T : T12}
    (hEnter : enterFinish s = .ok T) (J' : TestJob (Local W₀ Rc Xi Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) m.st.input
      (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'])
    (h5 : frontFiveB piLFull codesFull (testSh T) = true)
    {R : Johnson.Prover.Send.Rows}
    (hrows : carryRows D readers closing pl m.st.input (heardL (frontOf m))
      (restCoins J' c.2.1).mem = .ok R)
    (hSay : ∀ G', T.st.groups[T.g]? = some G' →
      AllSay rdE (begun T.st T.g G') (runRows T.st G').toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G') (layoutOf T.st G')
          (plainL R ((jobL (H2U.p12OfMade Zp.made) door D readers closing pl).first m.st.input
            (frontOf m) (restCoins J' c.2.1)))))
    (agree : Agree J' m.st.input (frontOf m) J'.s₀ (firstRd J' c.1) (restCoins J' c.2.1))
    (opens : ∃ depths src₀,
      (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).map (·.1) = depths ∧
      OpensFit J' (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) src₀)
    (planOk : (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).planOk = true) (form : formPubB J'.p = true)
    (count : termLen J'.p.nums.stages = (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds.length)
    (leaves : ∀ t' rs gs,
      (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).decide (J'.rec₀ m.st.input (frontOf m)) rs gs = .ok t' →
      ∃ s', leave s t' = .ok s') : FrontAtT J' leave s m E c :=
  { agree := agree, opens := opens, planOk := planOk, form := form, count := count
    asks := frontAtT_asks_of_shape h hG hf door D readers closing m hReach hEnter J' hJ c h5
      hrows hSay
    leaves := leaves }

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.frontAtT_asks_of_shape
#print axioms ProofFile.Honest.K12.AtProof.frontAtT_of_shape
