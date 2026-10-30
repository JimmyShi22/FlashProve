-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeAccepted.lean: the first chain's closing proximity
test is accepted along the thread (`AcceptedS`, Honest/Thread/PaysS.lean, at number 354 and the
letter `SaidOk`), under the library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at the job `jobL` with
the letters at which the wider filling lays it (`proxLotOf`, Honest/AtPureWiderK12.lean), FROM NAMED
PREMISES. A joining of laws: `acceptedS_at_L` (ClosingAtL.lean), `frontAtT_of_shape`
(LShapeSpender.lean), `carryRows_returns_at_stand` (LReturnsAtHead.lean), `reach_below`
(Honest/Thread/SaidOk.lean).

  `StandAsks`            five premises at one stand: at the record T that the way into the test
                         returns there, the patched job J', the coins c
  `roundsCount_written`  a closed line: at the written place the stages' count of rounds is the
                         block's
  `acceptedS_of_shape_at`   the joining, at every letter Said that gives `SaidOk`
  `acceptedS_of_shape`   the same at `SaidOk`

The premises of `acceptedS_of_shape`.
  h, hG, hf     the head; G is the blank ground; pl is the finish that `finishAt` returns there
  hClosing      the closing returns at zeros at pl (`K2.closingOk`): a test with code on public data
  H, hb         the thread's letters at the test (`LetterAtL`), and its member number 354
  hbs, hfirst   the thread's list is the head's chain; its first state is the description's
  hStored       the words of the thread's stored columns are below the field's prime
  hValid        the thread's valid inputs pass the description's test on the instance
  hStand        `StandAsks` at every stand, at the coins c that the run's book lends the patched
                job's two parts there
Three fields of `FrontAtT` that read the test's parameters alone (planOk, form, count) follow
inside, at the written place: `closed_LFull`, `formPubB_L` (AtFullSide/K12/FirstAnyAtHeadL.lean) and
the closed line `roundsCount_written` here.

Limits.
- EVERY PREMISE IS A PREMISE. None is shown here. `StandAsks` is asked at every stand of the thread
  at number 354: one stand at which a field of it fails makes hStand false, and then nothing is
  said.
- The field `five` of `StandAsks` is a test with code on the shape of T. It is evaluated at no shape
  here.
- `AcceptedS` holds emptily at a thread that never stands at number 354.
- "Accepted" is the thread's step at this one member. Nothing on the other members.
- At the sizes `Sz.ref` alone. The full size; the format's second hash function.
- Nothing on completeness of the chain, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `acceptedS_of_shape_at` and `acceptedS_of_shape` bear this label;
the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. The ground of the
first: it calls `acceptedS_at_L`, which bears it; the thread from `ThrS` as a premise of hStand,
`AcceptedS` as the end; hValid is on the letter for "valid". The second calls the first.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeSpender
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LReturnsAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import AtFullSide.K12.FirstAnyAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Block fieldPrimeWord)
open VerifiableInference.Desc.K12 (T12 enterFinish proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.K12 (TestJob frontFiveB atStand FrontAtT LetterAtL acceptedS_at_L
  firstPart restPart restCoins firstRd Agree OpensFit OldAt formPubB termLen)
open ProofFile.Honest.Sh (testSh)
open P5J (AtMgA F0T)

variable {W₀ Rc Tr X : Type}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **Five premises at one stand.** J: the job. pl: the sender's place. D, readers, closing: the
sender's letters. leave: the seat's way out. s, m, E: the stand. T: the verifier's record there.
J': the job patched there. c: the coins lent to its two parts. -/
structure StandAsks (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (pl : K2.SwitchPlace)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (leave : S → T12 → Except String S) (s : S) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env)
    (T : T12) (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
      restPart J']) : Prop where
  five : frontFiveB piLFull codesFull (testSh T) = true
  say : ∀ R, carryRows D readers closing pl m.st.input (heardL (frontOf m))
      (restCoins J' c.2.1).mem = .ok R →
    ∀ G', T.st.groups[T.g]? = some G' →
      AllSay rdE (begun T.st T.g G') (runRows T.st G').toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G') (layoutOf T.st G')
          (plainL R (J.first m.st.input (frontOf m) (restCoins J' c.2.1))))
  agree : Agree J' m.st.input (frontOf m) J'.s₀ (firstRd J' c.1) (restCoins J' c.2.1)
  opens : ∃ depths src₀,
    (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
      (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).map (·.1) = depths ∧
    OpensFit J' (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
      (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) src₀
  leaves : ∀ t' rs gs,
    (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).decide (J'.rec₀ m.st.input (frontOf m)) rs gs = .ok t' →
    ∃ s', leave s t' = .ok s'

set_option maxRecDepth 100000 in
/-- At the written place the stages' count of rounds is the block's. -/
theorem roundsCount_written :
    termLen piLFull.nums.stages = (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds.length := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
variable {Bk : ProverCoinCounts} {Cells Tok M : Type}

/-- **The test's number of the thread is accepted, from the named premises**, at every letter Said
that gives `SaidOk`. -/
theorem acceptedS_of_shape_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
    (hClosing : K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub Cells Tok M)
    (door : Local W₀ Rc ProofFile.Inst Tr → Front X → T12)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (leave : S → T12 → Except String S)
    (start : Local W₀ Rc ProofFile.Inst Tr → S) (fall : T12) (blk : Block S ProofFile.Cl)
    (pre t : List (Block S ProofFile.Cl))
    (H : LetterAtL L 354 (jobL (H2U.p12OfMade Zp.made) door
      (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) leave start fall blk pre t)
    (hb : L.thread.bs[354]? = some blk) (hbs : L.bs = cF.blocksInOrder) (hfirst : L.first = ProofFile.startS Zp)
    (hStored : ∀ w i y u, L.stored w i y = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hStand : ∀ k s m E T (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X),
      J' = atStand (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) m.st.input (frontOf m) T →
      ∀ c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart J'],
      ThrS L.thread Said 354 k s m E → enterFinish s = .ok T →
      lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) J'.p.place
        [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
          restPart J'] 0 = .ok c →
      StandAsks (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) pl
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) leave s m E T J' c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS L.thread Said fl 354 := by
  refine acceptedS_at_L H hb Said (fun k s m E T J' hJ c hT hEnter hLend => ?_) fl
  have A := hStand k s m E T J' hJ c hT hEnter hLend
  have hlen : 354 ≤ L.thread.bs.length := by
    have e := (List.getElem?_eq_some_iff.1 hb).1
    exact Nat.le_of_lt e
  have hReach := reach_below L.thread L.first (L.pubOf m.st.input.x) hlen (fun _ e => e) hStored
    ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hReach' : Johnson.Desc.First.Walk.Tied.Reach 0
      (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) 354
      (L.pubOf m.st.input.x, s) := by
    rw [← hbs, ← hfirst]
    exact hReach
  obtain ⟨R, hR⟩ := carryRows_returns_at_stand h hG hf hClosing readers L hValid hT.1
    (heardL (frontOf m)) (restCoins J' c.2.1).mem
  have e : J'.p = piLFull := by
    rw [hJ]
    exact Johnson.AtFull.Shape.p12_at_head h.toAtMg
  exact frontAtT_of_shape h hG hf door _ readers _ leave m E hReach' hEnter J' hJ c A.five
    hR (A.say R hR) A.agree A.opens
    (by rw [e]; exact VerifiableInference.Desc.K12.Coin.At.closed_LFull.plan)
    (by rw [e]; exact Light.formPubB_L) (by rw [e]; exact roundsCount_written) A.leaves

/-- **The test's number of the thread is accepted, from the named premises.** -/
theorem acceptedS_of_shape (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
    (hClosing : K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub Cells Tok M)
    (door : Local W₀ Rc ProofFile.Inst Tr → Front X → T12)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (leave : S → T12 → Except String S)
    (start : Local W₀ Rc ProofFile.Inst Tr → S) (fall : T12) (blk : Block S ProofFile.Cl)
    (pre t : List (Block S ProofFile.Cl))
    (H : LetterAtL L 354 (jobL (H2U.p12OfMade Zp.made) door
      (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) leave start fall blk pre t)
    (hb : L.thread.bs[354]? = some blk) (hbs : L.bs = cF.blocksInOrder) (hfirst : L.first = ProofFile.startS Zp)
    (hStored : ∀ w i y u, L.stored w i y = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (hStand : ∀ k s m E T (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X),
      J' = atStand (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) m.st.input (frontOf m) T →
      ∀ c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart J'],
      ThrS L.thread SaidOk 354 k s m E → enterFinish s = .ok T →
      lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) J'.p.place
        [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
          restPart J'] 0 = .ok c →
      StandAsks (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) pl
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) leave s m E T J' c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS L.thread SaidOk fl 354 :=
  acceptedS_of_shape_at h hG hf hClosing L door readers leave start fall blk pre t H hb hbs hfirst
    hStored hValid SaidOk (fun _ _ _ e => e) hStand fl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.StandAsks
#print axioms ProofFile.Honest.K12.AtProof.roundsCount_written
#print axioms ProofFile.Honest.K12.AtProof.acceptedS_of_shape_at
#print axioms ProofFile.Honest.K12.AtProof.acceptedS_of_shape
