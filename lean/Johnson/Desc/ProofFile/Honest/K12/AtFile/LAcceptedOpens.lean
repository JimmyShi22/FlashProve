-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LAcceptedOpens.lean: `acceptedS_of_shape`
(LShapeAccepted.lean) without two of its premises: the closing returns at zeros
(`closingOk_at_finish`, LReturnsClosing.lean), and the field `opens` at every stand
(`opens_at_thread`, LOpensAtStand.lean). A joining of laws.

  `StandLeft`            four premises at one stand
  `writtenTrees_353`, `treesTo_353`   76 trees are declared in front of member 353
  `acceptedS_of_four_at`   the joining, at every letter Said that gives `SaidOk`
  `acceptedS_of_four`    the same at `SaidOk`

The premises of `acceptedS_of_four`: those of `acceptedS_of_shape` without hClosing; hFixed, hHanded
and hBook of `opens_at_thread`; hOwn: `OwnTreesAt` (Honest/Thread/ScriptLots.lean) at member 353,
one tree, the table being table 0 of the finish's sending; hStand: `StandLeft` at every stand, at
the coins that the run's book lends the patched job's two parts there.

The four fields of `StandLeft`.
  five     the test `frontFiveB` on the shape of the record T
  say      the rows that the test takes in at T say their claims of the words of the rows that the
           sender's text returns
  agree    the two parts' coins agree (`Agree`)
  leaves   the seat's way out returns behind the block's yes

Limits.
- EVERY PREMISE IS A PREMISE. None is shown here. One stand at which a field of `StandLeft` fails
  makes hStand false, and then nothing is said.
- All limits of LShapeAccepted.lean and LOpensAtStand.lean hold here.
- In `acceptedS_of_four` hOwn stands at `SaidOk`, which says nothing of a play. So there it can be
  had of `OwnTrees` alone (`ownTreesAt_of_own`, Honest/Thread/ScriptLots.lean): at a letter whose
  table at own 76 is the finish's as a function. At a letter whose table is read off a play:
  `acceptedS_of_four_at`, at a Said that tells of the play too (by a reading). No file lays such a
  Said or shows `OwnTreesAt` at it; and such a Said owes `SaidNext` (Honest/Thread/Said.lean) at
  every member before `AcceptedS` at it joins a thread.
- hHanded and hBook at the book that the frame's maker returns: LAcceptedAtBook.lean.
- Nothing on completeness of the chain, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `acceptedS_of_four_at` and `acceptedS_of_four` bear this label;
the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. The ground of the
first: it calls `acceptedS_of_shape_at` and `opens_at_thread`, which bear it. The second calls the
first. Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeAccepted
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Block fieldPrimeWord)
open VerifiableInference.Desc.K12 (T12 enterFinish proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.K12 (TestJob frontFiveB atStand LetterAtL firstPart restPart restCoins firstRd
  Agree)
open ProofFile.Honest.Sh (testSh)
open P5J (AtMgA F0T)

variable {W₀ Rc Tr X : Type}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **Four premises at one stand.** The letters are those of `StandAsks` (LShapeAccepted.lean). -/
structure StandLeft (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (pl : K2.SwitchPlace)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (leave : S → T12 → Except String S) (s : S) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
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
  leaves : ∀ t' rs gs,
    (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).decide (J'.rec₀ m.st.input (frontOf m)) rs gs = .ok t' →
    ∃ s', leave s t' = .ok s'

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
variable {Bk : ProverCoinCounts} {Cells Tok M : Type}

set_option maxRecDepth 1000000 in
/-- By the kernel: the 353 rows in front of row 353 of the written cut have 76 trees. -/
theorem writtenTrees_353 : ((VerifiableInference.PlanWritten.cutFirstFull.map fun r =>
    (r.2.2.2.2.1.flatMap (·.2)).length).take 353).sum = 76 := by
  decide +kernel

/-- **76 trees are declared in front of member 353.** -/
theorem treesTo_353 {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D₀ r Zp Np cF) :
    treesTo cF.blocksInOrder 353 = 76 := by
  unfold treesTo
  rw [List.length_flatMap, List.map_take, ProofFile.Honest.K12.treesLens_at_head h]
  exact writtenTrees_353

/-- **The test's number of the thread is accepted, from the named premises**, at every letter Said
that gives `SaidOk`. -/
theorem acceptedS_of_four_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
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
    (hOwn : ProofFile.Honest.FirstThread.OwnTreesAt L.thread Said 353 1 fun j k w hd =>
      (pl.place, K2.switchTableAt Bk 0 (K2.coreSender K2.freshTable)
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl k w hd j))
    (hFixed : L.thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 pl k).isSome = true)
    (hBook : closingBookTest Bk pl ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true)
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
      StandLeft (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) pl
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) leave s m T J' c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS L.thread Said fl 354 :=
  acceptedS_of_shape_at h hG hf (closingOk_at_finish h hG hf) L door readers leave start fall blk
    pre t H hb hbs hfirst hStored hValid Said hSaid
    (fun k s m E T J' hJ c hT hEnter hLend =>
      have B := hStand k s m E T J' hJ c hT hEnter hLend
      have e76 : treesTo L.thread.bs 353 + 0 = 76 := by
        show treesTo L.bs 353 + 0 = 76
        rw [hbs, treesTo_353 h.toAtMg]
      have hSame := (hOwn 0 (by omega) 354 k s m E (by omega) hT).2
      ⟨B.five, B.say, B.agree,
        opens_at_thread h hG hf door readers L hbs hFixed hHanded hBook hValid hT.1
          (by rw [e76] at hSame; exact hSame) T J' hJ c hLend, B.leaves⟩) fl

/-- **The test's number of the thread is accepted, from the named premises.** -/
theorem acceptedS_of_four (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
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
    (hOwn : ProofFile.Honest.FirstThread.OwnTreesAt L.thread SaidOk 353 1 fun j k w hd =>
      (pl.place, K2.switchTableAt Bk 0 (K2.coreSender K2.freshTable)
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl k w hd j))
    (hFixed : L.thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 pl k).isSome = true)
    (hBook : closingBookTest Bk pl ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true)
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
      StandLeft (jobL (H2U.p12OfMade Zp.made) door
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) pl
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) leave s m T J' c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS L.thread SaidOk fl 354 :=
  acceptedS_of_four_at h hG hf L door readers leave start fall blk pre t H hb hbs hfirst hStored
    hValid SaidOk (fun _ _ _ e => e) hOwn hFixed hHanded hBook hStand fl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.StandLeft
#print axioms ProofFile.Honest.K12.AtProof.writtenTrees_353
#print axioms ProofFile.Honest.K12.AtProof.treesTo_353
#print axioms ProofFile.Honest.K12.AtProof.acceptedS_of_four_at
#print axioms ProofFile.Honest.K12.AtProof.acceptedS_of_four
