-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WAccepted.lean: the two debts of the last chain's proximity test
in the frame's form: `PlaysS` and `AcceptedS` (Thread/PaysS.lean), at that test's number of a last
chain's thread at the library's description, general in the thread's letters and in what is said of
the run, each premise under its name.

  `LetterAtW`     what the thread's letters owe, no run named: where the block stands, its seat, the
                  half behind the guard at its place, the job's door, the thread's first tree, the
                  rounds in front, what it takes over, that it has sent no tree in front
  `StandAtW`      what a stand owes, each under its name
  `enters_at_W`   the way in returns the job's state on entry
  `acceptedS_at_W`, `playsS_at_W`   the two debts

The clauses of `StandAtW`.
  `field`   the letter on the field (`EndsAre`, WDoor.lean): what is handed to the door: the field
            holds the two earlier chains' columns and then the columns in front, and the chain began
            at the start's state at those chains' ends
  `taken`   the job's three trees are the tables taken over (`TakenIs`, WAtHead.lean)
  `lines`   the three public tests on the shape (`linesB`, WStand.lean). By `frontFive_of_own`
            (WShape.lean) `frontFiveB` is a function of the first chain's last record's shape
  `front`   the hypotheses of the front (`FrontAsksD`): `front_of_ends` (WEnds.lean) pays it from
            what the two earlier chains hand over
  `saysAt`  what the rows taken in say of the words (`SaysAt`, K12/AsksWhole.lean)
  `old`, `trees`   the plan's two clauses of «it plays»: the taken trees have the declared widths, and
            the test's new trees are the thread's tables (`trees_of_thr`)

Can a clause be false or empty. Each of the clauses reads a stand. `saysAt` is false at a stand whose
witness is not the job's rows. `field` cannot hold where the field is none. Where no stand of the
thread exists at number b both sentences are idle: a stand is a premise here. `lines` and
`front` were seen at no run of this test.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, `AcceptedS` and `PlaysS` their
  ends.
- AT THE FILLING, NOT READ THROUGH: a half read through a reader of the coins is no `proverSideOfProximityTest`; these
  statements stand at the base prover, and the crossing to the term is `runC_thru`'s.
- `enter` is a letter here; at the description it is the seat's way in, which returns at every state.
- Nothing on completeness of the whole chain, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block OpenedColumn FileDescription)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (proofSendsFull)
open H2K.Member (codesFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K12.AtProof (fourOf placeW)
open ProofFile.Honest.K12.Light (ManyJob doorW SaysAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
variable {Xi W₀ Rc Tr X V Pb : Type} {Bk : ProverCoinCounts}

/-- **What the thread's letters owe, no run named.** F: the description. T: the last chain's thread.
b: the test's number. A: the job. enter, leave: the seat's way in and way out. blk: the block. fall:
the door's default. -/
structure LetterAtW (F : FileDescription Xi) (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb) (b : ℕ)
    (A : ManyJob (Local W₀ Rc Xi Tr) X) (enter : F.S₃ → Except String T12)
    (leave : F.S₃ → T12 → Except String F.S₃) (blk : Block F.S₃ F.Cl) (fall : T12) : Prop where
  member : T.bs[b]? = some blk
  seat : SeatOf blk A.toRun.toTest enter leave
  half : (T.hs.find? fun g => g.place == blk.place) =
    some (proverSideOfProximityTest A.toRun.toTest : Placed V (Local W₀ Rc Xi Tr) X).needsField
  door : A.rec₀ = doorW F (·.x) enter placeW fall
  ft : T.ft = F.lastChainFirstTreeNumber
  front : T.front = (F.first.blocksInOrder.flatMap (·.rounds)).length +
    (F.shared.blocksInOrder.flatMap (·.rounds)).length
  cut : T.bs.take b = F.second.blocksInOrder.takeWhile (·.place != placeW)
  taken : T.taken = takenLast
  sent : treesTo T.bs b = 0
  returns : ∀ s, ∃ R, enter s = .ok R
  leaves : ∀ s t, ∃ s', leave s t = .ok s'

/-- **What a stand owes of the field**: what the letter on the field gives at the thread's own tables,
and that the chain began at the start's state at the two ends. -/
def FieldAtW (F : FileDescription Xi) (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : ℕ) : Prop :=
  ∀ k st m E, ThrS T Said b k st m E → ∃ base cols e₁ e₂, EndsAre F m base e₁ e₂ ∧
    T.colsTo b m E = .ok cols ∧ m.opened = some (base ++ cols) ∧
    ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      F.start₃ (F.pub m.st.input.x) e₁ e₂ = .ok s₀

/-- **What a stand owes.** -/
structure StandAtW (F : FileDescription Xi) (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : ℕ)
    (A : ManyJob (Local W₀ Rc Xi Tr) X) : Prop where
  field : FieldAtW F T Said b
  taken : ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest :
      Part V (Local W₀ Rc Xi Tr) X), restPart A.toRun.toTest]),
    ThrS T Said b k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part V (Local W₀ Rc Xi Tr) X), restPart A.toRun.toTest] 0 =
        .ok c →
    ∀ i (hi : i < takenLast.length), TakenIs T k m
      (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
        (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
      i takenLast[i]
  lines : ∀ k st m E, ThrS T Said b k st m E →
    linesB A codesFull 3 (testSh (A.rec₀ m.st.input (frontOf m))) = true
  front : ∀ k st m E, ThrS T Said b k st m E →
    ∃ Dp, FrontAsksD A.toRun.toTest m.st.input (frontOf m) codesFull Dp
  saysAt : ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest :
      Part V (Local W₀ Rc Xi Tr) X), restPart A.toRun.toTest]),
    ThrS T Said b k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part V (Local W₀ Rc Xi Tr) X), restPart A.toRun.toTest] 0 =
        .ok c →
    SaysAt A m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)
  old : ∀ k st m E, ThrS T Said b k st m E →
    ∀ d ∈ (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
      ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W
  trees : ∀ blk, T.bs[b]? = some blk → ∀ k st m E ds y cols, ThrS T Said b k st m E →
    drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
    T.Trees (T.fresh b) k y.2 (E.add y.1)

variable {F : FileDescription Xi} {T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb} {b : ℕ}
  {A : ManyJob (Local W₀ Rc Xi Tr) X} {enter : F.S₃ → Except String T12}
  {leave : F.S₃ → T12 → Except String F.S₃} {blk : Block F.S₃ F.Cl} {fall : T12}
  {Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-- **At a stand the way in returns the job's state on entry, and the field is there.** -/
theorem enters_at_W (H : LetterAtW F T b A enter leave blk fall) (hF : FieldAtW F T Said b)
    {k : Coins Bk} {st : F.S₃} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (u : ThrS T Said b k st m E) :
    enter st = .ok (A.rec₀ m.st.input (frontOf m)) ∧ m.opened.isSome = true := by
  obtain ⟨base, cols, e₁, e₂, hE, hc, ho, hs⟩ := hF k st m E u
  obtain ⟨R, hR⟩ := H.returns st
  have hM : T.Made b k st m E := by
    obtain ⟨⟨-, -, -, -, hM, -, -⟩, -⟩ := u
    exact hM
  have d := door_at_made T enter placeW H.ft H.front H.cut hM hE hc ho hs
  refine ⟨?_, by rw [ho]; rfl⟩
  rw [H.door, door_value enter placeW fall m d hR]
  exact hR

/-- **The test's number of the thread is accepted, from the pair, at every letter for a fall.** -/
theorem acceptedS_at_W (h : P5J.AtMg o Z D r Zp Np cF)
    (H : LetterAtW F T b A enter leave blk fall) (S : StandAtW F T Said b A)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (hp : A.p = (fourOf Np).W) (f : Addr × ℕ) (hfr : A.fresh = some f) (hl : A.mems.length = 3)
    (hd : A.trees.map (·.1) = [13, 22, 22]) (fl : ℕ → F.S₃ → List Fmt.Drawn → Option String) :
    AcceptedS T Said fl b := by
  have hn : A.fresh.isNone = false := by
    rw [hfr]
    rfl
  obtain ⟨hP, hF, hpl, he, hcount, s, t, rest, hst, hk, -⟩ := public_head_W h A hp hn
  exact acceptedS_at_group T Said H.member A codesFull enter leave H.seat s t rest hst hk H.half
    (fun k st m E u => (enters_at_W H S.field u).2) hP hF hpl he hcount H.leaves fl
    fun k st m E c u hc =>
      { agree := agree_head_W h hB A hp f hfr hl _ _ c hc _ _
        opens := opens_at_own h T A hp hn hd H.taken H.sent u.1 _ _ (S.taken k st m E c u hc)
        enters := (enters_at_W H S.field u).1
        lines := S.lines k st m E u
        front := S.front k st m E u
        saysAt := S.saysAt k st m E c u hc }

/-- **The test's number of the thread plays, and its new trees are the thread's tables.** -/
theorem playsS_at_W (h : P5J.AtMg o Z D r Zp Np cF)
    (H : LetterAtW F T b A enter leave blk fall) (hF : FieldAtW F T Said b)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (hp : A.p = (fourOf Np).W) (f : Addr × ℕ) (hfr : A.fresh = some f) (hl : A.mems.length = 3)
    (hold : ∀ k st m E, ThrS T Said b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
        ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hT : ∀ blk, T.bs[b]? = some blk → ∀ k st m E ds y cols, ThrS T Said b k st m E →
      drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    PlaysS T Said b := by
  have hn : A.fresh.isNone = false := by
    rw [hfr]
    rfl
  obtain ⟨-, -, -, -, -, s, t, rest, hst, hk, P⟩ := public_head_W h A hp hn
  exact playsS_at_group T Said H.member A.toRun.toTest enter leave H.seat s t rest hst hk H.half
    (fun k st m E u => (enters_at_W H hF u).2) 0 P H.sent
    (fun k st m E c u hc => agree_head_W h hB A hp f hfr hl _ _ c hc _ _) hold
    fun k st m E ds y cols u hd hM => hT blk H.member k st m E ds y cols u hd hM

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.LetterAtW
#print axioms ProofFile.Honest.K12.AtFile.FieldAtW
#print axioms ProofFile.Honest.K12.AtFile.StandAtW
#print axioms ProofFile.Honest.K12.AtFile.enters_at_W
#print axioms ProofFile.Honest.K12.AtFile.acceptedS_at_W
#print axioms ProofFile.Honest.K12.AtFile.playsS_at_W
