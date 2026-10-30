-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WStand.lean: the frame's sentences «it plays» and «it is
accepted» (`PlaysS`, `AcceptedS`, Honest/Thread/PaysS.lean) at a member at which a proximity test on a
group of several members stands behind the guard (`Placed.needsField`, K12/FieldGuard.lean), at a
state on entry whose rows are dense. General in the thread, the letter, the job and the falls: the
last chain's test is its one use at the proof file.

  `dataThree_of_frontD`  the first three clauses of `DataFront` at the job's own rows and columns:
                   `dataThree_of_front` (K12/ManyFitsAt.lean) at `FrontAsksD`
  `linesB`         the three public tests on the shape in front of the test, as one Bool
  `accepts_at_own` the decision accepts what the term shows, from the plan's half, the lines,
                   `FrontAsksD` and `SaysAt`
  `OwnStand`       what is asked at a stand, each under its name
  `k12At_of_own`   `K12At` at every list that the block's rounds can sample
  `acceptedS_at_group`, `playsS_at_group`   the two sentences

The premise hop. A half behind the guard errs at its first move where the field `opened` is none. hop
asks the field of the pair, not of the letter alone: the letter says what the field holds at the
tables at which `Thread.Hand` holds, and the pair holds such tables.

By what. `ts_of_frontD` (K12/AsksAtHeadDense.lean);
`accepts_every_roundsD` (ClosingStand.lean); `saysYes_seat`, `saysYes_guarded`, `playsOn_k12`,
`playsOn_guarded`; `acceptedS_of_saysYes`, `old_of_hand` (AcceptedAtTest.lean, PlaysAtTest.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each statement on a thread has the thread's pair as a premise and a
  sentence of the frame as its end.
- `OwnStand` is asked; no thread is shown to meet it here. A theorem with a false premise says
  nothing.
- The number of trees is 3, as the last chain's test opens.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtTest
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHeadDense
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShapeDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes (Codes)
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.First (Plain logAt)
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TestSh testSh thinOf)
open ProofFile.Honest.K12.Light (ManyJob colsMany plainMany manyFitsS many_of_S dataThree_many tsLenOf
  ts_of_frontD SaysAt)

variable {W X : Type}

/-- **The first three clauses of `DataFront`, at `FrontAsksD`'s plain data.** -/
theorem dataThree_of_frontD (A : ManyJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : A.p.early = true) (h5 : frontFiveB A.p K (testSh (A.rec₀ w fr)) = true)
    (S : FrontAsksD A.toRun.toTest w fr K Dp)
    (hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees (thinOf (testSh (A.rec₀ w fr))) = true)
    (C : TestCoins) :
    ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
      StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
      A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
        groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  unfold frontFiveB at h5
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, -⟩, -⟩ := h5
  rw [ProofFile.Honest.Sh.thinOf_eq] at hS
  have hp : (A.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (A.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (A.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  have hc : ProofFile.Honest.Sh.claimsB (A.rec₀ w fr) = true := S.claims
  unfold ProofFile.Honest.Sh.claimsB at hc
  cases hG : (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G =>
    exact dataThree_many A Dp (many_of_S A.p _ _ _ hp he hS G hG Dp (S.plain G hG).1) w fr C

/-- **The three public tests on the shape in front of the test.** N: the shape. n: the trees that the
first switch opens. -/
def linesB (A : ManyJob W X) (K : Codes) (n : ℕ) (N : TestSh) : Bool :=
  frontFiveB A.p K N && manyFitsS A.p (A.mems.map (·.shape)) A.trees (thinOf N) &&
    decide (tsLenOf A.p (thinOf N) = n)

/-- **The decision accepts what the term shows**, at every list that can be sampled. -/
theorem accepts_at_own (A : ManyJob W X) (K : Codes) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) (hP : planB A.p K 3 = true) (hF : formPubB A.p = true)
    (hp : (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).planOk = true) (he : A.p.early = true)
    (hl : linesB A K 3 (testSh (A.rec₀ w fr)) = true)
    (hA : ∃ Dp, FrontAsksD A.toRun.toTest w fr K Dp) (hs : SaysAt A w fr C)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).decide (A.rec₀ w fr)
      ((testAll A.toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll A.toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  unfold linesB at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨h5, hm⟩, hn⟩ := hl
  obtain ⟨Dp, S⟩ := hA
  obtain ⟨t1, t2, t3⟩ := dataThree_of_frontD A w fr K Dp he h5 S hm C
  have hts : Dp.ts.length = 3 := by
    rw [ts_of_frontD A.toRun.toTest w fr K Dp he h5 S]
    exact hn
  have hP' : planB A.toRun.toTest.p K Dp.ts.length = true := by
    rw [hts]
    exact hP
  exact accepts_every_roundsD A.toRun.toTest w fr C K Dp _ _ hP' hF hp S ⟨t1, t2, t3, hs⟩ ds hd

section
variable {S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **What is asked at a stand; no challenge of the test is named.** -/
structure OwnStand (A : ManyJob W X) (K : Codes) (enter : S → Except String T12) (st : S)
    (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest]) : Prop where
  agree : Agree A.toRun.toTest m.st.input (frontOf m) A.toRun.toTest.s₀
    (firstRd A.toRun.toTest c.1) (restCoins A.toRun.toTest c.2.1)
  opens : ∃ depths src₀,
    (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1))).map (·.1) =
        depths ∧
    OpensFit A.toRun.toTest (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1))) src₀
  enters : enter st = .ok (A.rec₀ m.st.input (frontOf m))
  lines : linesB A K 3 (testSh (A.rec₀ m.st.input (frontOf m))) = true
  front : ∃ Dp, FrontAsksD A.toRun.toTest m.st.input (frontOf m) K Dp
  saysAt : SaysAt A m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)

/-- **`K12At` at every list that the block's rounds can sample.** -/
theorem k12At_of_own (A : ManyJob W X) (K : Codes) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (st : S) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hP : planB A.p K 3 = true) (hF : formPubB A.p = true)
    (hp : (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).planOk = true) (he : A.p.early = true)
    (hcount : termLen A.p.nums.stages = (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds.length)
    (hleave : ∀ t', ∃ s', leave st t' = .ok s')
    (h : OwnStand A K enter st m E c) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true) :
    K12At A.toRun.toTest enter leave st m E ds c := by
  obtain ⟨t', ht'⟩ := accepts_at_own A K m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1) ds
    hP hF hp he h.lines h.front h.saysAt hd
  exact ⟨h.agree, (length_test A.toRun.toTest _ _ _ _).trans hcount, h.opens, h.enters, t', ht',
    hleave t'⟩

variable {V' : Type}

/-- **It is accepted, behind the guard.** hop: the field is there at a stand. HS: what is asked at a
stand, at the coins that the frame lends. -/
theorem acceptedS_at_group (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (A : ManyJob W X) (K : Codes)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk A.toRun.toTest enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : A.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest A.toRun.toTest : Placed V W X).needsField)
    (hop : ∀ k st m E, ThrS T Said b k st m E → m.opened.isSome = true)
    (hP : planB A.p K 3 = true) (hF : formPubB A.p = true)
    (hp : (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).planOk = true) (he : A.p.early = true)
    (hcount : termLen A.p.nums.stages = (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds.length)
    (hleave : ∀ st t', ∃ s', leave st t' = .ok s')
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (HS : ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest : Part V W X),
        restPart A.toRun.toTest]),
      ThrS T Said b k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
        [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c →
      OwnStand A K enter st m E c) :
    AcceptedS T Said fall b := by
  have f1 : ([(proverSideOfProximityTest A.toRun.toTest : Placed V W X)].find? fun g =>
      g.place == A.toRun.toTest.p.place) = some (proverSideOfProximityTest A.toRun.toTest) := by
    have e : ((proverSideOfProximityTest A.toRun.toTest : Placed V W X).place == A.toRun.toTest.p.place) = true :=
      beq_self_eq_true _
    simp [List.find?, e]
  have f2 : ([(proverSideOfProximityTest A.toRun.toTest : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest A.toRun.toTest) := by
    rw [hseat.place]
    exact f1
  exact acceptedS_of_saysYes T Said hblk
    (saysYes_guarded (hs := T.hs) (proverSideOfProximityTest A.toRun.toTest) hf f2 hop
      (saysYes_seat T.φ Bk T.chain T.ft [proverSideOfProximityTest A.toRun.toTest] blk A.toRun.toTest enter leave
        hseat (fall b) (ThrS T Said b) s t rest hst hk f1
        fun k st m E ds c u hd _ hc =>
          k12At_of_own A K enter leave st m E c hP hF hp he hcount (hleave st)
            (HS k st m E c u hc) ds hd)) fun _ _ h => h

/-- **It plays, behind the guard, and its new trees are the thread's tables.** -/
theorem playsS_at_group (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hop : ∀ k st m E, ThrS T Said b k st m E → m.opened.isSome = true) (sent : ℕ)
    (P : PlanPlays J s (t :: rest) sent) (hsent : treesTo T.bs b = sent)
    (hA : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1))
    (hold : ∀ k st m E, ThrS T Said b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
        ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hT : ∀ k st m E ds y cols, ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    PlaysS T Said b := by
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J) := by
    have e : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := beq_self_eq_true _
    simp [List.find?, e]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J) := by
    rw [hseat.place]
    exact f1
  have P0 : PlaysOn T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk (ThrS T Said b) (fun _ _ _ _ => True) :=
    playsOn_k12 T.φ Bk T.chain T.ft _ blk J enter leave hseat _ _ s t rest hst hk f1 sent P
      (fun k st m E _ c u _ hc =>
        ⟨hA k st m E c u hc, by
          obtain ⟨⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩, -⟩ := u
          rw [h3, hsent], hold k st m E u⟩)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  have P1 := playsOn_guarded (hs := T.hs) (proverSideOfProximityTest J) hf f2 hop P0
  intro blk' hblk' k st m E ds l u hd hs hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hy, hc, -⟩ := P1 k st m E ds l u hd hs hl
  have hMv : T.Moved blk k m E ds y cols := ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, hT k st m E ds y cols u hd hMv⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.dataThree_of_frontD
#print axioms ProofFile.Honest.K12.AtFile.accepts_at_own
#print axioms ProofFile.Honest.K12.AtFile.k12At_of_own
#print axioms ProofFile.Honest.K12.AtFile.acceptedS_at_group
#print axioms ProofFile.Honest.K12.AtFile.playsS_at_group
