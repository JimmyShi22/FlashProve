-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/WholeShape.lean: one statement for the whole proximity test with
no acceptance asked at the door or at the first stage: at a place and a state in front whose shape
passes the door's tests, with the prover's data tied to the group, the decision of the test's own
block accepts all that `testAll` shows. In both cases of the first fold's fresh table; at a group of
any layout, in any number of trees. The stages from the second on go by an invariant that is a free
parameter. A definition and theorems, with their proofs.

In the list: a job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test.
The place is `J.p` (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place, in the description
of a file, at which a proximity test is; among them the list of stages (`Fmt.M1.Stage`): a is the
first stage, next the second, rest the list of the others. The plan is the place with the rounds
that it declares (`laidOf J.p`, Johnson/Desc/K12/Law/ReadsK.lean). w is the prover's input; fr is
what precedes the test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean). The state in front is
`J.rec₀ w fr`: the state on entry to the test, which the job computes; it has the type `T12` of the
verifier's state inside a test (Johnson/Desc/K12/Join.lean). Its shape is `testSh` of it
(Johnson/Desc/K12/Honest/Shape/Test.lean). C: the coins that `testAll` reads, by number
(`TestCoins`). D: the sampled challenges by the round's number, "BAT" being round 0. The test's own
block is `proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`: Frame.lean as above; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean).
It is made of parts (`Parts`), with tests of its own between them: the front, which has no round;
the batching, with the round "BAT"; for each stage but the last a fold, a switch and the batching
after the switch; the base case. The door is the front, the batching and the block's test that the
group is the first stage's (`DoorYes`, TestYes.lean in this folder). The first stage is what
`FirstYes` (Johnson/Desc/K12/Honest/FirstYes.lean) speaks of: the first fold, the first switch and
the batching after it. A part passes something on to the next in the state's field `pass`: a
batching a claim with its layout, a fold single rows. The group is the group of oracle messages
under test. Dp: the library's plain data on it (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean), among
them the list `Dp.ts` of the trees that hold its members and the fresh table. c: a tree's column at
a position, as words. R: the prover's rows as plain functions (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). The two cases: the field `mask` of the state in front is
`some id` where the fresh table has come earlier, and `none` where the first fold sends its own.

  `test_accepts_shape`: where the fresh table has come earlier, under the hypotheses below: the
    block's decision (`Block.decide`, Johnson/Desc/Block.lean) at the state in front, at the rounds
    of `testAll J w fr C D` without their digests (`noDigest`) and at its groups of opened columns
    returns `.ok t'` for a state t' with `Post t'`. The field `tr` of what `testAll` returns, the
    trees' columns, is no argument of a decision
  `test_accepts_shape_own`: the same where the first fold sends its own fresh table, with
    `foldCutOwn` for `foldCut`
  `accepts_of_first`: `test_accepts` (WholeTest.lean in this folder) with its hypotheses grouped.
    The acceptances at the door and `FirstYes` are hypotheses here, and so is that a claim is passed
    after the batching
  `RestAsks`: a definition: a structure that gathers hypotheses of `test_accepts` which `TermAsks`
    and `SwitchPub` do not contain and `first_of_shape` does not conclude; see "Hypotheses"
  `front_same`: where the front's decision accepts, the state that it returns is the state that it
    was given
  `recB_eq`: so the job's state after the batching, `J.recB w fr d`, is `tBat`
    (Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) at the place, the state in front and d, what
    "BAT" sampled. No hypothesis

By what. `test_accepts_shape` calls `first_of_shape` (FirstTerm.lean as above). Under h, hm, htidy,
hpl, hv, Pl, hB, hF, fB and A that theorem gives: the front accepts and returns the state in front;
the batching accepts and returns `tBat`; the group there is the first stage's; a claim is passed
there; `FirstYes`. `recB_eq` turns `tBat` into `J.recB`, and `accepts_of_first` calls
`test_accepts`. `test_accepts_shape_own` does the same with `first_of_shape_own`. `front_same` calls
`like_P5` (Johnson/Desc/K12/Law/OutK.lean), by which an acceptance of the front of `guardedProximityTestParts` is one
of `frontJ` (Join.lean as above), and `bind_ok` (Johnson/Desc/K12/Law/FoldLaw.lean); the text of
`frontJ` returns its state.

Hypotheses of `test_accepts_shape` and `test_accepts_shape_own`, and of what sort each is.
`TermAsks` (A) is defined in FirstTerm.lean.
- On the state in front, tests with code. h: the door's Bool on the shape (`Sh.doorB`,
  Johnson/Desc/K12/Honest/Shape/TestDoor.lean). htidy: the mark "tidy" (`stTidyB`,
  Johnson/Desc/Ground/Shape/Marks.lean). hv: the front's test on the open rows (`claimsB`,
  TestDoor.lean). The last two read the state itself, not its shape. hm: which of the two cases it
  is.
- On the shape after the first fold: `readPubB` (Johnson/Desc/K12/Honest/Shape/ReadShape.lean), in
  `TermAsks` (`pub`).
- On the rows taken in (`runRows`, OnBytes/Slice/BlkBegin.lean). hpl: each is a `PlainRow`
  (OnBytes/Slice/BlkPlain.lean): none has a written-out factor.
- On the plan. hst, hrd, hor: the place has two stages or more, rounds and oracle messages. Pl:
  `SwitchPub` (Johnson/Desc/K12/Honest/Shape/TestSwitch.lean) at the first switch; it also reads the
  codes in the state in front. hB, hF: the tests on the cuts (`batCut`, `foldCut` or `foldCutOwn`).
  In `TermAsks`: the switch's two declared rounds are dS and dC (`cut`); h ≤ k at the first stage
  (`hk`); the first stage as the program names it (`stage`). Six numbers of the block's cuts: the
  rounds and the openings of the batching (nB, oB), of the first fold and of the first switch (`nF`,
  `oF`, `nS`, `oS` in `TermAsks`); by `oS` the switch has as many openings as `Dp.ts` has trees. In
  `RestAsks`: each later stage fits the next (`fitAll`); the stages' sizes (`hk'`, `sized`, `room`).
- On the state after the batching, `J.recB w fr (D 0)`. In `TermAsks`: the library's plain data and
  its test (`gpOf`, `gpL`; the field `plain`). In `RestAsks`: the layout's four numbers (`layK`,
  `layH`, `lenC`, `lenZ`). That a claim is passed there is not asked: `RestAsks` is asked at
  whatever claim is passed (V), and so is `plain`; that one is passed comes from `first_of_shape`.
- On the state after the first fold (`t1At`, FirstYes.lean), in `RestAsks`: a mask code's length
  (`ell`); `OldOk` (Johnson/Desc/K12/Honest/FirstValues.lean) at the single rows that are passed
  there (`old`).
- On the challenges' format. fB, and `fitF`, `fitS` in `TermAsks`: the rounds of "BAT", of the first
  fold and of the first switch have the declared form (`roundsFit`, Block.lean). The first switch's
  positions are as many as stated (`count` in `RestAsks`) and in range (`range` in `TermAsks`). The
  seed's factor's words are below the prime (`words` in `RestAsks`); the factor is the element that
  the switch's first round samples after the coordinates of the seed's point (`bitsAt`,
  FirstValues.lean).
- On the prover's data, in `RestAsks`: `ColsAt` (FirstRows.lean; `cols`); `StateAt`
  (Johnson/Desc/K12/Honest/FirstState.lean; `state`); every row that the test takes in says its
  claim of the words that the plain rows make (`AllSay`, Johnson/Desc/Means/Says.lean, at `wordsAt`,
  Johnson/Desc/K12/Honest/LaidState.lean; `allSay`); the job's trees are the group's (`trees`). In
  `TermAsks`: the columns' widths (`width`).
- From the second stage on. Inv and Post are free parameters. hstep, hbase: what `body_yes_of`
  (Johnson/Prover/Link/BodyYes.lean) asks of them. Before a stage that is not the last, Inv gives
  `StageYes`, which contains that stage's acceptances, and Inv after the stage. Before the last
  stage, Inv gives that the base case accepts, and Post of the state that it returns. hI: Inv holds
  after the first stage where the claim that is passed there is true (`ClaimTrue`,
  Johnson/Desc/K12/Honest/ClaimTrue.lean).

Limits.
- Every clause above is asked; none is shown here of any place of a file.
- "Accepts" is `Block.decide ... = .ok`: the block's test on the plan (`planOk`) and the two tests
  of `Block.step` before the decision, on the rounds' form and on the columns' keys, positions and
  widths, are not concluded.
- The state in front is whatever the job's function `rec₀` returns at w and fr. It is compared with
  nothing here: it is not shown to be the verifier's.
- Values that meet the whole list, with the invariant put in: ToyAll.lean and ToyCame.lean in this
  folder, where the fresh table has come earlier; each at a small made-up place.
- For the other case the invariant stays a free parameter, and no values that meet the list are
  given.
- `BodyInv` over `PlanAll` (Johnson/Prover/Link/BodyCloseB.lean), which WholeAll.lean puts in, asks
  `p.nums.ownMask = false` (`PlanFrom`, Johnson/Prover/Link/FormStepPlan.lean): it holds at no place
  whose numbers say that the first fold sends its own table.
- The invariant that WholeAll.lean and BodyInvFirst.lean in this folder put in, in their calls of
  `test_accepts_shape`, is `BodyInv` (Johnson/Prover/Link/BodyInv.lean), by itself or with one
  further clause.
- Rows with a written-out factor are not covered: where the test takes in such a row, hpl fails.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.WholeTest
import Johnson.Desc.K12.Honest.Shape.FirstTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape first_of_shape_own SwitchPub claimsB testSh)

variable {W X : Type}

/-- The front's part changes nothing: where its decision accepts, at no round and no column, the
state that it returns is the state that it was given. -/
theorem front_same (p : P12) (t tF : T12) (h : (guardedProximityTestParts.front p).decide t [] [] = .ok tF) :
    tF = t := by
  have h' := (H2K.Out.like_P5 p).front _ _ h
  unfold frontJ at h'
  dsimp only at h'
  split at h'
  · obtain ⟨_, _, h'⟩ := H2K.FoldLaw.bind_ok h'
    cases h'
    rfl
  · cases h'

/-- The job's state after the batching (`TestJob.recB`) is `tBat` at the state in front. d: what
"BAT" sampled. No hypothesis: where the front rejects, `recB` goes on from the state in front. -/
theorem recB_eq (J : TestJob W X) (w : W) (fr : Front X) (d : Fmt.Drawn) :
    J.recB w fr d = tBat J.p (J.rec₀ w fr) d := by
  have e : ((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD (J.rec₀ w fr) =
      J.rec₀ w fr := by
    cases hf : (guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] [] with
    | error _ => rfl
    | ok tF => exact front_same J.p _ tF hf
  unfold TestJob.recB tBat
  simp only [e]
  rfl

/-- **Hypotheses of `test_accepts` that `TermAsks` and `SwitchPub` do not contain.** row, L: a
claim's row and its layout; the theorems below put in what is passed after the batching; no field
reads row. cu, nx: the first two stages as the program names them. The head says of what sort each
field is. -/
structure RestAsks (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dp : Plain) (c : ℕ → ℕ → List UInt64)
    (R : PlainRows) (row : GroupRow) (L : GroupLayout) (cu nx : IoppStage) : Prop where
  hk' : next.h ≤ next.k
  sized : (sg a).Sized
  cols : ColsAt a Dp c R
  state : StateAt a Dp (J.first w fr C) R
  trees : J.trees₀ w fr C.mem (J.first w fr C) = groupTrees Dp.ts (logAt Dp.book) c
  count : (D (1 + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t
  fitAll : FitAll next rest
  layK : L.k = (sgOf a).h + (sgOf a).g
  layH : L.h = (sgOf a).h
  lenC : 2 ^ L.logEll = a.C.l
  lenZ : 2 ^ L.logEllZk = a.Z.l
  allSay : ∀ G, (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD
      (J.rec₀ w fr)).st.groups[(((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD
      (J.rec₀ w fr)).g]? = some G →
    AllSay rdE (J.recB w fr (D 0)).st (runRows (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) []
      []).toOption.getD (J.rec₀ w fr)).st G).toList (wordsAt (J.recB w fr (D 0)).st L R)
  room : (sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l
  ell : ((t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
    (J.recB w fr (D 0)) (J.first w fr C) D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l
  old : ∀ rows gp, (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
    (J.recB w fr (D 0)) (J.first w fr C) D).pass = .single rows gp →
    OldOk (sgOf a) (sgOf next) (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a
      (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C) D).st.codes rows nx.code nx.maskCode
  words : okE (((D (1 + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
    (bitsAt J.p 0 next (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) D)) zeroE) = true

/-- `test_accepts` with its hypotheses grouped. d1, d2, d3: the acceptances at the door. Y:
`FirstYes`. he, h1, hnx, hf: what four fields of `SwitchPub` state (`early`, `one`, `stageN`,
`fits`). hp: a claim is passed after the batching. -/
theorem accepts_of_first (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ))) (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (cu n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (d1 : (guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] [] = .ok (J.rec₀ w fr))
    (d2 : (guardedProximityTestParts.bat J.p (((laidOf J.p).take 1).map (·.1))).decide (J.rec₀ w fr)
      [noDigest ⟨[], D 0⟩] [] = .ok (J.recB w fr (D 0)))
    (d3 : (guardedProximityTestParts.group (J.recB w fr (D 0))).any (firstFits a) = true)
    (Y : FirstYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
    (he : J.p.early = true) (h1 : J.p.answers = 1) (hnx : stageAt J.p (0 + 1) next = some n)
    (hf : CsFit (sgOf a) (sgOf next))
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.recB w fr (D 0))
      (J.first w fr C) D Dp c cu dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (row : GroupRow) (L : GroupLayout) (hp : (J.recB w fr (D 0)).pass = .claim row L)
    (R : PlainRows) (V : RestAsks J w fr C D a next rest Dp c R row L cu n)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next l o t P col
            (Johnson.Prover.Link.rowOf t) D)
          (sNext (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D)
          (sCol (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base J.p j cur (l.map (·.1))).decide t
        ((lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).rs.map noDigest)
        (lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).gs = .ok t' ∧ Post t')
    (hI : ClaimTrue (sgOf next)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D) →
      Inv rest 1 next ((J.laid.drop 1).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
        (aCol rest.isEmpty next
          (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧ Post t' := by
  have eF : ((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD (J.rec₀ w fr) =
      J.rec₀ w fr := by rw [d1]; rfl
  have Y0 : DoorYes J w fr (D 0) a := ⟨⟨_, d1⟩, ⟨_, by rw [eF]; exact d2⟩, nB, oB, d3⟩
  obtain ⟨hD, hok⟩ := A.plain row L hp
  exact test_accepts J w fr C D a next rest ds os hst hrd hor he h1 Y0 row L hp Dp hD hok A.hk V.hk'
    V.sized cu n A.stage hnx c R V.cols V.state V.trees Y A.range V.count hf V.fitAll V.layK V.layH
    V.lenC V.lenZ V.allSay V.room V.ell V.old V.words Inv Post hstep hbase hI

/-- **The test's block accepts the term: from the shape, where the fresh table has come earlier.**
The term is `testAll J w fr C D`. Hypotheses and limits: see the head. -/
theorem test_accepts_shape (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ))) (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = some id) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, PlainRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.recB w fr (D 0))
      (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next l o t P col
            (Johnson.Prover.Link.rowOf t) D)
          (sNext (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D)
          (sCol (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base J.p j cur (l.map (·.1))).decide t
        ((lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).rs.map noDigest)
        (lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).gs = .ok t' ∧ Post t')
    (hI : ClaimTrue (sgOf next)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D) →
      Inv rest 1 next ((J.laid.drop 1).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
        (aCol rest.isEmpty next
          (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧ Post t' := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨d1, d2, d3, ⟨row, L, hp⟩, Y⟩ := first_of_shape J.p
    (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp
    c i n id dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
  rw [← eR] at d2 d3 hp Y
  exact accepts_of_first J w fr C D a next rest ds os hst hrd hor Dp c _ n dS dC d1 d2 d3 Y Pl.early
    Pl.one Pl.stageN Pl.fits A nB oB row L hp R (V row L hp) Inv Post hstep hbase hI

/-- **The same where the first fold sends its own fresh table.** hm says `none`, hF is on
`foldCutOwn`, and the proof calls `first_of_shape_own`. -/
theorem test_accepts_shape_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ))) (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = none) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, PlainRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCutOwn a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.recB w fr (D 0))
      (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next l o t P col
            (Johnson.Prover.Link.rowOf t) D)
          (sNext (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D)
          (sCol (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base J.p j cur (l.map (·.1))).decide t
        ((lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).rs.map noDigest)
        (lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).gs = .ok t' ∧ Post t')
    (hI : ClaimTrue (sgOf next)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D) →
      Inv rest 1 next ((J.laid.drop 1).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
        (aCol rest.isEmpty next
          (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧ Post t' := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨d1, d2, d3, ⟨row, L, hp⟩, Y⟩ := first_of_shape_own J.p
    (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp
    c i n dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
  rw [← eR] at d2 d3 hp Y
  exact accepts_of_first J w fr C D a next rest ds os hst hrd hor Dp c _ n dS dC d1 d2 d3 Y Pl.early
    Pl.one Pl.stageN Pl.fits A nB oB row L hp R (V row L hp) Inv Post hstep hbase hI

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.front_same
#print axioms ProofFile.Honest.K12.recB_eq
#print axioms ProofFile.Honest.K12.accepts_of_first
#print axioms ProofFile.Honest.K12.test_accepts_shape
#print axioms ProofFile.Honest.K12.test_accepts_shape_own
#print axioms ProofFile.Honest.K12.RestAsks
