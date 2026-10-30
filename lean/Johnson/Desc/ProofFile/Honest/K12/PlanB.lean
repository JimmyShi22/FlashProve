-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlanB.lean: the hypotheses of `test_accepts_all` (WholeAll.lean in
this folder) sorted by what they read, into four groups, and that theorem stated with the four
groups as its hypotheses: `accepts_of_plan`. The first group, the plan's half, is one test with
code, `planB`, on the place, the table of codes and one number only. So at a place that is written
out as a value the plan's half can be proved once, by an evaluation (`planB_KR`, AtKeyRanges.lean in
this folder, does so at one place), and the theorem is left with the other three groups as its
hypotheses: the structures `ShapeAsks`, `FormAsks` and `DataAsks`. General in the job, the prover's
input, what precedes the test, the coins, the sampled challenges, the table of codes, the plain
data, the columns and the plain rows. Definitions and two theorems, with their proofs.

In the list: J is a job (`TestJob`, Test.lean in this folder): what a caller supplies for its test.
p, or `J.p`, is its place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at which a
proximity test is, among them the list of stages (`Fmt.M1.Stage`); a and next are the first two
stages. The plan is the place with the rounds that it declares (`laidOf p`, and `laidS p` without
the first of them; Johnson/Desc/K12/Law/ReadsK.lean). K is a table of codes (`Codes`,
OnBytes/Iop/Ground.lean). w is the prover's input, fr what precedes the test (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean), C the coins that `testAll` reads (`TestCoins`, Test.lean),
D the sampled challenges by the round's number, "BAT" being round 0. The block is `proximityTestKind guardedProximityTestParts J.p`
(Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean). Its parts (`Parts`, Frame.lean) are the
front, which has no round, the batching, with the round "BAT", for each stage but the last a fold, a
switch and a batching after the switch, and the base case. The term is `testAll J w fr C D`
(Test.lean): all that is shown in the test. By the text of `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean) its rounds at the first fold and at the first switch are
`rfAt` and `rsAt` (Johnson/Desc/K12/Honest/FirstYes.lean). The state on entry is `J.rec₀ w fr`, of
the type `T12` of the verifier's state inside a test (Johnson/Desc/K12/Join.lean). The state after
the batching is `J.recB w fr (D 0)` (Test.lean), and the state after the first fold is `tFold`: the
state on entry, advanced by the `decide` functions of the front, the batching and the first fold;
where one of them rejects, the state before it is kept. "Behind" a part means after it, and "in
front of" it before it. A part passes something on in the state's field `pass`: a batching a claim
with its layout, a fold single rows. A state's shape is `testSh` of it
(Johnson/Desc/K12/Honest/Shape/Test.lean), which holds `coreSh`
(Johnson/Desc/Ground/Shape/Core.lean) of its statement, book and roots. Dp is the library's plain
data on the group under test (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean), among them the list
`Dp.ts` of trees. c is a tree's column at a position, as words. R is the prover's rows as plain
functions of numbers (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean).

  `accepts_of_plan`: if `planB J.p K Dp.ts.length` is true, and `ShapeAsks J w fr C D K Dp`,
    `FormAsks J w fr C D` and `DataAsks J w fr C D Dp c R` hold, then the decision of the test's
    block accepts all that `testAll` shows: the block's `decide`, at the state on entry, the rounds
    of `testAll J w fr C D` without their digests (`noDigest`, Johnson/Desc/Block.lean) and its
    groups of opened columns, returns `.ok t'` for some state t'
  `planL p K nT`, `planB`, `planNo`: definitions: the plan's half. `planL` lists the clauses, each a
    name with a Bool; `planB`: all are true; `planNo`: the names of those that are false. nT: how
    many trees the first switch opens. At a place with fewer than three stages the list is one false
    clause, "three stages or more". Else the clauses are: the place has rounds and oracle messages
    (`roundsOfNums` and `testOracles`, Johnson/Desc/K12/TestEntries.lean, return something);
    `switchPubB` (Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean) at K and the first switch; the
    tests on the declared rounds that the block cuts for the batching and for the first fold
    (`batCut`, `foldCut`: FormBat.lean and FormFold.lean in Johnson/Prover/Link/); h ≤ k at the
    first two stages; the first stage as the program names it (`stageAt`, Join.lean); the first
    switch has two declared rounds; six numbers of the block's cuts: how many rounds and how many
    openings the first fold, the first switch and the batching have ("nF", "oF", "nS", "oS", "nB",
    "oB"; `foldAt`, `switchAt`, `batAt`, Johnson/Desc/K12/FrameLaws.lean), of which "oS" says that
    the first switch has nT openings; the first stage's sizes (`sizedB`,
    Johnson/Desc/K12/Honest/FirstTest.lean) and room (h + 2 (k - h) + 1 ≤ `a.Z.l`); a mask code's
    length: the mask code of K with the first stage's number has the message length `a.Z.l`; each
    later stage fits the next (`fitAllB`, Johnson/Desc/K12/Honest/FirstAsks.lean); `switchPlanB`
    (AllB.lean in this folder) at K and the first switch; `planFromOk`
    (Johnson/Prover/Link/StepPlanOk.lean) at K, from the second stage on; the items' sorts: from the
    second stage on the declared rounds ask the sorts of `bodyItems`
    (Johnson/Prover/Link/LinkItems.lean)
  `ShapeAsks J w fr C D K Dp`: a definition: a structure of nine hypotheses on the three states,
    public by its text only: see Limits. On the state on entry: the codes are K (`codes`);
    `Sh.doorB` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean) at its shape (`door`); the fresh table
    has come earlier: the field `mask` is `some` (`came`); the two marks, `stTidyB` and `stPlainB`
    (Johnson/Desc/Ground/Shape/Marks.lean; `tidy`, `plainRows`); `claimsB` (TestDoor.lean;
    `claims`). On the state after the batching, at whatever claim it passes (`plain`): `gpOf`
    returns Dp, the library's plain data; Dp passes its test `gpL` (both in FirstOk.lean); the
    layout's four numbers are the first stage's. On the state after the first fold: the codes are K
    (`codes₁`); at whatever single rows it passes (`pub`): `readPubB`
    (Johnson/Desc/K12/Honest/Shape/ReadShape.lean) at the shapes, and `OldOk`
    (Johnson/Desc/K12/Honest/FirstValues.lean)
  `FormAsks J w fr C D`: a definition: a structure of seven hypotheses on the challenges. The
    declared form (`roundsFit`, Block.lean) at "BAT" (`bat`) and at the first fold's and the first
    switch's rounds as the term shows them (`fold`, `switch`), and from the second stage on
    (`later`: `FitFrom`, Johnson/Prover/Link/BodyFit.lean); the first switch's positions are as many
    as the first stage states (`count`) and in range (`range`); the seed's factor's words are below
    the prime (`words`: `okE`, OnBytes/Field/Ext.lean, at the element with the number `bitsAt`,
    FirstValues.lean, among those that the first switch's first round samples)
  `DataAsks J w fr C D Dp c R`: a definition: a structure of four hypotheses on the prover's data:
    `ColsAt` (FirstRows.lean; `cols`); `StateAt` (Johnson/Desc/K12/Honest/FirstState.lean) at the
    first stage's state `J.first w fr C` (`state`); the job's trees are the group's: `J.trees₀`
    returns `groupTrees` (Johnson/Desc/K12/Honest/GroupState.lean) of `Dp.ts` and c (`trees`); at
    whatever claim is passed after the batching, every row that the test takes in says its claim of
    the words that the plain rows make: `AllSay` (Johnson/Desc/Means/Says.lean) at `wordsAt`
    (Johnson/Desc/K12/Honest/LaidState.lean; `allSay`)
  `tFold J w fr C D`: an abbreviation: the state after the first fold: `t1At` (FirstYes.lean) at the
    place, the coins, the first stage, the state after the batching, the first stage's state and D
  `stA p`, `stN p`: definitions: the place's first and second stage; a stage of zeros where there is
    none
  `front_getD`: the front's part, run, leaves the state, whether it accepts or not: its `decide` at
    a state t, no round and no column, with t kept where it rejects, gives t

By what. `accepts_of_plan` unfolds `planB` into its clauses and calls `test_accepts_all` at the
parameters that `lettersOf` (AllB.lean) computes from the place. `switchPub_of` (TestSwitchPub.lean)
gives `SwitchPub` at K, and `codes` turns K into the codes of the state on entry. `runRows_plain`
(TestDoor.lean) gives, from `plainRows`, that no row taken in has a written-out factor. `TermAsks`
(Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) and `RestAsks` (WholeShape.lean in this folder) are
built field by field from the clauses and the three structures' fields, with `two_of_length`
(StepPlanOk.lean), `sized_of` (FirstTest.lean) and `fitAll_of` (FirstAsks.lean); `front_getD`
rewrites the state in the field `allSay` of `RestAsks`. `codes₁` turns the codes after the first
fold into K in three places: the mask code's length; `switchPlan_of_B` (AllB.lean), which gives
`FirstSwitchPlan` (Johnson/Prover/Link/BodyBehindAll.lean), here `SwitchPlan` because a third stage
follows; and `planFrom_of_ok` (StepPlanOk.lean), which with the clause on the sorts gives `PlanAll`
(Johnson/Prover/Link/BodyCloseB.lean). `front_getD` calls `front_same` (WholeShape.lean).

Hypotheses of `accepts_of_plan`. hP: `planB` is true at the place, K and the number of trees in
`Dp.ts`. S: `ShapeAsks` at K and Dp. F: `FormAsks`. Dt: `DataAsks` at Dp, c and R.

Limits.
- The three structures are hypotheses: none of them is shown here of any value.
- "Public" and "no value of the prover" are said of `ShapeAsks` by its text: by type its clauses
  behind the fold hang on the term's rounds, and nothing here says that the shape behind the fold is
  a function of the shape in front. By type every clause reads the prover's input w and the front
  fr, through `J.rec₀` or `J.recB`; `codes₁` and `pub` read the coins C and the first stage's state
  `J.first w fr C` too, through `tFold`.
- `plain`, `pub` and `allSay` are implications. Where the state after the batching passes no claim,
  `plain` and `allSay` ask nothing, and where the state after the first fold passes no single rows,
  `pub` asks nothing. `plain` is the only clause of `ShapeAsks` that names Dp: where it asks
  nothing, Dp is tied by `DataAsks` only.
- Six of the nine read the shape alone (numbers, flags, lists); the two marks and `claimsB` read the
  open rows' summands too, which hang on challenges in front of the test. The nine are the fields of
  `ShapeAsks`; the six are `codes`, `door`, `came`, `plain`, `codes₁` and `pub`. The count is by
  reading: no theorem states it. In `plain` the equation `gpOf ... = some Dp` fixes Dp, whose fields
  `st` and `book` are a whole statement and a whole book, not shapes.
- The state on entry is whatever the job's function `rec₀` returns at w and fr. It is compared with
  nothing here: it is not shown to be the verifier's. The states after the batching and after the
  first fold are computed from it.
- The clause "the codes after the first fold are K" (`codes₁`) could be derived; here it is a
  hypothesis.
- `FormAsks`' clauses on the first stage's rounds read the term's rounds, and so the prover's state,
  though `roundsFit` tests of a sent item its sort alone.
- Where the four hypotheses hold together: SortsMember.lean (not in the library yet) in this folder
  (`sorts_one`, `sorts_came`): at two small made-up places, each at one list of challenges.
  `ShapeAsks` and `DataAsks` have no value that meets them in the library yet: no theorem of the
  library concludes one of them but from the same structure at other challenges (Sim/PlanCausal.lean
  in this folder): by reading the files that name them.
- `planB` is false at a place with fewer than three stages; `test_accepts_all` is stated from two
  stages on.
- The reach is that of `test_accepts_all`: see the limits of WholeAll.lean. `came` asks that the
  state on entry names the fresh table, and the clause "planFromOk" that the place's `ownMask` is
  false: the case in which the first fold sends its own table is not covered. Nor is a statement on
  entry in which an open row or a sample row has a written-out factor (`plainRows`). "Accepts" is
  `Block.decide ... = .ok`: `planOk` and the two tests of `Block.step` before the decision are not
  concluded.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AllB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB)

variable {W X : Type}

/-- The plan's half: the clauses, each a name with a Bool. nT: how many trees the first switch
opens. At a place with fewer than three stages: one false clause. -/
def planL (p : P12) (K : Codes) (nT : ℕ) : List (String × Bool) :=
  match p.nums.stages with
  | a :: next :: nx' :: rest' =>
    let Z := lettersOf p a next
    [("rounds", (H2U.roundsOfNums p.nums).isSome),
     ("oracle messages", (H2U.testOracles p.nums).isSome),
     ("switchPubB", switchPubB p K 0 a next (nx' :: rest').isEmpty ⟨Z.i.1, Z.i.2, a.k, a.h⟩ Z.n Z.dS
       Z.dC),
     ("batCut", batCut (((laidOf p).take 1).map (·.1))),
     ("foldCut", foldCut a.k (((laidS p).take (1 + a.k)).map (·.1))),
     ("h ≤ k", decide (a.h ≤ a.k)),
     ("the first stage", decide (stageAt p 0 a = some ⟨Z.i.1, Z.i.2, a.k, a.h⟩)),
     ("two rounds", decide (((((laidS p).drop (1 + a.k)).take 2).map (·.1)).length = 2)),
     ("nF", decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).rounds.length =
       1 + ((sgOf a).h + (sgOf a).g))),
     ("oF", decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).openings = 0)),
     ("nS", decide ((switchAt guardedProximityTestParts p 0 a next (nx' :: rest').isEmpty (laidS p) :
       Block T12 Unit).rounds.length = 2)),
     ("oS", decide ((switchAt guardedProximityTestParts p 0 a next (nx' :: rest').isEmpty (laidS p) :
       Block T12 Unit).openings = nT)),
     ("nB", decide ((batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).rounds.length = 1)),
     ("oB", decide ((batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).openings = 0)),
     ("h ≤ k, next", decide (next.h ≤ next.k)),
     ("sizes", sizedB a),
     ("later stages fit", fitAllB next (nx' :: rest')),
     ("room", decide ((sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l)),
     ("a mask code's length", decide ((K.mask.getD Z.i.2 default).ell = a.Z.l)),
     ("switchPlanB", switchPlanB p K 0 a next Z.n),
     ("planFromOk", planFromOk p (nx' :: rest') (0 + 1) next ((laidS p).drop (a.k + 3)) K),
     ("sorts", decide (((laidS p).drop (a.k + 3)).map asked = bodyItems next (nx' :: rest')))]
  | _ => [("three stages or more", false)]

/-- All clauses of `planL` are true. -/
def planB (p : P12) (K : Codes) (nT : ℕ) : Bool := (planL p K nT).all (·.2)

/-- The names of the clauses of `planL` that are false. -/
def planNo (p : P12) (K : Codes) (nT : ℕ) : List String :=
  ((planL p K nT).filter (!·.2)).map (·.1)

/-- The place's first stage; a stage of zeros where there is none. -/
def stA (p : P12) : Fmt.M1.Stage := p.nums.stages.headD default
/-- The place's second stage; a stage of zeros where there is none. -/
def stN (p : P12) : Fmt.M1.Stage := p.nums.stages.getD 1 default

section
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)

/-- The state after the first fold, at the term: `t1At` at the job's state after the batching and
the first stage's state. It is computed from the job's state on entry, which is not shown to be the
verifier's. -/
abbrev tFold : T12 :=
  t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0))
    (J.first w fr C) D

/-- The hypotheses on the state on entry, on the state after the batching and on the state after the
first fold. "Public" is said of them by their text only: see the limits at the top of this file. The
state on entry is the job's, not shown to be the verifier's. -/
structure ShapeAsks (K : Codes) (Dp : Plain) : Prop where
  codes : (J.rec₀ w fr).st.codes = K
  door : Sh.doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
    (lettersOf J.p (stA J.p) (stN J.p)).i
    ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
    (testSh (J.rec₀ w fr)) = true
  came : (J.rec₀ w fr).mask.isSome = true
  tidy : stTidyB (J.rec₀ w fr).st = true
  plainRows : stPlainB (J.rec₀ w fr).st = true
  claims : claimsB (J.rec₀ w fr) = true
  plain : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
    gpOf J.p (J.recB w fr (D 0)) (stA J.p) L = some Dp ∧ ok (gpL J.p (stA J.p) row Dp) = true ∧
      L.k = (sgOf (stA J.p)).h + (sgOf (stA J.p)).g ∧ L.h = (sgOf (stA J.p)).h ∧
      2 ^ L.logEll = (stA J.p).C.l ∧ 2 ^ L.logEllZk = (stA J.p).Z.l
  codes₁ : (tFold J w fr C D).st.codes = K
  pub : ∀ rows gp, (tFold J w fr C D).pass = .single rows gp →
    readPubB (coreSh ⟨(tFold J w fr C D).st, (tFold J w fr C D).book, (tFold J w fr C D).roots⟩)
      (singleSh rows) (stA J.p).C.a = true ∧
    OldOk (sgOf (stA J.p)) (sgOf (stN J.p)) (tFold J w fr C D).st.codes rows
      (lettersOf J.p (stA J.p) (stN J.p)).n.code (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode

/-- The hypotheses on the challenges. -/
structure FormAsks : Prop where
  bat : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true
  fold : roundsFit (((laidS J.p).take (1 + (stA J.p).k)).map (·.1))
    (rfAt (coinsOf J.p.nums.stages C.hide C.rest) 0 (stA J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) = true
  switch : roundsFit
    [(lettersOf J.p (stA J.p) (stN J.p)).dS, (lettersOf J.p (stA J.p) (stN J.p)).dC]
    ((rsAt J.p (coinsOf J.p.nums.stages C.hide C.rest) (J.p.nums.stages.drop 2) 0 (stA J.p)
      (stN J.p) (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) D).map noDigest) = true
  later : FitFrom D ((laidS J.p).drop ((stA J.p).k + 3))
    (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g) + 3)
  range : ∀ x ∈ (D (1 + 2 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g))).poss,
    x < 2 ^ (stA J.p).C.a
  count : (D (1 + 2 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g))).poss.length = (stA J.p).t
  words : okE (((D (1 + 1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g))).elems.map E.ofTriple).getD
    (bitsAt J.p 0 (stN J.p) (tFold J w fr C D)) zeroE) = true

/-- The hypotheses on the prover's data. -/
structure DataAsks (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows) : Prop where
  cols : ColsAt (stA J.p) Dp c R
  state : StateAt (stA J.p) Dp (J.first w fr C) R
  trees : J.trees₀ w fr C.mem (J.first w fr C) = groupTrees Dp.ts (logAt Dp.book) c
  allSay : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
    ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      AllSay rdE (J.recB w fr (D 0)).st (runRows (J.rec₀ w fr).st G).toList
        (wordsAt (J.recB w fr (D 0)).st L R)

end

/-- The front's part, run, leaves the state, whether it accepts or not. -/
theorem front_getD (p : P12) (t : T12) :
    ((guardedProximityTestParts.front p).decide t [] []).toOption.getD t = t := by
  cases hf : (guardedProximityTestParts.front p).decide t [] [] with
  | error _ => rfl
  | ok tF => exact front_same p _ tF hf

/-- **The plan's half as its test `planB`, the other three groups as hypotheses: the block's
decision accepts all that `testAll` shows.** -/
theorem accepts_of_plan (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp c R) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    have hR : J.p.nums.stages.drop 2 = nx' :: rest' := by
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19,
      p20, p21, p22⟩ := hP
    obtain ⟨ds, hrd⟩ := Option.isSome_iff_exists.1 p1
    obtain ⟨os, hor⟩ := Option.isSome_iff_exists.1 p2
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9, s10⟩ := S
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := F
    obtain ⟨d1, d2, d3, d4⟩ := Dt
    simp only [tFold, hA, hN, hR] at s2 s7 s9 s10 f2 f3 f4 f5 f6 f7 d1 d2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    refine test_accepts_all J w fr C D a next (nx' :: rest') ds os hst hrd hor Dp c
      (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 (fun G hG => runRows_plain s5 hG) s6 Pl p4 p5 f1
      ⟨fun row L h => ⟨(s7 row L h).1, (s7 row L h).2.1⟩, p6, p7, d1.width, f5, two_of_length _ p8,
        f2, f3, fun rows gp h => (s10 rows gp h).1, p9, p10, p11, p12⟩ p13 p14 R
      (fun row L h => ⟨p15, sized_of p16, d1, d2, d3, f6, fitAll_of _ _ p17, (s7 row L h).2.2.1,
        (s7 row L h).2.2.2.1, (s7 row L h).2.2.2.2.1, (s7 row L h).2.2.2.2.2, ?_, p18, ?_,
        fun rows gp h' => (s10 rows gp h').2, f7⟩) ?_ ⟨?_, p22⟩ f4
    · rw [front_getD]
      exact d4 row L h
    · show ((t1At J.p _ 0 a (laidS J.p) 1 _ _ D).st.codes.mask.getD _ default).ell = a.Z.l
      rw [s9]
      exact p19
    · show SwitchPlan J.p _ 0 a next _
      rw [s9]
      exact switchPlan_of_B p20
    · rw [s9]
      exact planFrom_of_ok J.p _ _ _ _ _ p21
  · simp at hP

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.front_getD
#print axioms ProofFile.Honest.K12.accepts_of_plan
#print axioms ProofFile.Honest.K12.planL
#print axioms ProofFile.Honest.K12.planB
#print axioms ProofFile.Honest.K12.planNo
#print axioms ProofFile.Honest.K12.stA
#print axioms ProofFile.Honest.K12.stN
#print axioms ProofFile.Honest.K12.tFold
#print axioms ProofFile.Honest.K12.ShapeAsks
#print axioms ProofFile.Honest.K12.FormAsks
#print axioms ProofFile.Honest.K12.DataAsks
