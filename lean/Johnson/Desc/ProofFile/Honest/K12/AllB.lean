-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AllB.lean: two tests with code, `coreB` and `allB`, whose "true"
gives every hypothesis of `test_accepts_all` and of `test_left_all` (WholeAll.lean in this folder),
with the theorems that say so. Where `coreB` is true, the decision of the proximity test's block
accepts all that `testAll` shows; where `allB` is true, which has one clause more, nothing is left
untested after it besides. With them the hypotheses can be checked together at a value by an
evaluation: ToyAll.lean, ToyCame.lean and ToyLate.lean in this folder do so, at small made-up
places. General in the job, the prover's input, what precedes the test, the coins, the sampled
challenges and the plain rows. Definitions with code, statements and proofs.

In the list: J is a job (`TestJob`, Test.lean in this folder: what a caller supplies for its test)
and `J.p` its place (`P12`, Johnson/Desc/K12/Frame.lean: the test's parameters). w is the prover's
input, fr what precedes the test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean), C the coins that
`testAll` reads (`TestCoins`, Test.lean), D the sampled challenges by the round's number, R the
prover's rows as plain functions of numbers (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean).
`J.rec₀ w fr` is the state on entry to the test. The block is `proximityTestKind guardedProximityTestParts J.p` (Frame.lean). It is
built from the parts of `guardedProximityTestParts` (`Parts`, Frame.lean): the front, the batching, for each stage
(`Fmt.M1.Stage`) but the last a fold, a switch and a batching after the switch, and the base case. a
and next are the place's first two stages.

Which decisions of the verifier the tests run. The states after the batching and after the first
fold are terms that run the `decide` functions of the front, the batching and the first fold:
`TestJob.recB` (Test.lean) and `t1At` (Johnson/Desc/K12/Honest/FirstYes.lean). Where a part rejects,
they keep the state before it. Arms of the tests read a verdict through what the state passes on
(`T12.pass`, Johnson/Desc/K12/Join.lean): `coreL` and `allL` ask that a claim is passed after the
batching; `termB` and `restB` ask that single rows are passed after the fold. Each is stricter than
the hypothesis that it replaces, which is vacuous where no such value is passed. Where the fold has
rejected, `t1At` is the state after the batching, which in `coreL` and `allL` passes a claim: so the
arms of `termB` and `restB` are false there. Where the batching has rejected, `recB` is the state on
entry (`front_same`, WholeShape.lean in this folder): the arm of `coreL` and `allL` is false there
unless the state on entry itself passes a claim. The theorems do not use these arms as acceptances:
the theorems of WholeAll.lean get the acceptances of the front, the batching and the first fold from
the tests on the shape, by `first_of_shape` (Johnson/Desc/K12/Honest/Shape/FirstTerm.lean), no
hypothesis of which is an acceptance. No clause runs the whole block's decision, a switch, a
batching after a switch, a later stage, the base case, the reading of the old rows, or `Block.step`.

  `accepts_of_coreB`: if `coreB J w fr C D R` is true, the block's `decide`, at the state
    `J.rec₀ w fr`, the rounds of `testAll J w fr C D` without their digests (`noDigest`) and its
    opened columns, returns `.ok t'` for some state t'. The field `tr` of what `testAll` returns,
    the trees' columns, is no argument of the decision
  `accepts_of_allB`: if `allB J w fr C D R` is true, the same holds, and
    `ChainEnd.NothingLeft t'.st` (Johnson/Desc/ChainEndLaw.lean)
  `coreL`, `coreB`, `coreNo`: definitions: the clauses for `test_accepts_all`, each a name with a
    Bool; all of them are true; the names of those that are false. The list is one false clause
    where the place has fewer than three stages, where no claim is passed after the batching, or
    where `gpOf` (Johnson/Desc/K12/Law/FirstOk.lean) returns nothing
  `allL`, `allB`, `allNo`: definitions: the same for `test_left_all`: with the clause "nothing is
    left untested behind the batching" besides
  `termB`, `termAsks_of`: `TermAsks` (Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) as a test; where
    the state after the batching passes a claim and `gpOf` returns the plain data, its "true" at
    `lettersOf` gives `TermAsks`
  `restB`, `restAsks_of`: `RestAsks` (WholeShape.lean) as a test, at the columns of the job's own
    trees (`colsFrom`, Johnson/Desc/K12/Honest/FirstAsks.lean, at `J.trees₀`); where `gpOf` returns
    the plain data, its "true" gives `RestAsks`, at every value of the parameter row, which no
    field of `RestAsks` reads
  `switchPlanB`, `switchPlan_of_B`: `SwitchPlan` (Johnson/Prover/Link/FormBehindAny.lean) as a test,
    whose "true" gives it: it has no clause on a tree of the old rows
  `Letters`, `lettersOf`: a structure and a definition: the parameters that the hypotheses name,
    computed from the place: the numbers of the first stage's two codes, the second stage in the
    program's form (`IoppStage`), the first switch's two declared rounds

By what. `accepts_of_coreB` calls `test_accepts_all`, and `accepts_of_allB` calls `test_left_all`.
Each clause gives its hypothesis as follows. The tests on the shape are hypotheses as they are:
`Sh.firstB` (Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean) unfolds into `Sh.doorB`, `switchPubB`
(`switchPub_of`, same file, gives `SwitchPub`) and the tests `batCut` and `foldCut` on the declared
rounds; `stTidyB`; `claimsB`; `readPubB`, in `TermAsks`. Rows without a written-out factor:
`runRows_plain` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean). The plan: `switchPlan_of_B` at the
first switch, where `FirstSwitchPlan` (Johnson/Prover/Link/BodyBehindAll.lean) is `SwitchPlan`
because a third stage follows; `planFrom_of_ok` (Johnson/Prover/Link/StepPlanOk.lean) from the
second stage on. The items' sorts: an equation of lists, which is `SortsFrom`
(Johnson/Prover/Link/BodySorts.lean). The challenges' format: `fitFrom_of_B`
(Johnson/Desc/K12/Honest/FitFromB.lean) and `roundsFit` (Johnson/Desc/Block.lean). "Nothing is left
untested": `untested_spec` (Johnson/Desc/ChainEndLaw.lean). The prover's data: `colsAt_of`,
`stateAt_of`, `allSay_of` and `groupTrees_colsFrom` (FirstTest.lean, FirstStateTest.lean,
BatStateTest.lean and FirstAsks.lean in Johnson/Desc/K12/Honest/).

Limits.
- Sufficient, not necessary.
- Neither test is shown to be true at any value here.
- Both tests are false at a place with fewer than three stages; the two theorems of WholeAll.lean
  are stated from two stages on.
- Two names are coarse: "TermAsks" is one name for thirteen clauses, "RestAsks" for sixteen (both
  counts by reading `termB` and `restB`).
- `Sh.firstB` and `Sh.doorB` (on the shape) are other tests than `firstB`
  (Johnson/Desc/K12/Honest/FirstTest.lean) and `doorB` (TestYesTest.lean (not in the library yet)
  in this folder) of this namespace, which run decisions.
- The reach is that of the two theorems of WholeAll.lean: see the limits there. By their text the
  tests are false where `(J.rec₀ w fr).mask` is `none`, where the place says that the first fold
  sends its own table (`ownMask`), and where an open row or a sample row of the statement on entry
  has a written-out factor (`stPlainB`). "Accepts" is `Block.decide ... = .ok`: `planOk` and the two
  tests of `Block.step` before the decision are not concluded.
- `coreL` and `allL` are two texts: that the second is the first with one clause more is stated by
  no theorem.
- `J.rec₀`, `J.rows₀` and `J.trees₀` are functions that the caller supplies (Test.lean). Nothing
  here compares the state on entry with a verifier's state in a run.
- The prover's values are compared by "RestAsks" only (`colsB`, `stateB`, `saysB`). They also enter
  `t1At`, through the rounds that the first fold shows, and "TermAsks", "SwitchPlan at the first
  switch" and "the plan from the second stage on (planFromOk)" are computed from `t1At` too. That
  these three do not depend on the prover's values is not stated. `claimsB` reads values of the
  state on entry.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.WholeAll
import Johnson.Desc.K12.Honest.Shape.TestSwitchPub
import Johnson.Desc.K12.Honest.FitFromB
import Johnson.Desc.K12.Honest.BatStateTest
import Johnson.Desc.K12.Honest.FirstAsks
import Johnson.Prover.Link.StepPlanOk
import Johnson.Desc.ChainEndLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain)

variable {W X : Type}

/-- The parameters that the hypotheses of `test_accepts_all` and `test_left_all` name. `i`: the
numbers of the first stage's two codes. `n`: the second stage in the program's form. `dS`, `dC`: the
first switch's two declared rounds. -/
structure Letters where
  i : ℕ × ℕ
  n : IoppStage
  dS : Fmt.DeclaredRound
  dC : Fmt.DeclaredRound

/-- These parameters, computed from the place p and its first two stages a and next; a default value
where the place has none. -/
def lettersOf (p : P12) (a next : Fmt.M1.Stage) : Letters :=
  ⟨p.idx.headD (0, 0), stageOr p 1 next,
    ((((laidS p).drop (1 + a.k)).take 2).map (·.1)).getD 0 default,
    ((((laidS p).drop (1 + a.k)).take 2).map (·.1)).getD 1 default⟩

/-- `TermAsks` as a test. tB: the state after the batching. False unless single rows are passed
after the first fold. -/
def termB (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage) (o : ℕ)
    (tB : T12) (P : PS) (D : ℕ → Fmt.Drawn) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (row : GroupRow)
    (Z : Letters) : Bool :=
  ok (gpL p a row Dp) && decide (a.h ≤ a.k) &&
  decide (stageAt p 0 a = some ⟨Z.i.1, Z.i.2, a.k, a.h⟩) &&
  (Dp.ts.all fun u => (List.range (2 ^ logAt Dp.book u)).all fun x =>
    decide ((c u x).length = widthAt Dp.book u)) &&
  ((D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.all fun x => decide (x < 2 ^ a.C.a)) &&
  decide (((((laidS p).drop (1 + a.k)).take 2).map (·.1)).length = 2) &&
  roundsFit (((laidS p).take (1 + a.k)).map (·.1)) (rfAt K 0 a o tB P D) &&
  roundsFit [Z.dS, Z.dC] ((rsAt p K rest 0 a next (laidS p) o tB P D).map noDigest) &&
  (match (t1At p K 0 a (laidS p) o tB P D).pass with
    | .single rows _ => readPubB (coreSh ⟨(t1At p K 0 a (laidS p) o tB P D).st,
        (t1At p K 0 a (laidS p) o tB P D).book, (t1At p K 0 a (laidS p) o tB P D).roots⟩)
        (singleSh rows) a.C.a
    | _ => false) &&
  decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).rounds.length =
    1 + ((sgOf a).h + (sgOf a).g)) &&
  decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).openings = 0) &&
  decide ((switchAt guardedProximityTestParts p 0 a next rest.isEmpty (laidS p) : Block T12 Unit).rounds.length =
    2) &&
  decide ((switchAt guardedProximityTestParts p 0 a next rest.isEmpty (laidS p) : Block T12 Unit).openings =
    Dp.ts.length)

theorem termAsks_of (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (tB : T12) (P : PS) (D : ℕ → Fmt.Drawn) (Dp : Plain) (c : ℕ → ℕ → List UInt64)
    (row : GroupRow) (L : GroupLayout) (hp : tB.pass = .claim row L)
    (hD : gpOf p tB a L = some Dp)
    (h : termB p K rest a next o tB P D Dp c row (lettersOf p a next) = true) :
    TermAsks p K rest a next o tB P D Dp c
      ⟨(lettersOf p a next).i.1, (lettersOf p a next).i.2, a.k, a.h⟩ (lettersOf p a next).dS
      (lettersOf p a next).dC := by
  unfold termB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩ := h
  refine ⟨fun row' L' h' => ?_, a2, a3,
    fun u hu x hx => of_decide_eq_true (all_range (List.all_eq_true.1 a4 u hu) x hx),
    fun x hx => of_decide_eq_true (List.all_eq_true.1 a5 x hx), two_of_length _ a6, a7, a8,
    fun rows gp h' => ?_, a10, a11, a12, a13⟩
  · rw [hp] at h'
    injection h' with e1 e2
    subst e1 e2
    exact ⟨hD, a1⟩
  · rw [h'] at a9
    exact a9

/-- `RestAsks` as a test, at the columns of the job's own trees. False unless single rows are passed
after the first fold. -/
def restB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dp : Plain) (R : PlainRows)
    (L : GroupLayout) (cu nx : IoppStage) : Bool :=
  decide (next.h ≤ next.k) && sizedB a &&
  colsB a Dp (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) R &&
  stateB a Dp (J.first w fr C) R &&
  decide ((J.trees₀ w fr C.mem (J.first w fr C)).map (·.1) = Dp.ts.map (logAt Dp.book)) &&
  decide ((D (1 + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t) && fitAllB next rest &&
  decide (L.k = (sgOf a).h + (sgOf a).g) && decide (L.h = (sgOf a).h) &&
  decide (2 ^ L.logEll = a.C.l) && decide (2 ^ L.logEllZk = a.Z.l) &&
  saysB (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD (J.rec₀ w fr))
    (J.recB w fr (D 0)) L R &&
  decide ((sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l) &&
  decide (((t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
    (J.recB w fr (D 0)) (J.first w fr C) D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l) &&
  (match (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).pass with
    | .single rows _ => oldOkB (sgOf a) (sgOf next) (t1At J.p
        (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes rows nx.code nx.maskCode
    | _ => false) &&
  okE (((D (1 + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
    (bitsAt J.p 0 next (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) D)) zeroE)

theorem restAsks_of (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dp : Plain) (R : PlainRows)
    (row : GroupRow) (L : GroupLayout) (cu nx : IoppStage)
    (hD : gpOf J.p (J.recB w fr (D 0)) a L = some Dp)
    (h : restB J w fr C D a next rest Dp R L cu nx = true) :
    RestAsks J w fr C D a next rest Dp (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) R row
      L cu nx := by
  unfold restB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩,
    b15⟩, b16⟩ := h
  have hnd : Dp.ts.Nodup := by
    rw [(made_of _ _ _ _ _ hD).ts]
    exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h
  exact ⟨b1, sized_of b2, colsAt_of b3, stateAt_of b4,
    (groupTrees_colsFrom _ Dp.ts (logAt Dp.book) hnd b5).symm, b6, fitAll_of _ _ b7, b8, b9, b10,
    b11, allSay_of b12, b13, b14, fun rows gp h' => by
      rw [h'] at b15
      exact oldOk_of b15, b16⟩

/-- `SwitchPlan` (Johnson/Prover/Link/FormBehindAny.lean) as a test. -/
def switchPlanB (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) : Bool :=
  p.early && decide (p.answers = 1) && decide (stageAt p (j + 1) next = some n) &&
  decide (p.idx[j + 1]? = some (n.code, n.maskCode)) && decide (next.h ≤ next.k) &&
  H2K.Pub.csFitB cur next && decide ((K.base[n.code]?).map codeOf = some (sgOf next).C) &&
  decide ((K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z) &&
  decide (n.k = (sgOf next).h + (sgOf next).g) && decide (n.h = (sgOf next).h) && K.lengthsOk &&
  decide (2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63) &&
  decide (2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63) &&
  Own.treesCan K (swNotices p n false) &&
  H2K.Pub.oneTreeB K (OnBytes.Slice.sentOf (swTarget p n) (othersOf false n)) (sgOf next).C.a

theorem switchPlan_of_B {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {n : IoppStage}
    (h : switchPlanB p K j cur next n = true) : SwitchPlan p K j cur next n := by
  unfold switchPlanB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩ := h
  exact ⟨a1, a2, a3, a4, a5, H2K.Pub.csFit_of_B a6, a7, a8, a9, a10, a11, ⟨a12, a13⟩, a14,
    H2K.Pub.oneTree_of_B a15⟩

/-- The clauses for `test_left_all`, each with its name. -/
def allL (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : List (String × Bool) :=
  match J.p.nums.stages, (J.recB w fr (D 0)).pass with
  | a :: next :: nx' :: rest', .claim row L =>
    match gpOf J.p (J.recB w fr (D 0)) a L with
    | some Dp =>
      let Z := lettersOf J.p a next
      let K := coinsOf J.p.nums.stages C.hide C.rest
      let t₁ := t1At J.p K 0 a (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) D
      [("the place has rounds", (H2U.roundsOfNums J.p.nums).isSome),
       ("the place has oracle messages", (H2U.testOracles J.p.nums).isSome),
       ("the fresh table has come earlier", (J.rec₀ w fr).mask.isSome),
       ("all that is public in front of the first stage (Sh.firstB)",
         Sh.firstB J.p a next (((laidOf J.p).take 1).map (·.1))
           (((laidS J.p).take (1 + a.k)).map (·.1)) Z.i Z.n (nx' :: rest').isEmpty Z.dS Z.dC
           (testSh (J.rec₀ w fr))),
       ("the mark tidy", stTidyB (J.rec₀ w fr).st),
       ("no row has a written-out factor", stPlainB (J.rec₀ w fr).st),
       ("the front's test on the open rows", claimsB (J.rec₀ w fr)),
       ("BAT's challenges have the declared form",
         roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩]),
       ("TermAsks", termB J.p K (nx' :: rest') a next 1 (J.recB w fr (D 0)) (J.first w fr C) D Dp
         (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) row Z),
       ("the batching has one round",
         decide ((batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)),
       ("the batching opens nothing",
         decide ((batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)),
       ("RestAsks", restB J w fr C D a next (nx' :: rest') Dp R L
         ⟨Z.i.1, Z.i.2, a.k, a.h⟩ Z.n),
       ("nothing is left untested behind the batching",
         (ChainEnd.refuse (ChainEnd.untestedL (J.recB w fr (D 0)).st)).isOk),
       ("SwitchPlan at the first switch", switchPlanB J.p t₁.st.codes 0 a next Z.n),
       ("the plan from the second stage on (planFromOk)",
         planFromOk J.p (nx' :: rest') (0 + 1) next ((laidS J.p).drop (a.k + 3)) t₁.st.codes),
       ("the sorts of the items from the second stage on",
         decide (((laidS J.p).drop (a.k + 3)).map asked = bodyItems next (nx' :: rest'))),
       ("the challenges from the second stage on have the declared form",
         fitFromB D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3))]
    | none => [("the library's plain data of the group", false)]
  | _, _ => [("three stages or more, and a claim behind the batching", false)]

/-- All clauses of `allL` are true. -/
def allB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : Bool := (allL J w fr C D R).all (·.2)

/-- The names of the clauses of `allL` that are false. -/
def allNo (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : List String := ((allL J w fr C D R).filter (!·.2)).map (·.1)

/-- The clauses for `test_accepts_all`, each with its name: the text of `allL` without "nothing is
left untested behind the batching". -/
def coreL (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : List (String × Bool) :=
  match J.p.nums.stages, (J.recB w fr (D 0)).pass with
  | a :: next :: nx' :: rest', .claim row L =>
    match gpOf J.p (J.recB w fr (D 0)) a L with
    | some Dp =>
      let Z := lettersOf J.p a next
      let K := coinsOf J.p.nums.stages C.hide C.rest
      let t₁ := t1At J.p K 0 a (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) D
      [("the place has rounds", (H2U.roundsOfNums J.p.nums).isSome),
       ("the place has oracle messages", (H2U.testOracles J.p.nums).isSome),
       ("the fresh table has come earlier", (J.rec₀ w fr).mask.isSome),
       ("all that is public in front of the first stage (Sh.firstB)",
         Sh.firstB J.p a next (((laidOf J.p).take 1).map (·.1))
           (((laidS J.p).take (1 + a.k)).map (·.1)) Z.i Z.n (nx' :: rest').isEmpty Z.dS Z.dC
           (testSh (J.rec₀ w fr))),
       ("the mark tidy", stTidyB (J.rec₀ w fr).st),
       ("no row has a written-out factor", stPlainB (J.rec₀ w fr).st),
       ("the front's test on the open rows", claimsB (J.rec₀ w fr)),
       ("BAT's challenges have the declared form",
         roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩]),
       ("TermAsks", termB J.p K (nx' :: rest') a next 1 (J.recB w fr (D 0)) (J.first w fr C) D Dp
         (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) row Z),
       ("the batching has one round",
         decide ((batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)),
       ("the batching opens nothing",
         decide ((batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)),
       ("RestAsks", restB J w fr C D a next (nx' :: rest') Dp R L
         ⟨Z.i.1, Z.i.2, a.k, a.h⟩ Z.n),
       ("SwitchPlan at the first switch", switchPlanB J.p t₁.st.codes 0 a next Z.n),
       ("the plan from the second stage on (planFromOk)",
         planFromOk J.p (nx' :: rest') (0 + 1) next ((laidS J.p).drop (a.k + 3)) t₁.st.codes),
       ("the sorts of the items from the second stage on",
         decide (((laidS J.p).drop (a.k + 3)).map asked = bodyItems next (nx' :: rest'))),
       ("the challenges from the second stage on have the declared form",
         fitFromB D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3))]
    | none => [("the library's plain data of the group", false)]
  | _, _ => [("three stages or more, and a claim behind the batching", false)]

/-- All clauses of `coreL` are true. -/
def coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : Bool := (coreL J w fr C D R).all (·.2)

/-- The names of the clauses of `coreL` that are false. -/
def coreNo (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) : List String := ((coreL J w fr C D R).filter (!·.2)).map (·.1)

/-- **Where `coreB` is true, the block's decision accepts.** -/
theorem accepts_of_coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (R : PlainRows) (h : coreB J w fr C D R = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  unfold coreB coreL at h
  split at h
  · rename_i a next nx' rest' row L hst hp
    split at h
    · rename_i Dp hD
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, cS, c14, c15, c16⟩ := h
      obtain ⟨ds, hrd⟩ := Option.isSome_iff_exists.1 c1
      obtain ⟨os, hor⟩ := Option.isSome_iff_exists.1 c2
      obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 c3
      unfold Sh.firstB at c4
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at c4
      obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := c4
      have f4' : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true := by
        have e : (testSh (J.rec₀ w fr)).mask.isSome = true := c3
        rw [if_pos e] at f4
        exact f4
      have hTail := planFrom_of_ok J.p _ _ _ _ _ c14
      have Pl := switchPub_of f2
      exact test_accepts_all J w fr C D a next (nx' :: rest') ds os hst hrd hor Dp _
        (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
        (lettersOf J.p a next).dC f1 hm c5 (fun G hG => runRows_plain c6 hG) c7 Pl f3 f4' c8
        (termAsks_of _ _ _ _ _ _ _ _ _ _ _ row L hp hD c9) c10 c11 R
        (fun row' L' h' => by
          rw [hp] at h'
          injection h' with e1 e2
          subst e1 e2
          exact restAsks_of J w fr C D a next _ Dp R row L _ _ hD c12) (switchPlan_of_B cS)
        ⟨hTail, c15⟩ (fitFrom_of_B D _ _ c16)
    · simp at h
  · simp at h

/-- **Where `allB` is true, the block's decision accepts, and nothing is left untested after it.**
-/
theorem accepts_of_allB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (R : PlainRows) (h : allB J w fr C D R = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧
      ChainEnd.NothingLeft t'.st := by
  unfold allB allL at h
  split at h
  · rename_i a next nx' rest' row L hst hp
    split at h
    · rename_i Dp hD
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, cS, c14, c15, c16⟩ := h
      obtain ⟨ds, hrd⟩ := Option.isSome_iff_exists.1 c1
      obtain ⟨os, hor⟩ := Option.isSome_iff_exists.1 c2
      obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 c3
      unfold Sh.firstB at c4
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at c4
      obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := c4
      have f4' : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true := by
        have e : (testSh (J.rec₀ w fr)).mask.isSome = true := c3
        rw [if_pos e] at f4
        exact f4
      have hTail := planFrom_of_ok J.p _ _ _ _ _ c14
      have Pl := switchPub_of f2
      have hleft : ChainEnd.NothingLeft (J.recB w fr (D 0)).st := by
        refine ChainEnd.untested_spec _ ?_
        cases hu : ChainEnd.refuse (ChainEnd.untestedL (J.recB w fr (D 0)).st) with
        | ok _ => rfl
        | error _ =>
          rw [hu] at c13
          cases c13
      exact test_left_all J w fr C D a next (nx' :: rest') ds os hst hrd hor Dp _
        (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
        (lettersOf J.p a next).dC f1 hm c5 (fun G hG => runRows_plain c6 hG) c7 Pl f3 f4' c8
        (termAsks_of _ _ _ _ _ _ _ _ _ _ _ row L hp hD c9) c10 c11 R
        (fun row' L' h' => by
          rw [hp] at h'
          injection h' with e1 e2
          subst e1 e2
          exact restAsks_of J w fr C D a next _ Dp R row L _ _ hD c12) hleft (switchPlan_of_B cS)
        ⟨hTail, c15⟩ (fitFrom_of_B D _ _ c16)
    · simp at h
  · simp at h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.switchPlan_of_B
#print axioms ProofFile.Honest.K12.termAsks_of
#print axioms ProofFile.Honest.K12.restAsks_of
#print axioms ProofFile.Honest.K12.accepts_of_coreB
#print axioms ProofFile.Honest.K12.accepts_of_allB
#print axioms ProofFile.Honest.K12.Letters
#print axioms ProofFile.Honest.K12.lettersOf
#print axioms ProofFile.Honest.K12.termB
#print axioms ProofFile.Honest.K12.restB
#print axioms ProofFile.Honest.K12.switchPlanB
#print axioms ProofFile.Honest.K12.allL
#print axioms ProofFile.Honest.K12.allB
#print axioms ProofFile.Honest.K12.allNo
#print axioms ProofFile.Honest.K12.coreL
#print axioms ProofFile.Honest.K12.coreB
#print axioms ProofFile.Honest.K12.coreNo
