-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlanLaw.lean: the law `core_inv` (Sim/ClaimBody.lean) at a
job's values, with the one hypothesis of `core_inv` that ranges over every coin (hbody) derived from
four hypotheses, sorted by what they read: the plan's half, a test with code (a function to `Bool`)
that reads only the place, the table of codes and a number of trees (`planB`); the shape of the
state of type `T12` on entry, after the batching and after the first fold (`ShapeAsks`); the
challenges' form (`FormAsks`); the prover's data (`DataAsks`). The four are defined in
Johnson/Desc/ProofFile/Honest/K12/PlanB.lean; below: the four sorts. So at a place that is written
out the plan's half can be proved once, by an evaluation, and no test with code has to be run at an
input, as `coreB` (…/K12/AllB.lean) has to be for `law_of_coreB` (Sim/AllRest.lean). The same
equation of two texts' laws. No property is claimed, and it is no sentence on a simulator. Three
theorems, stated for every job J, input w, front fr, coins C and challenges D. Sim/ExactPlan.lean,
which imports this file, calls `behind_of_plan`.

In this head: a job is a `TestJob` (Johnson/Desc/ProofFile/Honest/K12/Test.lean): what a caller
supplies for its proximity test: the place `J.p`, and functions of the prover's input w and of the
front fr, among them the state on entry `rec₀`, the first stage's rows `rows₀` and the trees that
hold them `trees₀`. A place is a `P12` (Johnson/Desc/K12/Frame.lean): a test's numbers, among them
its list of stages `nums.stages`; it is written out where it is a closed term. The front is a
`Front` (Johnson/Desc/ProofFile/Honest/Sum.lean): what precedes the test. A stage is a
`Fmt.M1.Stage`, with codes C and Z and numbers k and h; its sizes are `sgOf` of it
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. Every stage but the last has a fold and then
a switch to the next stage. D gives the sampled challenges by the round's number; the batching is
the round "BAT", number 0. A reading round is a round whose challenge samples positions. The table
of codes K is a `Codes` (OnBytes/Iop/Ground.lean). Dp is the library's plain data (`Plain`,
Johnson/Desc/K12/Law/FirstOk.lean); `Dp.ts` lists the numbers of the group's trees, cc gives these
trees' columns, and R gives the prover's rows as plain functions (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). C is a `TestCoins` (Test.lean): the switches' coins are its
field `rest`, and a family of them is a function c : ℕ → `GE`; the carried coins are the members'
stretches (`mem`: the coins of the group's oracle messages), the first fold's coefficients (`hide`)
and its table's tails (`tails`). The rows are `J.first w fr C`. tB is `J.recB w fr (D 0)`
(Test.lean): `J.rec₀ w fr`, advanced by the `decide` functions of `guardedProximityTestParts.front` and
`guardedProximityTestParts.bat`. The term is `testAll` (Test.lean) with the definitions of which it is made; the
term's rounds that `ShapeAsks` reads are the first fold's, `rfAt`
(Johnson/Desc/K12/Honest/FirstYes.lean) inside `tFold` (PlanB.lean): computed from tB, the rows,
`C.hide` and the challenges. The invariant of the later stages is `BodyInv`
(Johnson/Prover/Link/BodyInv.lean) at `PlanAll` (Johnson/Prover/Link/BodyCloseB.lean). The two views
`realOwn` and `zeroOwn` and the type `OwnCs` are defined in Sim/CoreOwn.lean, whose head says what a
text is and what is shown of it. `realOwn`: what is shown of the text at the rows P₀, at coins by
number. `zeroOwn`: what is shown of the text at rows 0 with the one item laid anew, at coins by
number. `OwnCs`: the coins that the second part takes; the second part is `restPart`
(Johnson/Desc/ProofFile/Honest/K12/Parts.lean), a `Part` of the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean). A law is a distribution, here `PMF.map` of a view over
`Prob.unif`; the law, as the name of a theorem, is the equation of the two. The tree in front is the
one tree of htr below; colR is its written column, and colF, on the right side, is a free parameter
in the place of colR. A letter is a free parameter, or a field of a structure. Asked: taken as a
hypothesis. To lay: to put or to make. To stand: to occur. To hang on: to depend on. In front of,
behind, beside: before, after, next to.

  `law_of_plan`: the law, from the four sorts. In Lean: `PMF.map` of `realOwn` at `(stretchOf c).e`
    and `PMF.map` of `zeroOwn` at `(stretchOf c).e`, both over
    `Prob.unif (OwnCs a (next :: nx' :: rest'))`, are equal. Both views are at `J.p` for p,
    `laidS J.p` for l, `J.recB w fr (D 0)` for tB, `J.first w fr C` for P₀ and `C.hide` for hide;
    `realOwn` is at colR, `zeroOwn` at colF. Under the hypotheses below
  `wanted_of_plan`: the four sorts ⟹ the invariant of the later stages holds behind the first switch
    (`Wanted`, …/K12/BodyInvFirst.lean) at every family of the switches' coins. In Lean: under hP,
    S, F and Dt, for every c : ℕ → `GE`, the place's stages are some a :: next :: nx' :: rest', and
    `Wanted` holds at J, w, fr, D, these stages, Dp, cc and at C with c for its field `rest`.
    General in the number of trees in `Dp.ts`
  `behind_of_plan`: the same in the form of Sim/ClaimBody.lean (`BehindFirst`), at one tree in
    front. In Lean: under hP, S, F, Dt, hst and htr, `BehindFirst` holds at every c : ℕ → `GE`, at
    the values that `law_of_plan` gives to p, l, tB, P₀ and hide, and at colR

By what. The proof of `wanted_of_plan` is that of `accepts_of_plan` (…/K12/PlanB.lean), with
`bodyInv_behind_first` (…/K12/BodyInvFirst.lean) called in the place of `test_accepts_all`
(…/K12/WholeAll.lean), and with `termAsks_rest`, `restAsks_rest` and `fold_rest` (Sim/AllRest.lean),
which carry what is derived at `C.rest` to every c. `behind_of_plan` calls `wanted_of_plan` and
rewrites the group's trees to the one tree by `DataAsks.trees` and htr. `law_of_plan` is `core_inv`
with `behind_of_plan` at `(stretchOf c).e` for hbody.

Hypotheses of `law_of_plan`.
- hP: `planB J.p K Dp.ts.length = true`: every clause of `planL` (PlanB.lean) passes at the place,
  at K and at the number of trees in `Dp.ts`. Where the place has fewer than three stages it is
  false.
- S: `ShapeAsks J w fr C D K Dp`: clauses on `J.rec₀ w fr`, on tB and on `tFold J w fr C D`.
- F: `FormAsks J w fr C D`: the challenges have the declared form at "BAT", at the first fold's and
  the first switch's rounds as the term shows them, and from the second stage on; the first switch's
  positions are as many as stated and in range; a clause on the words of the seed's factor.
- Dt: `DataAsks J w fr C D Dp cc R`: `ColsAt`, `StateAt`, the job's trees are the group's
  (`groupTrees`, Johnson/Desc/K12/Honest/GroupState.lean), `AllSay` at `wordsAt`.
- hst: the place's stages are a :: next :: nx' :: rest'.
- htr: the job's trees are one tree, of the depth `(sgOf a).C.a`, with the column colR.
- hF: `FitsBody D (next :: nx' :: rest') a 1` (Johnson/LinkSim/AtText/SpecShift.lean).
- hlow: h ≤ k at every stage in next :: nx' :: rest'.
- hcol: colR and colF are equal at every position in
  `Fmt.listOf (openedAt D (next :: nx' :: rest') a 1)` (`openedAt`,
  Johnson/LinkSim/AtText/SpecStage.lean).
- hasks: for every i, each position in the first list of asks at i is in
  `openedTr D (next :: nx' :: rest') a 1 (1 + (h + g) + i)` (Sim/CoreText.lean), with h and g from
  the first stage's sizes.
hF, hlow, hcol and hasks are those of `core_inv`; clause by clause: the head of Sim/CoreOwn.lean.

Limits.
- `rec₀` is a field of the job J, and J is a free parameter: no statement that this state is the
  verifier's. "The verifier's state" names below what the description's `decide` functions compute
  from `J.rec₀ w fr`.
- On the right side the rows and the first fold's coefficients still stand, through the verifier's
  state behind the first fold alone (`entryOf`, Sim/CoreLaw.lean): a function of the state tB behind
  the batching and of the first fold's rounds as they are shown. And tB is `J.recB w fr (D 0)`: the
  job's letter `rec₀` takes the input by type.
- `ShapeAsks`, `FormAsks` and `DataAsks` are asked, at one value of the input, the front, the
  carried coins and the challenges.
- `DataAsks` reads the input and another part's coins.
- `ShapeAsks`' clauses behind the first fold hang, by type, on the term's rounds.
- Beside them: `FitsBody` · h ≤ k behind the first stage · one tree in front, of the first stage's
  depth · the positions asked are among those that the next reading round samples.
- The reach is that of `test_accepts_all` (…/K12/WholeAll.lean), but for the stages, of which that
  theorem asks two or more and `planB` three: three stages or more; the first fresh table has come
  earlier (`ShapeAsks.came`); no row taken in has a written-out factor (`ShapeAsks.plainRows`).
- The law's hypothesis on public numbers, `planB`, at one tree, which hP, htr and `DataAsks.trees`
  together ask for, is proved at one of the library's nine closed places, the key file's test on the
  ranges (`planB_KR`, …/K12/AtKeyRanges.lean). No value is shown to meet `ShapeAsks` and `DataAsks`
  at that place. The nine: by reading, off the head of Sim/ReachAt.lean.
- That the hypotheses hold together at any values is not shown in this file. No statement of this
  library shows them together at any values, and none shows that the two sides differ.
- At the level of oracle messages: no root, salt or hash. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.AllRest
import Johnson.Desc.ProofFile.Honest.K12.PlanB

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB)
open OnBytes.LinkSim.AtText (FitsBody openedAt)

attribute [local instance] csNonempty

variable {W X : Type}

/-- **The four sorts give the invariant behind the first switch, at every family of the switches'
coins.** The four sorts are hP, S, F and Dt, and c is the family. The invariant is `Wanted`
(…/K12/BodyInvFirst.lean), at C with c for its field `rest`. -/
theorem wanted_of_plan (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R) (c : ℕ → GE) :
    ∃ a next nx' rest', J.p.nums.stages = a :: next :: nx' :: rest' ∧
      Wanted J w fr { C with rest := c } D a next (nx' :: rest') Dp cc := by
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
    have A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) (nx' :: rest') a next 1
        (J.recB w fr (D 0)) (J.first w fr C) D Dp cc
        ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
        (lettersOf J.p a next).dS (lettersOf J.p a next).dC :=
      ⟨fun row L h => ⟨(s7 row L h).1, (s7 row L h).2.1⟩, p6, p7, d1.width, f5, two_of_length _ p8,
        f2, f3, fun rows gp h => (s10 rows gp h).1, p9, p10, p11, p12⟩
    have V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
        RestAsks J w fr C D a next (nx' :: rest') Dp cc R row L
          ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          (lettersOf J.p a next).n := fun row L h =>
      ⟨p15, sized_of p16, d1, d2, d3, f6, fitAll_of _ _ p17, (s7 row L h).2.2.1,
        (s7 row L h).2.2.2.1, (s7 row L h).2.2.2.2.1, (s7 row L h).2.2.2.2.2,
        by rw [front_getD]; exact d4 row L h, p18,
        by
          show ((t1At J.p _ 0 a (laidS J.p) 1 _ _ D).st.codes.mask.getD _ default).ell = a.Z.l
          rw [s9]
          exact p19,
        fun rows gp h' => (s10 rows gp h').2, f7⟩
    have s9' : (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes = K :=
      (congrArg (fun x => (aRec1 J.p 0 a (laidS J.p) (J.recB w fr (D 0)) x).st.codes)
        (fold_rest J.p.nums.stages C.hide c C.rest a 1 (J.first w fr C) _ D)).trans s9
    refine ⟨a, next, nx', rest', hst, ?_⟩
    refine bodyInv_behind_first J w fr { C with rest := c } D a next (nx' :: rest') ds os hst hrd
      hor Dp cc (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 (fun G hG => runRows_plain s5 hG) s6 Pl p4 p5 f1
      (termAsks_rest A c) p13 p14 R (fun row L h => restAsks_rest (V row L h) c) ?_ ⟨?_, p22⟩ f4
    · show SwitchPlan J.p (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1
        (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next _
      rw [s9']
      exact switchPlan_of_B p20
    · show PlanFrom J.p (nx' :: rest') (0 + 1) next ((laidS J.p).drop (a.k + 3))
        (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
          (J.first w fr C) D).st.codes
      rw [s9']
      exact planFrom_of_ok J.p _ _ _ _ _ p21
  · simp at hP

/-- The invariant behind the first switch, in Sim/ClaimBody.lean's form, at every family of the
switches' coins. The form is `BehindFirst`. htr: the job's trees are one tree, of the first stage's
depth, with the column colR. -/
theorem behind_of_plan (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (colR : ℕ → List UInt64)
    (htr : J.trees₀ w fr C.mem (J.first w fr C) = [((sgOf a).C.a, colR)]) (c : ℕ → GE) :
    BehindFirst J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
      colR D c := by
  obtain ⟨a', n', x', r', hst', hW⟩ := wanted_of_plan J w fr C D K Dp cc R hP S F Dt c
  rw [hst] at hst'
  injection hst' with e1 e2
  injection e2 with e2 e3
  injection e3 with e3 e4
  subst e1 e2 e3 e4
  have hT' : groupTrees Dp.ts (logAt Dp.book) cc = [((sgOf a).C.a, colR)] := Dt.trees.symm.trans htr
  unfold Wanted at hW
  unfold BehindFirst
  rw [← hst, ← hT']
  exact hW

/-- **The law, from the four sorts.** It is `core_inv` (Sim/ClaimBody.lean) at the job's values. The
same equation of two texts' laws. No property is claimed, and it is no sentence on a simulator.
Hypotheses and limits: the head of this file. -/
theorem law_of_plan (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (colR colF : ℕ → List UInt64)
    (htr : J.trees₀ w fr C.mem (J.first w fr C) = [((sgOf a).C.a, colR)])
    (hF : FitsBody D (next :: nx' :: rest') a 1) (hlow : ∀ st ∈ next :: nx' :: rest', st.h ≤ st.k)
    (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: nx' :: rest') a 1), colR x = colF x)
    (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      q ∈ openedTr D (next :: nx' :: rest') a 1 (1 + ((sgOf a).h + (sgOf a).g) + i)) :
    PMF.map (fun c : OwnCs a (next :: nx' :: rest') =>
        realOwn J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
          colR D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs a (next :: nx' :: rest'))) =
      PMF.map (fun c : OwnCs a (next :: nx' :: rest') =>
        zeroOwn J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
          colF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs a (next :: nx' :: rest'))) :=
  core_inv J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide colR
    colF D dep n asks hF hlow hcol
    (fun c => behind_of_plan J w fr C D K Dp cc R hP S F Dt a next nx' rest' hst colR htr
      (stretchOf c).e) hasks

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.wanted_of_plan
#print axioms ProofFile.Honest.K12.behind_of_plan
#print axioms ProofFile.Honest.K12.law_of_plan
