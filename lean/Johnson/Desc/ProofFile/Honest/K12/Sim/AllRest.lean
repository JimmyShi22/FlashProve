-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/AllRest.lean: where one test with code on a proximity test's
place, input, front, carried coins and challenges says "true" (`coreB`,
Johnson/Desc/ProofFile/Honest/K12/AllB.lean), the law `core_inv` (Sim/ClaimBody.lean) holds, with no
premise left that is asked at every coin. The same equation of two texts' laws. No property is
claimed, and it is no sentence on a simulator. The main theorem is `law_of_coreB`. It is stated for
every job J and for all values of the other parameters that meet the hypotheses below. Theorems
only, no definition. Sim/PlanLaw.lean, which imports this file, calls `fold_rest`, `termAsks_rest`
and `restAsks_rest`.

In this head: a job J (`TestJob`, Johnson/Desc/ProofFile/Honest/K12/Test.lean) is what a caller
supplies for its test. Its place `J.p` (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the
place of a proximity test, among them the list of stages `J.p.nums.stages`. A stage is a
`Fmt.M1.Stage`, with codes C and Z and numbers k and h; its sizes are `sgOf` of it
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. A main row's tail has C.r entries, a mask
row's Z.r. Every stage but the last has a fold and then a switch to the next stage; a switch has two
rounds (`aSwitch`, Johnson/Desc/K12/Honest/Stages.lean). A reading round is a round whose challenge
samples positions. w is the input. The front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is
what a caller's functions are given of the run besides the input: the challenges, what was handed on
and the rounds shown before the test. C is a `TestCoins` (Test.lean), with four fields: `hide`, the
first fold's coefficients; `tails`, its table's tails; `mem`, the members' stretches, that is the
coins of the group's oracle messages by the member's number; `rest`, the switches' coins. A family
of the switches' coins is a function c : ℕ → `GE`, put for `C.rest` by `{ C with rest := c }`. D
gives the challenges by the round's number; "BAT", the batching, is round 0. R (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean), the prover's rows as plain functions, is one more argument
of `coreB`. A test with code is a function with values in `Bool`; the test is `coreB`; an arm of it
is a `match` or a named clause in `coreL`, `termB` or `restB` (AllB.lean). `J.rec₀ w fr` is the
state on entry. tB is `J.recB w fr (D 0)` (Test.lean): that state, advanced by the `decide`
functions of the description's front and batching; where one of the two rejects, the state before it
is kept. The first part is `firstPart`, "BAT" and the first fold; the second part is `restPart`, all
the rest (both Johnson/Desc/ProofFile/Honest/K12/Parts.lean). The second part's own coins are the
switches'; with their count in the type they are `OwnCs` (Sim/CoreOwn.lean). This file names neither
part. The invariant of the later stages is `BodyInv` (Johnson/Prover/Link/BodyInv.lean). The door's
tests are `Sh.doorB` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean) with `stTidyB`, plain rows and
`claimsB`: tests on the state on entry. The two texts, and what is shown of them, are explained in
the head of Sim/CoreOwn.lean: `realOwn` is the left side, `zeroOwn` the right side. A law is a
distribution, here `PMF.map` of one of the two over `Prob.unif`. As the name of a theorem, the law
is the equation of the two; the law of `coreB` is the theorem whose premises the test's clauses
give, here `bodyInv_behind_first` (Johnson/Desc/ProofFile/Honest/K12/BodyInvFirst.lean), and its end
is its conclusion, `Wanted`. The later stages' plan and form are the clauses of `coreL` with
`planFromOk` and with `fitFromB`. The library's closed places are closed terms of type `P12`. A
condition is a predicate on what precedes a part (the parameter `On` in
Johnson/Desc/ProofFile/Honest/Small/Field.lean), which is not given the part's own challenges; it
can hold a hypothesis only if it is given all that the hypothesis reads. In the limits, "it" is
`coreB` from "`coreB` is no public premise" to "Beside it are asked", and `law_of_coreB` in "Its
reach at the library's closed places" and in "It speaks of". A letter is a free parameter, or a
field of a structure. A premise is a hypothesis; it is asked where it is a hypothesis. To stand: to
occur. To hang on: to depend on. In front of, behind: before, after. Beside: in addition to. Alone:
only. To the letter: word for word.

  `law_of_coreB`: the law. In Lean: under the seven hypotheses below, `PMF.map` of `realOwn` at the
    column colR and `PMF.map` of `zeroOwn` at the column colF, each at `(stretchOf c).e` and over
    `Prob.unif (OwnCs a (next :: nx' :: rest'))`, are equal. Both sides are at the place `J.p`, the
    declared rounds after "BAT" (`laidS J.p`), the state `J.recB w fr (D 0)`, the rows
    `J.first w fr C` and the coefficients `C.hide`; dep, n and asks are free parameters
  `behind_of_coreB`: so the invariant behind the first switch, in Sim/ClaimBody.lean's form. In
    Lean: under h, hst and htr below, `BehindFirst` (Sim/ClaimBody.lean) holds at these same
    arguments, at colR and at every c : ℕ → `GE`
  `wanted_trees`: what the test's "true" gives, at every family of the switches' coins: `Wanted`
    (…/K12/BodyInvFirst.lean) and that the job's trees are the group's: the proof is that of
    `wanted_of_coreB` (…/K12/BodyInvMember.lean), which hands them out at the test's own family,
    with two calls more. In Lean: where `coreB J w fr C D R = true`, for every c there are stages a,
    next, nx', rest' and plain data Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) such that the
    place's stages are a :: next :: nx' :: rest', `Wanted` holds at `{ C with rest := c }`, and
    `J.trees₀ w fr C.mem (J.first w fr C)` is `groupTrees` (Johnson/Desc/K12/Honest/GroupState.lean)
    of its own columns. The two calls are of `termAsks_rest` and `restAsks_rest`
  `fold_rest`, `fitS_any`, `termAsks_rest`, `restAsks_rest`: no coin of a switch is read. One by one
    in the next four entries
  `fold_rest`: `aFold` (Stages.lean) at stage number 0 is the same at `coinsOf st hide c` and at
    `coinsOf st hide c'` (`coinsOf`: Johnson/Desc/ProofFile/Honest/K12/Coins.lean)
  `fitS_any`: `roundsFit [dS, dC]` (Johnson/Desc/Block.lean) of the two rounds `aSwitch cur o D x`,
    mapped by `noDigest`, is the same at every sent value x
  `termAsks_rest`: `TermAsks` (Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) at `coinsOf st hide c`
    gives `TermAsks` at `coinsOf st hide c'`, for every c', the other arguments unchanged
  `restAsks_rest`: `RestAsks` (Johnson/Desc/ProofFile/Honest/K12/WholeShape.lean) at C gives
    `RestAsks` at `{ C with rest := c }`, for every c, the other arguments unchanged

By what. `coreB` takes the switches' coins among its arguments. What its "true" gives does not read
them: of what hangs on them the premises of its law ask only that the first switch's two rounds have
the declared form, which reads no sent value (`termAsks_rest`, `restAsks_rest`). So from its "true"
at one family of these coins its law's end (the invariant of the later stages holds behind the first
switch) holds at every family. `fold_rest` and `fitS_any` hold by `rfl`; `termAsks_rest` rewrites by
the two; `restAsks_rest` gives back the fields as they are. `wanted_trees` unfolds `coreB` and calls
`bodyInv_behind_first` at `{ C with rest := c }`; the hypotheses of that call come from the test's
clauses by `termAsks_of`, `restAsks_of` and `switchPlan_of_B` (AllB.lean), `switchPub_of`
(Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean), `runRows_plain` (TestDoor.lean),
`planFrom_of_ok` (Johnson/Prover/Link/StepPlanOk.lean) and `fitFrom_of_B`
(Johnson/Desc/K12/Honest/FitFromB.lean). `behind_of_coreB` unfolds `Wanted` and `BehindFirst` and
rewrites the trees by htr. `law_of_coreB` calls `core_inv`, with `behind_of_coreB` at
`(stretchOf c).e` for its hypothesis at every coin.

Hypotheses of `law_of_coreB`.
- h: `coreB J w fr C D R = true`.
- hst: the place's stages are a :: next :: nx' :: rest': three or more.
- htr: `J.trees₀ w fr C.mem (J.first w fr C)` is one tree, of the depth `(sgOf a).C.a`, with the
  written column colR.
- hF: `FitsBody D (next :: nx' :: rest') a 1` (Johnson/LinkSim/AtText/SpecShift.lean); its clauses
  are listed in the limits.
- hlow: h ≤ k at every stage in next :: nx' :: rest'.
- hcol: colR and colF are equal at every position in
  `Fmt.listOf (openedAt D (next :: nx' :: rest') a 1)` (`openedAt`,
  Johnson/LinkSim/AtText/SpecStage.lean): the positions that the second round of the first switch
  samples, taken modulo 2^a, a being the first stage's `C.a`.
- hasks: for every i, each position in the first list of asks at i is in
  `openedTr D (next :: nx' :: rest') a 1 (1 + (h + g) + i)` (Sim/CoreText.lean), with h and g from
  the first stage's sizes.

Limits.
- `rec₀` is a field of the job, and the job is a free parameter: no statement that the state on
  entry is the verifier's. "The verifier's state" names below what the description's fold computes
  from tB.
- On the right side the rows and the first fold's coefficients still stand, through the verifier's
  state behind the first fold alone (`entryOf`, Sim/CoreLaw.lean): a function of the state tB behind
  the batching and of the first fold's rounds as they are shown.
- And tB is `J.recB w fr (D 0)`: the job's letter `rec₀` takes the input by type: so the input
  stands on the right side in tB too; nothing here narrows it.
- `coreB` is no public premise: it reads the input and the carried coins (the members' stretches,
  the first fold's coefficients and its table's tails), at one value.
- Toward a sentence at every run it is again a premise at every value: of the input, and of another
  part's coins.
- Three of its arms read a verdict of the verifier's through what the state passes (a claim behind
  the batching; single rows behind the first fold, twice): all in front of the first switch; none
  reads a coin of the second part.
- "No acceptance is asked" is true of `BodyInv`, not to the letter of `coreB`.
- It is sufficient, not necessary; its reach is its own law's (three stages or more; the first fresh
  table has come earlier).
- Beside it are asked: `FitsBody` (each stage fits the next; no list of sampled positions, counted
  with repeats, is longer than a row's tail; the packing has room; h = g = 0 at the last stage) ·
  h ≤ k behind the first stage · one tree in front, of the first stage's depth · the positions asked
  are among those that the next reading round samples.
- Its reach at the library's closed places: the premises on public numbers hold at three of nine
  (the proof file's last test behind the links · the key file's test on the ranges · a copy's test);
  at the other six the first reading round opens two or three trees (Sim/ReachAt.lean).
- `coreB` reads the challenges too, the second part's own among them (the later stages' plan and
  form): a condition that is not handed these cannot hold it; the premise sorted by what it reads:
  Sim/PlanLaw.lean. By their text, `termB` and `restB` (AllB.lean) read the challenges of the first
  switch's two rounds too.
- It speaks of the second part and its own coins alone: of no run of coins that is lent, and not of
  the first part.
- That the seven hypotheses hold together at any values is not shown in this file. They have no
  values that meet them together in the library yet, and no file in the library shows that the two
  sides differ.
- At the level of oracle messages: no root, salt or hash.
- Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ClaimBody
import Johnson.Desc.ProofFile.Honest.K12.BodyInvMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain)
open OnBytes.LinkSim.AtText (FitsBody openedAt)

attribute [local instance] csNonempty

variable {W X : Type}

/-! ## 1 What the test's "true" gives does not read the switches' coins -/

/-- The first fold's rounds read no coin of a switch. In Lean: `aFold` at stage number 0 is the same
at `coinsOf st hide c` and at `coinsOf st hide c'`. -/
theorem fold_rest (st : List Fmt.M1.Stage) (hide c c' : ℕ → GE) (a : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    aFold (coinsOf st hide c) 0 a o P row D = aFold (coinsOf st hide c') 0 a o P row D := rfl

/-- Whether a switch's two rounds have the declared form reads no sent value. In Lean:
`roundsFit [dS, dC]` of `aSwitch cur o D x`, mapped by `noDigest`, is the same at every x. -/
theorem fitS_any (dS dC : Fmt.DeclaredRound) (cur : Fmt.M1.Stage) (o : ℕ) (D : ℕ → Fmt.Drawn)
    (x y : GE) :
    roundsFit [dS, dC] ((aSwitch cur o D x).map noDigest) =
      roundsFit [dS, dC] ((aSwitch cur o D y).map noDigest) := rfl

/-- What is asked beside the door's tests reads no coin of a switch. In Lean: `TermAsks` at
`coinsOf st hide c` gives `TermAsks` at `coinsOf st hide c'`, for every c'. -/
theorem termAsks_rest {p : P12} {st : List Fmt.M1.Stage} {hide c : ℕ → GE}
    {rest : List Fmt.M1.Stage} {a next : Fmt.M1.Stage} {o : ℕ} {tB : T12} {P : PS}
    {D : ℕ → Fmt.Drawn} {Dp : Plain} {cc : ℕ → ℕ → List UInt64} {cu : IoppStage}
    {dS dC : Fmt.DeclaredRound} (A : TermAsks p (coinsOf st hide c) rest a next o tB P D Dp cc cu dS dC)
    (c' : ℕ → GE) : TermAsks p (coinsOf st hide c') rest a next o tB P D Dp cc cu dS dC := by
  have eF : rfAt (coinsOf st hide c') 0 a o tB P D = rfAt (coinsOf st hide c) 0 a o tB P D :=
    fold_rest st hide c' c a o P _ D
  have eT : t1At p (coinsOf st hide c') 0 a (laidS p) o tB P D =
      t1At p (coinsOf st hide c) 0 a (laidS p) o tB P D :=
    congrArg (aRec1 p 0 a (laidS p) tB) eF
  refine ⟨A.plain, A.hk, A.stage, A.width, A.range, A.cut, ?_, ?_, ?_, A.nF, A.oF, A.nS, A.oS⟩
  · rw [eF]
    exact A.fitF
  · exact (fitS_any dS dC a o D _ _).trans A.fitS
  · rw [eT]
    exact A.pub

/-- What the first stage's values' laws ask reads no coin of a switch. In Lean: `RestAsks` at C
gives `RestAsks` at `{ C with rest := c }`, for every c. -/
theorem restAsks_rest {J : TestJob W X} {w : W} {fr : Front X} {C : TestCoins} {D : ℕ → Fmt.Drawn}
    {a next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {Dp : Plain} {cc : ℕ → ℕ → List UInt64}
    {R : PlainRows} {row : GroupRow} {L : GroupLayout} {cu nx : IoppStage}
    (V : RestAsks J w fr C D a next rest Dp cc R row L cu nx) (c : ℕ → GE) :
    RestAsks J w fr { C with rest := c } D a next rest Dp cc R row L cu nx :=
  ⟨V.hk', V.sized, V.cols, V.state, V.trees, V.count, V.fitAll, V.layK, V.layH, V.lenC, V.lenZ,
    V.allSay, V.room, V.ell, V.old, V.words⟩

/-! ## 2 What the test's "true" gives -/

/-- `Wanted` at every family of the switches' coins, and that the job's trees are the group's. -/
theorem wanted_trees (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (R : PlainRows) (h : coreB J w fr C D R = true) (c : ℕ → GE) :
    ∃ a next nx' rest' Dp, J.p.nums.stages = a :: next :: nx' :: rest' ∧
      Wanted J w fr { C with rest := c } D a next (nx' :: rest') Dp
        (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) ∧
      J.trees₀ w fr C.mem (J.first w fr C) = groupTrees Dp.ts (logAt Dp.book)
        (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) := by
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
      refine ⟨a, next, nx', rest', Dp, hst, ?_,
        (restAsks_of J w fr C D a next _ Dp R row L _ _ hD c12).trees⟩
      exact bodyInv_behind_first J w fr { C with rest := c } D a next (nx' :: rest') ds os hst hrd
        hor Dp _ (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
        (lettersOf J.p a next).dC f1 hm c5 (fun G hG => runRows_plain c6 hG) c7 Pl f3 f4' c8
        (termAsks_rest (termAsks_of _ _ _ _ _ _ _ _ _ _ _ row L hp hD c9) c) c10 c11 R
        (fun row' L' h' => by
          rw [hp] at h'
          injection h' with e1 e2
          subst e1 e2
          exact restAsks_rest (restAsks_of J w fr C D a next _ Dp R row L _ _ hD c12) c)
        (switchPlan_of_B cS) ⟨hTail, c15⟩ (fitFrom_of_B D _ _ c16)
    · simp at h
  · simp at h

/-! ## 3 The law -/

/-- The invariant behind the first switch, at every family of the switches' coins. -/
theorem behind_of_coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) (h : coreB J w fr C D R = true) (a next nx' : Fmt.M1.Stage)
    (rest' : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: nx' :: rest')
    (colR : ℕ → List UInt64)
    (htr : J.trees₀ w fr C.mem (J.first w fr C) = [((sgOf a).C.a, colR)]) (c : ℕ → GE) :
    BehindFirst J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
      colR D c := by
  obtain ⟨a', n', x', r', Dp, hst', hW, hT⟩ := wanted_trees J w fr C D R h c
  rw [hst] at hst'
  injection hst' with e1 e2
  injection e2 with e2 e3
  injection e3 with e3 e4
  subst e1 e2 e3 e4
  have hT' : groupTrees Dp.ts (logAt Dp.book)
      (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) = [((sgOf a).C.a, colR)] :=
    hT.symm.trans htr
  unfold Wanted at hW
  unfold BehindFirst
  rw [← hst, ← hT']
  exact hW

/-- **The law, from the test's "true".** The conclusion is that of `core_inv` (Sim/ClaimBody.lean).
No property is claimed, and it is no sentence on a simulator. -/
theorem law_of_coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) (h : coreB J w fr C D R = true) (a next nx' : Fmt.M1.Stage)
    (rest' : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: nx' :: rest')
    (colR colF : ℕ → List UInt64)
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
    (fun c => behind_of_coreB J w fr C D R h a next nx' rest' hst colR htr (stretchOf c).e) hasks

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fold_rest
#print axioms ProofFile.Honest.K12.fitS_any
#print axioms ProofFile.Honest.K12.termAsks_rest
#print axioms ProofFile.Honest.K12.restAsks_rest
#print axioms ProofFile.Honest.K12.wanted_trees
#print axioms ProofFile.Honest.K12.behind_of_coreB
#print axioms ProofFile.Honest.K12.law_of_coreB
