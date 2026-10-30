-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SortsMember.lean: the four hypotheses of `accepts_of_plan`
(PlanB.lean in this folder) hold together at two small made-up places. The four are the plan's half,
which is the test `planB` (a function to Bool), and the three structures `ShapeAsks`, `FormAsks`
and `DataAsks`, all in PlanB.lean. Here they are derived from the "true" of the test `coreB`
(AllB.lean in this folder) and from two equations more: the state on entry to the test and the state
after the first fold have one table of codes, K. That step, `sorts_of_coreB`, is general in the job,
the prover's input, what precedes the test, the coins, the sampled challenges, the plain rows and K.
Three theorems with their proofs; no definition.

In the list: J is a job (`TestJob`, Test.lean in this folder): what a caller supplies for its
proximity test. `J.p` is its place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at
which a proximity test is. w is the prover's input, fr what precedes the test (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean), C the coins that `testAll` reads (`TestCoins`, Test.lean),
D the sampled challenges by the round's number, R the prover's rows as plain functions of numbers
(`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean), K a table of codes (`Codes`,
OnBytes/Iop/Ground.lean). The state on entry is `J.rec₀ w fr`; the state after the first fold is
`tFold J w fr C D` (PlanB.lean). Dp is the library's plain data on the group under test (`Plain`,
Johnson/Desc/K12/Law/FirstOk.lean), among them the list `Dp.ts` of trees.

  `sorts_of_coreB`: under the three hypotheses below there is a Dp with: `planB J.p K Dp.ts.length`
    is true; `ShapeAsks J w fr C D K Dp`; `FormAsks J w fr C D`; and `DataAsks J w fr C D Dp c R`,
    where c gives the columns of the job's own trees: `colsFrom`
    (Johnson/Desc/K12/Honest/FirstAsks.lean) at what `J.trees₀` returns and at `Dp.ts`
  `sorts_one`, `sorts_came`: so the four hold together, at some Dp, at the values of
    `ToyGroup.one Toy.list₁` (ToyGroup.lean and Toy.lean in this folder; the place of ToyAll.lean)
    and of `ToyCame.came 0` (ToyCame.lean). In `sorts_one` K is the table of codes of that job's
    own state on entry; in `sorts_came` K is the written table `ToyCame.codes`. In both, R is the
    field `lay` of these values at the first stage's state (`At.lay`, `At.P`, ToyAt.lean)

By what. `sorts_of_coreB` unfolds `coreB` and `coreL` (AllB.lean) into their clauses, and three of
these into theirs: `Sh.firstB` (Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean), `termB` and
`restB` (AllB.lean). Dp is what `gpOf` (FirstOk.lean) returns at the claim that the state after the
batching passes. The clauses are then put one by one into `planL` (PlanB.lean) and into the fields
of the three structures. The two equations are the fields `codes` and `codes₁` of `ShapeAsks`. The
first also turns the codes into K in the clause "switchPubB" of `planL`, the second in the clauses
"a mask code's length", "switchPlanB" and "planFromOk". `termAsks_of` and `restAsks_of` (AllB.lean)
give the field `pub` of `ShapeAsks`, the field `range` of `FormAsks` and all four of `DataAsks`;
`fitFrom_of_B` (Johnson/Desc/K12/Honest/FitFromB.lean) gives the field `later` of `FormAsks`;
`front_getD` (PlanB.lean) rewrites the state in `allSay`. `sorts_one` is `sorts_of_coreB` at
`coreB_one` (ToyAll.lean), and `sorts_came` at `ToyCame.coreB_came` (ToyCame.lean). These two are
proved by the kernel's own evaluation (`decide +kernel`), and so are the equations at the two
places, but for the first in `sorts_one`, which is `rfl`.

Hypotheses of `sorts_of_coreB`. h: `coreB J w fr C D R` is true. h1: the table of codes in the state
on entry is K. h2: the table of codes in the state after the first fold is K.

Limits.
- The second equation could be derived; here it is a hypothesis of `sorts_of_coreB`, and at the two
  places it is evaluated.
- The four are shown together at two small made-up places only, each at one list of challenges.
- What holds vacuously at each of the two places: see the limits of ToyAll.lean and ToyCame.lean.
- Nothing is shown at a place of a file: both places have made-up numbers, and no description of a
  file (`FileDescription`, Johnson/Desc/Block.lean) is named here.
- Only the direction from `coreB` to the four hypotheses is proved.
- The fields `plain` and `pub` of `ShapeAsks` and `allSay` of `DataAsks` are implications from what
  a state passes; `allSay` has a second hypothesis inside it, that the state on entry has the group
  under test. The three theorems do not conclude that a claim is passed after the batching, or
  single rows after the first fold, or that the group is there. So, read by their statements only,
  `sorts_one` and `sorts_came` could hold with these three fields vacuous. Whoever cites them as
  values that meet the four hypotheses has to cite with them `coreB_one` and `ToyCame.coreB_came`,
  from which they are proved.
- No theorem here states the length of `Dp.ts`. The clause `asks` of `OnFree` (Sim/ExactFree.lean in
  this folder) asks `Dp.ts.length = 1`. At the values of `ToyCame.came 0` the plain data lists four
  trees (`At.places`, ToyAt.lean; by a `#guard` of ToyCame.lean): `sorts_came` gives no value that
  meets that clause.
- The state on entry is whatever the job's function `rec₀` returns. It is compared with nothing
  here: it is not shown to be the verifier's.
- `accepts_of_plan` is not called here: no acceptance is concluded.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.ProofFile.Honest.K12.ToyCame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPubB)

variable {W X : Type}

/-- **Where `coreB` is true and the codes on entry and after the first fold are K, the four
hypotheses of `accepts_of_plan` hold**, at some plain data Dp and at the columns of the job's own
trees. -/
theorem sorts_of_coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (R : PlainRows) (K : Codes) (h : coreB J w fr C D R = true)
    (h1 : (J.rec₀ w fr).st.codes = K) (h2 : (tFold J w fr C D).st.codes = K) :
    ∃ Dp : Plain, planB J.p K Dp.ts.length = true ∧ ShapeAsks J w fr C D K Dp ∧
      FormAsks J w fr C D ∧
      DataAsks J w fr C D Dp (colsFrom (J.trees₀ w fr C.mem (J.first w fr C)) Dp.ts) R := by
  unfold coreB coreL at h
  split at h
  · rename_i a next nx' rest' row L hst hp
    split at h
    · rename_i Dp hD
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
      simp only [tFold, hA] at h2
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, cS, c14, c15, c16⟩ := h
      unfold Sh.firstB at c4
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at c4
      obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := c4
      have f4' : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true := by
        have e : (testSh (J.rec₀ w fr)).mask.isSome = true := c3
        rw [if_pos e] at f4
        exact f4
      have f2' : switchPubB J.p K 0 a next (nx' :: rest').isEmpty
          ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          (lettersOf J.p a next).n (lettersOf J.p a next).dS (lettersOf J.p a next).dC = true := by
        rw [← h1]
        exact f2
      have T := termAsks_of _ _ _ _ _ _ _ _ _ _ _ row L hp hD c9
      have V := restAsks_of J w fr C D a next _ Dp R row L _ _ hD c12
      have c9' := c9
      unfold termB at c9'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at c9'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩ := c9'
      have c12' := c12
      unfold restB at c12'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at c12'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩,
        b14⟩, b15⟩, b16⟩ := c12'
      have claimIs : ∀ row' L', (J.recB w fr (D 0)).pass = .claim row' L' → row' = row ∧ L' = L :=
        fun row' L' h' => by
          rw [hp] at h'
          injection h' with e1 e2
          exact ⟨e1.symm, e2.symm⟩
      refine ⟨Dp, ?_, ?_, ?_, ?_⟩
      · unfold planB planL
        rw [hst]
        simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          decide_eq_true_eq]
        refine ⟨c1, c2, f2', f3, f4', a2, a3, a6, a10, a11, a12, a13, c10, c11, b1, b2, b7, b13, ?_,
          ?_, ?_, c15⟩
        · rw [← h2]
          exact b14
        · rw [← h2]
          exact cS
        · rw [← h2]
          exact c14
      · refine ⟨h1, ?_, c3, c5, c6, c7, ?_, ?_, ?_⟩
        · rw [hA, hN]
          exact f1
        · intro row' L' h'
          obtain ⟨rfl, rfl⟩ := claimIs row' L' h'
          rw [hA]
          exact ⟨hD, a1, b8, b9, b10, b11⟩
        · simp only [tFold, hA]
          exact h2
        · intro rows gp h'
          simp only [tFold, hA, hN] at h' ⊢
          exact ⟨T.pub rows gp h', V.old rows gp h'⟩
      · refine ⟨c8, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hA]
          exact a7
        · rw [hA, hN, hR]
          exact a8
        · rw [hA]
          exact fitFrom_of_B D _ _ c16
        · rw [hA]
          exact T.range
        · rw [hA]
          exact b6
        · simp only [tFold, hA, hN]
          exact b16
      · refine ⟨?_, ?_, V.trees, ?_⟩
        · rw [hA]
          exact V.cols
        · rw [hA]
          exact V.state
        · intro row' L' h' G hG
          obtain ⟨rfl, rfl⟩ := claimIs row' L' h'
          have k := V.allSay G
          rw [front_getD] at k
          exact k hG
    · simp at h
  · simp at h

set_option maxRecDepth 100000 in
/-- **The four hypotheses hold together at the place of ToyAll.lean**, at one list of challenges. K
is the table of codes of the job's own state on entry. -/
theorem sorts_one : ∃ Dp : Plain,
    planB (ToyGroup.one Toy.list₁).J.p
      ((ToyGroup.one Toy.list₁).J.rec₀ (ToyGroup.one Toy.list₁).w
        (ToyGroup.one Toy.list₁).fr).st.codes Dp.ts.length = true ∧
    ShapeAsks (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
      (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D
      ((ToyGroup.one Toy.list₁).J.rec₀ (ToyGroup.one Toy.list₁).w
        (ToyGroup.one Toy.list₁).fr).st.codes Dp ∧
    FormAsks (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
      (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D ∧
    DataAsks (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
      (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D Dp
      (colsFrom ((ToyGroup.one Toy.list₁).J.trees₀ (ToyGroup.one Toy.list₁).w
        (ToyGroup.one Toy.list₁).fr (ToyGroup.one Toy.list₁).C.mem
        ((ToyGroup.one Toy.list₁).J.first (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
          (ToyGroup.one Toy.list₁).C)) Dp.ts)
      ((ToyGroup.one Toy.list₁).lay (ToyGroup.one Toy.list₁).P) :=
  sorts_of_coreB _ _ _ _ _ _ _ coreB_one rfl (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The four hypotheses hold together at the place of ToyCame.lean**, at one list of challenges. K
is `ToyCame.codes`. -/
theorem sorts_came : ∃ Dp : Plain,
    planB (ToyCame.came 0).J.p ToyCame.codes Dp.ts.length = true ∧
    ShapeAsks (ToyCame.came 0).J (ToyCame.came 0).w (ToyCame.came 0).fr (ToyCame.came 0).C
      (ToyCame.came 0).D ToyCame.codes Dp ∧
    FormAsks (ToyCame.came 0).J (ToyCame.came 0).w (ToyCame.came 0).fr (ToyCame.came 0).C
      (ToyCame.came 0).D ∧
    DataAsks (ToyCame.came 0).J (ToyCame.came 0).w (ToyCame.came 0).fr (ToyCame.came 0).C
      (ToyCame.came 0).D Dp
      (colsFrom ((ToyCame.came 0).J.trees₀ (ToyCame.came 0).w (ToyCame.came 0).fr
        (ToyCame.came 0).C.mem ((ToyCame.came 0).J.first (ToyCame.came 0).w (ToyCame.came 0).fr
          (ToyCame.came 0).C)) Dp.ts)
      ((ToyCame.came 0).lay (ToyCame.came 0).P) :=
  sorts_of_coreB _ _ _ _ _ _ _ ToyCame.coreB_came (by decide +kernel) (by decide +kernel)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.sorts_of_coreB
#print axioms ProofFile.Honest.K12.sorts_one
#print axioms ProofFile.Honest.K12.sorts_came
