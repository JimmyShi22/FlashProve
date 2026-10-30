-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/BodyInvMember.lean: the invariant of a proximity test's later
stages (`BodyInv`, Johnson/Prover/Link/BodyInv.lean) can be met. It holds after the first stage at
the two small made-up examples of ToyAll.lean and ToyCame.lean in this folder, at the values that
`testAll` (Test.lean in this folder) computes there. The statement is `Wanted` (BodyInvFirst.lean
in this folder): `BodyInv` before the second stage. `wanted_of_coreB` derives it from the "true" of
the test `coreB` (AllB.lean in this folder) and is general in the job, the prover's input, the
front, the coins, the challenges and the plain rows. At the two examples `coreB` is proved true. A
definition, three theorems and their proofs.

In the list: a job J (`TestJob`, Test.lean) is what a caller supplies for its test. `J.p` is its
place (`P12`, Johnson/Desc/K12/Frame.lean: the test's parameters, among them the list of stages,
`J.p.nums.stages`). w is the prover's input, fr the front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), C the coins that `testAll` reads
(`TestCoins`, Test.lean), D the sampled challenges by the round's number, R the prover's rows as
plain functions of numbers (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean). Dp has the type
of the library's plain data on the group of oracle messages under test (`Plain`,
Johnson/Desc/K12/Law/FirstOk.lean). The job's own trees are `J.trees₀ w fr C.mem (J.first w fr C)`.
Their columns are `colsFrom` (Johnson/Desc/K12/Honest/FirstAsks.lean) at that list and `Dp.ts`: for
a tree's number in `Dp.ts`, the column function of the tree at the same index in the list. The
group's trees built from columns c are `groupTrees Dp.ts (logAt Dp.book) c`
(Johnson/Desc/K12/Honest/GroupState.lean): for each number in `Dp.ts`, the depth by `Dp.book` and
the column by c. An example's values are an `At` (ToyAt.lean in this folder): a job, a front, coins,
a list of challenges, how the plain rows are read from the first stage's state, and the prover's
input.

  `wanted_of_coreB`: if `coreB J w fr C D R` is true, there are stages a, next, nx', a list rest'
    and a Dp such that: the place's stages are a, next, nx' and then rest', so three or more;
    `Wanted J w fr C D a next (nx' :: rest') Dp` holds at the columns of the job's own trees; and
    the job's own trees are the group's trees built from these columns
  `wanted_one`, `wanted_came`: `WantedAt` at `ToyGroup.one Toy.list₁` (ToyGroup.lean in this
    folder), the example of ToyAll.lean, and at `ToyCame.came 0`, the example of ToyCame.lean
  `WantedAt A`: a definition: the conclusion of `wanted_of_coreB` at an example's values A

By what. `wanted_of_coreB` calls `bodyInv_behind_first` (BodyInvFirst.lean). Its proof derives that
theorem's hypotheses from the clauses of `coreB` as the proof of `accepts_of_coreB` (AllB.lean)
derives those of `test_accepts_all` (WholeAll.lean in this folder), line for line up to the last
call: by `termAsks_of`, `restAsks_of` and `switchPlan_of_B` (AllB.lean), `switchPub_of`
(Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean), `runRows_plain`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean), `planFrom_of_ok`
(Johnson/Prover/Link/StepPlanOk.lean) and `fitFrom_of_B` (Johnson/Desc/K12/Honest/FitFromB.lean).
The equation on the trees is the field `trees` of `RestAsks` (WholeShape.lean in this folder).
`wanted_one` and `wanted_came` are `wanted_of_coreB` at `coreB_one` (ToyAll.lean) and
`ToyCame.coreB_came` (ToyCame.lean), which are proved by the kernel's own evaluation
(`decide +kernel`).

Limits.
- `wanted_one` and `wanted_came` are at two small made-up places, each at one list of challenges.
- Which cases each of the two lacks, so that what is asked for them holds vacuously there: see the
  limits of the two files.
- The stages and the plain data are under "there are" (∃). The equation on the place's list fixes
  the stages. In the proof Dp is what `gpOf` (FirstOk.lean) returns at the job's state after the
  batching, `J.recB w fr (D 0)`; the statements do not say so.
- `coreB` is sufficient, not necessary: see the limits of AllB.lean. It is false at a place with
  fewer than three stages, and where the field `mask` of the state on entry is `none` (its clause
  "the fresh table has come earlier"): nothing is shown there.
- "The values that `testAll` computes there" is read off the definitions: see the limits of
  BodyInvFirst.lean. No theorem here states it. `testAll` goes through the stages at the job's own
  trees and `Wanted` has the group's trees: the third clause says that the two lists are equal.
- The values in `Wanted` are computed from the job's state on entry, `J.rec₀ w fr`, and from its
  rows, `J.rows₀`, both the caller's functions: no statement that this state is the verifier's.
- No acceptance is concluded here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.BodyInvFirst
import Johnson.Desc.ProofFile.Honest.K12.ToyCame

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

/-- **Where `coreB` is true, `Wanted` holds.** There are stages and a Dp such that the place has
three stages or more, `Wanted` holds at the columns of the job's own trees, and these trees are the
group's trees built from these columns. -/
theorem wanted_of_coreB (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (R : PlainRows) (h : coreB J w fr C D R = true) :
    ∃ a next nx' rest' Dp, J.p.nums.stages = a :: next :: nx' :: rest' ∧
      Wanted J w fr C D a next (nx' :: rest') Dp
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
      exact bodyInv_behind_first J w fr C D a next (nx' :: rest') ds os hst hrd hor Dp _
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

/-- The conclusion of `wanted_of_coreB` at an example's values. -/
def WantedAt (A : At) : Prop :=
  ∃ a next nx' rest' Dp, A.J.p.nums.stages = a :: next :: nx' :: rest' ∧
    Wanted A.J A.w A.fr A.C A.D a next (nx' :: rest') Dp
      (colsFrom (A.J.trees₀ A.w A.fr A.C.mem (A.J.first A.w A.fr A.C)) Dp.ts) ∧
    A.J.trees₀ A.w A.fr A.C.mem (A.J.first A.w A.fr A.C) = groupTrees Dp.ts (logAt Dp.book)
      (colsFrom (A.J.trees₀ A.w A.fr A.C.mem (A.J.first A.w A.fr A.C)) Dp.ts)

/-- `WantedAt` at the example of ToyAll.lean, by `coreB_one`. -/
theorem wanted_one : WantedAt (ToyGroup.one Toy.list₁) := wanted_of_coreB _ _ _ _ _ _ coreB_one

/-- `WantedAt` at the example of ToyCame.lean, by `ToyCame.coreB_came`. -/
theorem wanted_came : WantedAt (ToyCame.came 0) := wanted_of_coreB _ _ _ _ _ _ ToyCame.coreB_came

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.wanted_of_coreB
#print axioms ProofFile.Honest.K12.wanted_one
#print axioms ProofFile.Honest.K12.wanted_came
#print axioms ProofFile.Honest.K12.WantedAt
