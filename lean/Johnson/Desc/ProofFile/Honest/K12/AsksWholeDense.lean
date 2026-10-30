-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AsksWholeDense.lean: the "dense" twin of `dataAsks_of_one`
(AsksWhole.lean in this folder).

What it is. The old statements and structures hold, take or give `FrontAsks` (ShapeAll.lean) or
`ShapeAsks` (PlanB.lean), each with a field `plainRows`, which asks that no open row and no sample
row of the whole statement on entry has a written-out variable (`stPlainB`,
Johnson/Desc/Ground/Shape/Marks.lean). The twins have `FrontAsksD` (ShapeAllDense.lean) and
`ShapeAsksD` (PlanBDense.lean) in their places, whose field `denseRows` asks `DenseRow` of the rows
taken in at the group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a
row has a written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables
where every tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter. The files named here lie in
Johnson/Desc/ProofFile/Honest/K12/.

Why. Without these twins `ShapeAsksD` could be had from the old `ShapeAsks` alone, and so from the
old mark. These are the statements that make a `ShapeAsks` from tests on the front, and the second
member's condition at a play and at a run.

Main names. `dataAsks_of_oneD`.

By what. Each twin's proof is the old proof with the twins' names in it. Where the old proof drew
`PlainRow` from `plainRows` by `runRows_plain`, the twin hands on `denseRows`.

Limits.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`, as all the twins do
  (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean says why).
- They do not reach the first chain's proximity test yet. The library proves the hypothesis on the
  rows there, of the verifier's state (`taken_dense_entered`,
  Johnson/AtFull/Shape/TakenRowsDense.lean). These files do not show the other hypotheses there: the
  tests on the front (`frontFiveB`), `stTidyB` and `claimsB` on entry, `planB`, and the hypotheses
  on the prover's data. `onFreeTD_at_run` (OnFreeTAtRunDense.lean) speaks of the shared chain, on
  which that test does not lie.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Without a twin: `sorts_of_coreB` (SortsMember.lean), which makes a `ShapeAsks` from the test
  `coreB`, whose list has the clause `stPlainB`; `frontAsks_of_shape` (OneToAll.lean, not in the
  library), which no statement on the way to `OnFreeTD` calls; the forms without trees
  (`OnPlan`, `OnFree`, `AtEntry` and what is stated of them); the statements that conclude
  `ShapeAsks`, `FrontAsks` or `OnFreeT` at the shared chain's first test or at a small example:
  there the new conclusions follow from the old by `shapeAsksD_of`, `frontAsksD_of`, `onFreeTD_of`.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.K12.Honest.Shape.SwitchInShapeDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open ProofFile.Honest.Sh (door_facts_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB SingleSh door_facts batT_codes rounds_split gpLS_eq)
variable {W X : Type}

/-- The twin of `dataAsks_of_one` (AsksWhole.lean), from `FrontAsksD`. -/
theorem dataAsks_of_oneD (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : FrontAsksD J w fr K Dp)
    (f1 : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (Dt : DataFront J w fr C Dp c R) : DataAsks J w fr C D Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun row' L' h G' hG' => ?_⟩
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
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, -, p4, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    have s2 := S.door
    simp only [hA, hN] at s2
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts_dense s2 hm S.tidy S.denseRows S.claims p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
    rw [eR] at h ⊢
    have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
    injection h' with h1 h2
    subst h1 h2
    exact Dt.allSay G hG'
  · simp at hP

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.dataAsks_of_oneD
