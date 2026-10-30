-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlanLawDense.lean: the "dense" twin of `wanted_of_plan`
(PlanLaw.lean in this folder).

What it is. The old statements and structures hold or take `ShapeAsks` (PlanB.lean in the folder
above), whose field `plainRows` asks that no open row and no sample row of the whole statement on
entry has a written-out variable (`stPlainB`, Johnson/Desc/Ground/Shape/Marks.lean). The twins hold
or take `ShapeAsksD` (PlanBDense.lean there), which asks `DenseRow` of the rows taken in at the
group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a row has a
written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables where every
tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `wanted_of_plan_dense`.

By what. Each proof is the old proof with the twins' names in it. One line differs beyond that: the
new field is handed on where the old proof called `runRows_plain`.

Limits.
- These statements rest on this: in Johnson/Prover/Link/FormFirst.lean the structure
  `TestFront` has the field `dense`. With a field `plain` in its place,
  `testFront_of_dense` (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
  rest, could not be proved.
- They do not reach the first chain's proximity test yet. The library proves the new hypothesis
  there, of the verifier's state (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean).
  These files do not show that the other hypotheses hold there: the other fields of `ShapeAsksD`
  (Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean), `planB`, and the hypotheses on the prover's
  data.
- `ShapeAsksD` is made from the old `ShapeAsks` (`shapeAsksD_of`), and so from the old mark
  `stPlainB`; and from `FrontAsksD`, the hypotheses on the front with the same new field, by
  `shapeAsksD_of_front` (ShapeAllDense.lean) and `shapeAsksD_of_two`, `shapeAsksD_of_form`,
  `shapeAsksD_of_draws` (ShapeOfTwoDense.lean); `FrontAsksD` is made by `frontAsksD_of_five`
  (FrontAtShapeDense.lean). These files lie in Johnson/Desc/ProofFile/Honest/K12/. Without a twin:
  `sorts_of_coreB` (SortsMember.lean) and `frontAsks_of_shape` (OneToAll.lean, not in the library
  yet).
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanLaw
import Johnson.Desc.ProofFile.Honest.K12.PlanBDense
import Johnson.Desc.ProofFile.Honest.K12.BodyInvFirstDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
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

/-- The twin of `wanted_of_plan` (PlanLaw.lean), from `ShapeAsksD`. Where the old proof drew
`PlainRow` of the rows taken in from `plainRows`, this one hands on `denseRows`. -/
theorem wanted_of_plan_dense (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsksD J w fr C D K Dp)
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
    refine bodyInv_behind_first_dense J w fr { C with rest := c } D a next (nx' :: rest') ds os hst
        hrd
      hor Dp cc (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 s5 s6 Pl p4 p5 f1
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

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.wanted_of_plan_dense
