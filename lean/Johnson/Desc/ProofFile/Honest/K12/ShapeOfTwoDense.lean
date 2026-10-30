-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ShapeOfTwoDense.lean: the "dense" twins of `shapeAsks_of_two`,
`shapeAsks_of_form`, `shapeAsks_of_draws` (ShapeOfTwo.lean in this folder).

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

Main names. `shapeAsksD_of_two`, `shapeAsksD_of_form`, `shapeAsksD_of_draws`.

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
import Johnson.Desc.ProofFile.Honest.K12.ShapeOfTwo
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.ProofFile.Honest.K12.PlanBDense
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

/-- The twin of `shapeAsks_of_two` (ShapeOfTwo.lean): `FrontAsksD` gives `ShapeAsksD`. -/
theorem shapeAsksD_of_two (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planB J.p K Dp.ts.length = true)
    (S : FrontAsksD J w fr K Dp)
    (f1 : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (f2 : roundsFit (((laidS J.p).take (1 + (stA J.p).k)).map (·.1))
      (rfAt (coinsOf J.p.nums.stages C.hide C.rest) 0 (stA J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D) = true) : ShapeAsksD J w fr C D K Dp := by
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
    obtain ⟨-, -, p3, p4, p5, p6, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9⟩ := S
    have s2' := s2
    simp only [hA, hN] at s2' s7 s9 f2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts_dense s2' hm s4 s5 s6 p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    rw [eR] at f2
    have FF := foldFront_first H x row hr
    have hfold := fold5_yes FF p5 _ f2
    have e1 := getD_of_ok (d := batT (J.rec₀ w fr) G row) hfold
    obtain ⟨rE, rR, hrs, hR'⟩ := rounds_split (length_of_foldCut p5) f2
    have hk0 : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k
    have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq p6
    obtain ⟨q1, q2, q3, q4⟩ := s7 G H.group
    have eT : tFold J w fr C D = foldT (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ ((lettersOf J.p a next).n.code, (lettersOf J.p a next).n.maskCode) id
        (rE :: rR) := by
      show t1At J.p _ 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0)) _ D = _
      rw [hA, eR, ← hrs]
      exact e1
    refine ⟨s1, s2, s3, s4, s5, s6, ?_, ?_, ?_⟩
    ·
      intro row' L' h
      rw [eR] at h ⊢
      have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA]
      refine ⟨q1, ?_, H.layK.trans kk.symm, H.layH, q3, q4⟩
      rw [← gpLS_eq, hk0]
      rw [← gpLS_eq] at q2
      exact q2
    · rw [eT]
      exact (foldT_keeps _ _ _ _ _ _ _).1.trans ((batT_codes _ G row).trans s1)
    ·
      intro rows gp h
      rw [eT] at h ⊢
      have h' : Passing.single (foldOut (batT (J.rec₀ w fr) G row) row
          (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2,
            a.k, a.h⟩ id (rE :: rR)) (batT (J.rec₀ w fr) G row).st.groups.size =
          .single rows gp := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA, hN]
      obtain ⟨y1, y2, y3, y4⟩ := foldOut_says (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ id rE rR
      constructor
      · refine (readPubB_congr _ _ _ _ y1 (y4 fun k => H.noKept k) ?_ y3 y2).trans
          (s9 G id H.group hm)
        show (rR.map drawnOf).length = a.k
        rw [List.length_map]
        exact hR'
      · have hcodes : (batT (J.rec₀ w fr) G row).st.codes = (J.rec₀ w fr).st.codes :=
          batT_codes _ G row
        have Pl' : SwitchPub J.p (batT (J.rec₀ w fr) G row).st.codes 0 a next
            (nx' :: rest').isEmpty ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
              a.h⟩ (lettersOf J.p a next).n (lettersOf J.p a next).dS
            (lettersOf J.p a next).dC := by
          rw [hcodes]
          exact Pl
        have hrow : foldRowOk (spent (batT (J.rec₀ w fr) G row).st id)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G)) row = true :=
          (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans FF.rowFits)
        have hlen : (rR.map drawnOf).length = a.k := by
          rw [List.length_map]
          exact hR'
        rw [(foldT_keeps _ _ _ _ _ _ _).1]
        obtain ⟨g1, g2, g3, g4, g5, -⟩ := foldedFit_pure (batT (J.rec₀ w fr) G row).st.codes
          (sgOf a) (sgOf next) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          Pl'.codes (lettersOf J.p a next).n.code (lettersOf J.p a next).n.maskCode Pl'.zk
          Pl'.codeN Pl'.zkN Pl'.small (batT (J.rec₀ w fr) G row).st
          (spent (batT (J.rec₀ w fr) G row).st id) row (layoutOf (J.rec₀ w fr).st G) id
          (drawnOf rE) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
          (rR.map drawnOf) rfl rfl hk0 (fun k _ => H.noKept k) (hlen.trans Pl.codes.k)
          ((Own.foldShapeFits_agrees _ _).trans FF.shape) hrow
        exact ⟨g1, g2, g3, g4, g5⟩
  · simp at hP

/-- The twin of `shapeAsks_of_form` (ShapeOfTwo.lean). -/
theorem shapeAsksD_of_form (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planB J.p K Dp.ts.length = true)
    (S : FrontAsksD J w fr K Dp) (F : FormAsks J w fr C D) : ShapeAsksD J w fr C D K Dp :=
  shapeAsksD_of_two J w fr C D K Dp hP S F.bat F.fold

/-- The twin of `shapeAsks_of_draws` (ShapeOfTwo.lean). -/
theorem shapeAsksD_of_draws (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) (K : Codes) (Dp : Plain) (a next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (P : FormPub J.p a next rest) (hP : planB J.p K Dp.ts.length = true)
    (S : FrontAsksD J w fr K Dp)
    (hd : drawsFit (((laidOf J.p).take (2 + a.k)).map (·.1)) ds = true) :
    ShapeAsksD J w fr C (byNo ds) K Dp :=
  shapeAsksD_of_two J w fr C (byNo ds) K Dp hP S (two_of_draws J w fr C ds a next rest hst P hd).1
    (two_of_draws J w fr C ds a next rest hst P hd).2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shapeAsksD_of_two
#print axioms ProofFile.Honest.K12.shapeAsksD_of_form
#print axioms ProofFile.Honest.K12.shapeAsksD_of_draws
