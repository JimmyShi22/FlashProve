-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingAccepts.lean: the decision of a proximity test's
block accepts all that `testAll` shows, at a state on entry whose rows taken in are dense
(`DenseRow`, OnBytes/Slice/BlkProxDense.lean), not plain. General in the job, the prover's input,
the front, the coins, the challenges, the table of codes, the plain data, the columns and the plain
rows: nothing here names a place, a number of members or a message.

  `test_accepts_all_dense`   `test_accepts_all` (K12/WholeAll.lean) with `DenseRow` in the place of
                             `PlainRow`
  `accepts_of_planD`         `accepts_of_plan` (K12/PlanB.lean) with `ShapeAsksD` in the place of
                             `ShapeAsks`
  `accepts_every_listD`      `accepts_every_list` (K12/ShapeAll.lean) with `FrontAsksD` in the place
                             of `FrontAsks`: at every list of challenges that the declared rounds
                             can sample

Why. At a test that takes in a row with a written-out factor, `ShapeAsks.plainRows` is false, so
`accepts_of_plan` says nothing there. The first test's own laws ask less: `first_of_shape_dense`,
`switchIn_shape_dense`, `test_accepts_shape_dense`.

By what. `test_accepts_all_dense`: the proof of `test_accepts_all` with these three in the places of
their plain forms; `BodyInv`, `bodyInv_first_all`, `hstep_at`, `hbase_at` as they stand.
`accepts_of_planD`: the proof of `accepts_of_plan`, the field `denseRows` handed on.
`accepts_every_listD`: `formAsks_of_draws`, `shapeAsksD_of_front`, `dataAsks_of_frontD`.

Limits.
- The hypotheses are hypotheses: none of `ShapeAsksD`, `FormAsks`, `DataAsks`, `FrontAsksD`,
  `DataFront` is shown here of any value.
- The state on entry is the job's own `rec₀`; it is compared with nothing here. `DataAsks.allSay`
  reads targets: at a job whose state on entry has lost its targets no honest words meet it.
- `planB` is false at a place with fewer than three stages. The case in which the first fold sends
  its own table is not served. A statement on entry with no group number `g` meets no `door`.
- "Accepts" is `Block.decide ... = .ok`: `planOk` and the two tests of `Block.step` are not
  concluded.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.BodyInvFirstDense
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.ProofFile.Honest.K12.WholeAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow)
open ProofFile.Honest.Sh (switchIn_shape_dense first_of_shape_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks SwitchPub claimsB testSh switchPub_of)

variable {W X : Type}

/-- **The decision of the test's block accepts the rounds and the opened columns of `testAll`, where
the rows taken in are dense.** -/
theorem test_accepts_all_dense (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ)))
    (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = some id) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty
      ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1
      (J.recB w fr (D 0)) (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Sp : FirstSwitchPlan J.p (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll J.p rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨-, -, -, -, Y⟩ := first_of_shape_dense J.p (coinsOf J.p.nums.stages C.hide C.rest)
    rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl
    hv Pl hB hF fB (by rw [← eR]; exact A)
  obtain ⟨rows, In, hst1⟩ := switchIn_shape_dense J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a
    next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
    (noDigest ⟨[.answer (ofE (aAns J.p 0 a next 1 D (t1At J.p
      (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1
      (J.first w fr C) D)))], D (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩) rfl
  rw [← eR] at Y In hst1
  have hI := bodyInv_first_all J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
    (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D n _
    rows Y Sp In hPlan hFit
  obtain ⟨t', e, -⟩ := test_accepts_shape_dense J w fr C D a next rest ds os hst hrd hor Dp c i n
    id dS dC h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D) (fun _ => True)
    (hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t P col x
      exact ⟨t', e, trivial⟩)
    hI
  exact ⟨t', e⟩

/-- **The plan's half as its test `planB`, the other three groups as hypotheses, where the rows taken
in are dense: the block's decision accepts all that `testAll` shows.** -/
theorem accepts_of_planD (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsksD J w fr C D K Dp)
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
    refine test_accepts_all_dense J w fr C D a next (nx' :: rest') ds os hst hrd hor Dp c
      (lettersOf J.p a next).i (lettersOf J.p a next).n id (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 s5 s6 Pl p4 p5 f1
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

/-- **At every list of challenges that the declared rounds can sample**, from premises that name no
challenge of the test. -/
theorem accepts_every_listD (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (K : Codes)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (Pb : FormPub J.p a next rest)
    (S : FrontAsksD J w fr K Dp) (Dt : DataFront J w fr C Dp c R) (ds : List Fmt.Drawn)
    (hd : drawsFit ((laidOf J.p).map (·.1)) ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C (byNo ds)).rs.map noDigest) (testAll J w fr C (byNo ds)).gs = .ok t' := by
  have F := formAsks_of_draws J w fr C ds a next rest hst Pb hd
  exact accepts_of_planD J w fr C (byNo ds) K Dp c R hP
    (shapeAsksD_of_front J w fr C _ K Dp hP S F) F (dataAsks_of_frontD J w fr C _ K Dp c R hP S F Dt)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.test_accepts_all_dense
#print axioms ProofFile.Honest.K12.accepts_of_planD
#print axioms ProofFile.Honest.K12.accepts_every_listD
