-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/AcceptsOwn.lean

THE DECISION OF A PROXIMITY TEST ACCEPTS ALL THAT THE TERM SHOWS, WHERE THE FIRST FOLD SENDS ITS OWN
FRESH TABLE. The fellows of `test_accepts_all` (WholeAll.lean in the folder above) and
`accepts_of_plan` (PlanB.lean), which stand where that table has come earlier alone.

  `test_accepts_all_own`   under the hypotheses of `bodyInv_behind_first_own`
                 (BodyInvFirstOwn.lean in this folder): the block's `decide` returns
  `accepts_of_plan_own`   the same from `planOB`, `ShapeAsksO`, `FormAsks`, `DataAsks` and the flag

By what. The proofs are those of `bodyInv_behind_first_own` and `wanted_of_plan_own`
(EndOkOwn.lean in this folder), which reach `test_accepts_shape_own` and drop what it accepts: here
that is what is kept. The invariant is `BodyInv` at `renumP`; `stageYes_back` and `base_renum` bring
each stage back to the place itself. The conclusions name no `renumP`.

HOW EACH PREMISE OF `accepts_of_plan_own` WOULD BE PAID AT jobKO (E2E/KeyHalves.lean).
- ho: `piKOFull`'s field `ownMask` is true; `place_O` ties the chain's place to it (a trial).
- hP: `planOB_KO_full`, at Dp.ts.length = 3: that length is OPEN at the run: by reading gpOf gives
  the trees 1, 2, 7.
- S: door: `shape_doorOmegaF`, whose four premises hb, hS, hw, hpU are OPEN at the key, and
  `door_O`. codes: OPEN: `door_O` pins four entries of the table alone; owed that the shape's codes
  are the written value's (`codes_held`). noMask: by text, at every input and front, with no
  `enters`: the seat's way in and `fallOmega` both lay none. tidy, plainRows, claims:
  `three_doorOmegaF`, `three_O`, its other premises OPEN at the key. plain, codes₁, pub:
  OPEN: a twin of `shapeAsks_of_front`.
- F: `formAsks_of_draws`, `facts_KO`: `pKO` of that file against `piKOFull` OPEN.
- Dt: cols, state, trees: OPEN: a twin of `dataThree_of_front`. allSay: OPEN: four pieces.

- THE VALUE: `door_O` and `three_O` stand at the trial's `QK`; `fitsK_O`, `membersKO` stand at `AK`, at
  `atKey`, and the thread's own value is a third. They differ as terms in set, scope, beforePoint.
  Whether `endOmega` reads these: OPEN.
No premise is known to be unmeetable at jobKO. Met here: ho; hP at 3 and not yet at Dp.ts.length.

Limits.
- "Accepts" is `Block.decide` returning: `planOk` and the two tests of `Block.step` are not concluded.
  `decide` is handed the rounds without digests and the groups, not the field `tr`, where the fold's
  own tree lies: that the third group is that tree's is `cols_term_own`'s matter.
- MEMBERS AT TWO TOYS ALONE (Member.lean in this folder): so the five premises are consistent as a
  form. At jobKO no value is known at which they hold together.
- NOTHING ON t': `Post` is `fun _ => True`. What the chain's end asks of the state left is not paid
  here.
- Where rec₀ is not the verifier's state, nothing is said on a run. At a list of which `drawsFit` is
  false, nothing. At a half behind the guard, nothing here: SaysYesOwn.lean.
- The yes is news on the text, not on the mathematics: `bodyInv_behind_first_own` already obtained
  this from the same call.
- Conditionals. `ShapeAsksO`, `FormAsks`, `DataAsks` are hypotheses: that they can be had together
  is not shown, and of `DataAsks` the clause `allSay` is a sentence on values.
- The state on entry is the job's own `rec₀`: it is not shown to be the verifier's. Where it is a
  fall-back the conclusion says nothing on a run.
- Through BodyInvFirstOwn.lean: the library's structures in their later form, with the clause
  `dense`. Every row taken in is asked to be a `PlainRow`. There is no "dense" twin.
- `renumP` stands in hypotheses of `test_accepts_all_own`, and in clause 21 of `planOB`, so of
  `accepts_of_plan_own` too: what BodyInvFirstOwn.lean's limits say of it stands. Nothing drawn at
  `renumP` is quoted here of stage 0 or of any count.
- `planOB` asks three stages or more.
- Nothing on completeness, on soundness or on what is
  hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.EndOkOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape_own switchIn_shape_own SwitchPub claimsB testSh
  readPubB singleSh switchPub_of runRows_plain switchPubB)

variable {W X : Type}

/-- **The decision of the test's block accepts the rounds and the opened columns of `testAll`, where
the first fold sends its own fresh table.** Under the hypotheses of `bodyInv_behind_first_own`. -/
theorem test_accepts_all_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ)))
    (hst : J.p.nums.stages = a :: next :: rest) (ho : J.p.nums.ownMask = true)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = none) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, PlainRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty
      ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCutOwn a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1
      (J.recB w fr (D 0)) (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Sp : FirstSwitchPlan (renumP J.p) (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS
      J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll (renumP J.p) rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨-, -, -, -, Y⟩ := first_of_shape_own J.p (coinsOf J.p.nums.stages C.hide C.rest)
    rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n dS dC h hm htidy hpl
    hv Pl hB hF fB (by rw [← eR]; exact A)
  obtain ⟨rows, In⟩ := switchIn_shape_own J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a
    next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
    (noDigest ⟨[.answer (ofE (aAns J.p 0 a next 1 D (t1At J.p
      (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1
      (J.first w fr C) D)))], D (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩) rfl (renumP J.p) rfl
  rw [← eR] at Y In
  have hI := bodyInv_first_all (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
    (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D n _
    rows (firstYes_renum _ _ _ _ _ _ _ _ _ _ _ _ Y) Sp In hPlan hFit
  obtain ⟨t', e, -⟩ := test_accepts_shape_own J w fr C D a next rest ds os hst hrd hor Dp c i n dS
    dC h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (BodyInv (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll (renumP J.p)) D)
    (fun _ => True)
    (fun next' rest' j cur l o t P col x =>
      ⟨stageYes_back _ _ _ _ _ _ _ _ _ _ _ _
          (hstep_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P
            col x).1,
        (hstep_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P
          col x).2⟩)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t
        P col x
      rw [base_renum J.p j cur _ ho a next rest hst] at e
      exact ⟨t', e, trivial⟩)
    (fun hc => hI hc)
  exact ⟨t', e⟩

/-- **`accepts_of_plan` where the first fold sends its own fresh table**: from the test on the plan
`planOB` and the three structures, at the place's flag `ho`. -/
theorem accepts_of_plan_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (ho : J.p.nums.ownMask = true) (hP : planOB J.p K Dp.ts.length = true)
    (S : ShapeAsksO J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  unfold planOB planOL at hP
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
    have hm := S.noMask
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
    refine test_accepts_all_own J w fr C D a next (nx' :: rest') ds os hst ho hrd hor Dp cc
      (lettersOf J.p a next).i (lettersOf J.p a next).n (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 (fun G hG => runRows_plain s5 hG) s6 Pl p4 p5 f1 A p13 p14
      R V ?_ ⟨?_, p22⟩ f4
    · show SwitchPlan (renumP J.p) (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p)
        1 (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next _
      rw [s9]
      exact switchPlan_renum (switchPlan_of_B p20)
    · show PlanFrom (renumP J.p) (nx' :: rest') (0 + 1) next ((laidS J.p).drop (a.k + 3))
        (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
          (J.first w fr C) D).st.codes
      rw [s9]
      exact planFrom_of_ok (renumP J.p) _ _ _ _ _ p21
  · simp at hP

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.test_accepts_all_own
#print axioms ProofFile.Honest.K12.Own.accepts_of_plan_own
