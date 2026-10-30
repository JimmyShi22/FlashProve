-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineTestLeftOwn.lean: at a proximity test whose first fold sends its own fresh table: the clause asks of the condition at
the entry of the second part (∃ Dp cc R, … `ShapeAsksO` ∧ `DataAsks`: Johnson/Desc/ProofFile/Honest/K12/Own/EndOkOwn.lean,
PlanB.lean), at challenges that end with the first fold, FROM TESTS ON THE SHAPE OF THE STATE ON ENTRY, THE FORM OF THE
CHALLENGES HEARD, AND ONE SENTENCE ON HIDDEN DATA. General in the job (a `ManyJob`), the input, the front and the coins.

  `shapeAsksO_of_heard`   `ShapeAsksO` at a list that ends with the first fold, from `FrontAsksO`, the plan's tests and the
                          list's form. `shapeAsks_of_front_own` (…/K12/Own/ShapeAsksOwn.lean) asks the whole `FormAsks`, which no such
                          list meets: so the list is lengthened by any tail that the later rounds can draw, and
                          the clauses, which read the first fold's challenges alone, are carried back
  `trees_of_front_own`    the number of the plain data's trees is a function of the thin shape of the state in front: the
                          statement and proof of `ts_of_front_own` (…/K12/AtFile/OAtHead.lean), laid here so that this file
                          stands over none of that file's ground at the proof file
  `RowsSayInFront`        THE ONE SENTENCE ON HIDDEN DATA: the rows that the group under test has taken in say true things
                          of the members' words, at the state with the group's test begun
  `OwnTestShape`          the tests on the shape and the plan, as one structure: all Bools on public terms, and the
                          three tests that read the state's rows
  `left_of_shape_own`     the theorem

Limits. Conditional. The state on entry is the job's own letter, compared with nothing here. `RowsSayInFront` is a
premise: no value is shown to meet it. It reads the input and the coins: no later law may take it as a
hypothesis on a run and then speak of the coins as drawn anew. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.FrontOwnFive
import Johnson.Desc.ProofFile.Honest.K12.Own.DataThreeOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.DataAsksOwn
import Johnson.Desc.ProofFile.Honest.K12.ShapeOfTwo
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanCausal
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (ManyJob plainMany colsMany manyFitsS tsLenOf plain_ts)
open OnBytes (Codes)
open OnBytes.Means (AllSay layoutOf)
open OnBytes.Slice (rdE begun runRows)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open H2K.JointK (laidOf)
open H2K.First (Plain)
open H2K.Pub (sgOf)
open Johnson.Prover.Link (batCut kk_eq)
open ProofFile.Honest.Sh (testSh thinOf claimsB)

variable {W X : Type}

/-- **`ShapeAsksO` at a list of challenges that ends with the first fold.** tail: any list that the later
rounds can draw. -/
theorem shapeAsksO_of_heard (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (hs tail : List Fmt.Drawn) (K : Codes) (Dp : Plain) (a next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (P : FormPub J.p a next rest) (hP : planOB J.p K Dp.ts.length = true)
    (S : FrontAsksO J w fr K Dp) (hen : 2 + a.k ≤ (laidOf J.p).length)
    (hd : drawsFit (((laidOf J.p).take (2 + a.k)).map (·.1)) hs = true)
    (ht : drawsFit (((laidOf J.p).drop (2 + a.k)).map (·.1)) tail = true) :
    ShapeAsksO J w fr C (byNo hs) K Dp := by
  have hfull : drawsFit ((laidOf J.p).map (·.1)) (hs ++ tail) = true := by
    have e : (laidOf J.p).map (·.1) =
        ((laidOf J.p).take (2 + a.k)).map (·.1) ++ ((laidOf J.p).drop (2 + a.k)).map (·.1) := by
      rw [← List.map_append, List.take_append_drop]
    rw [e]
    exact K12.drawsFit_append _ _ _ _ hd ht
  have F := formAsks_of_draws J w fr C (hs ++ tail) a next rest hst P hfull
  have S' := shapeAsks_of_front_own J w fr C (byNo (hs ++ tail)) K Dp hP S F
  have hA : stA J.p = a := by
    unfold stA
    rw [hst]
    rfl
  have hl : hs.length = 2 + a.k := by
    have e := K12.drawsFit_length _ _ hd
    rw [List.length_map, List.length_take, Nat.min_eq_left hen] at e
    exact e
  have h : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) →
      byNo (hs ++ tail) n = byNo hs n := by
    intro n hn
    rw [hA, kk_eq P.hk] at hn
    unfold byNo
    rw [List.getD_append _ _ _ _ (by omega)]
  have e0 : byNo (hs ++ tail) 0 = byNo hs 0 := h 0 (by omega)
  have eT := tFold_congr J w fr C (byNo (hs ++ tail)) (byNo hs) h
  exact ⟨S'.codes, S'.door, S'.noMask, S'.tidy, S'.plainRows, S'.claims, by rw [← e0]; exact S'.plain,
    by rw [← eT]; exact S'.codes₁, by rw [← eT]; exact S'.pub⟩

/-- **The number of the plain data's trees is a function of the thin shape of the state in front.** -/
theorem trees_of_front_own (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : J.p.early = true) (h : frontOwnFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (S : FrontAsksO J w fr K Dp) :
    Dp.ts.length = tsLenOf J.p (thinOf (testSh (J.rec₀ w fr))) := by
  have hp := pass_of_five _ _ _ h
  have hc : claimsB (J.rec₀ w fr) = true := S.claims
  unfold frontOwnFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, -⟩ := h
  rw [ProofFile.Honest.Sh.thinOf_eq] at h5 ⊢
  unfold claimsB at hc
  cases hG : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G => exact plain_ts J.p _ hp he h5 G hG Dp (S.plain G hG).1

/-- **THE ONE SENTENCE ON HIDDEN DATA**: `DataFront`'s last clause (…/K12/ShapeAll.lean) at the job's own plain rows. -/
def RowsSayInFront (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) : Prop :=
  ∀ G, (A.toRun.toTest.rec₀ w fr).st.groups[(A.toRun.toTest.rec₀ w fr).g]? = some G →
    AllSay rdE (begun (A.toRun.toTest.rec₀ w fr).st (A.toRun.toTest.rec₀ w fr).g G)
      (runRows (A.toRun.toTest.rec₀ w fr).st G).toList
      (wordsAt (begun (A.toRun.toTest.rec₀ w fr).st (A.toRun.toTest.rec₀ w fr).g G)
        (layoutOf (A.toRun.toTest.rec₀ w fr).st G) (plainMany A w fr C))

/-- **The tests on the shape of the state on entry and on the plan.** n: the number of trees. -/
structure OwnTestShape (A : ManyJob W X) (w : W) (fr : Front X) (K : Codes) (n : ℕ)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Prop where
  stages : A.p.nums.stages = a :: next :: rest
  early : A.p.early = true
  form : FormPub A.p a next rest
  plan : planOB A.p K n = true
  bat : batCut (((laidOf A.p).take 1).map (·.1)) = true
  enough : 2 + a.k ≤ (laidOf A.p).length
  five : frontOwnFiveB A.p K (testSh (A.rec₀ w fr)) = true
  trees : tsLenOf A.p (thinOf (testSh (A.rec₀ w fr))) = n
  many : manyFitsS A.p (A.mems.map (·.shape)) A.trees (thinOf (testSh (A.rec₀ w fr))) = true
  tidy : stTidyB (A.rec₀ w fr).st = true
  plainRows : stPlainB (A.rec₀ w fr).st = true
  claims : claimsB (A.rec₀ w fr) = true

/-- **The clause asks, from the tests on the shape, the form of the challenges heard and the one sentence on
hidden data.** -/
theorem left_of_shape_own (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) (K : Codes) (n : ℕ)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (T : OwnTestShape A w fr K n a next rest)
    (hs tail : List Fmt.Drawn)
    (hd : drawsFit (((laidOf A.p).take (2 + a.k)).map (·.1)) hs = true)
    (ht : drawsFit (((laidOf A.p).drop (2 + a.k)).map (·.1)) tail = true)
    (say : RowsSayInFront A w fr C) :
    ∃ Dp cc R, Dp.ts.length = n ∧ ShapeAsksO A.toRun.toTest w fr C (byNo hs) K Dp ∧
      DataAsks A.toRun.toTest w fr C (byNo hs) Dp cc R := by
  obtain ⟨Dp, S⟩ := frontAsksO_of_five A.toRun.toTest w fr K T.early T.five T.tidy T.plainRows T.claims
  have hn : Dp.ts.length = n :=
    (trees_of_front_own A.toRun.toTest w fr K Dp T.early T.five S).trans T.trees
  obtain ⟨d1, d2, d3⟩ := dataThree_of_front_own A w fr K Dp T.early (pass_of_five _ _ _ T.five) S T.many C
  have f1 := (two_of_draws A.toRun.toTest w fr C hs a next rest T.stages T.form hd).1
  exact ⟨Dp, colsMany A Dp.ts w fr C, plainMany A w fr C, hn,
    shapeAsksO_of_heard A.toRun.toTest w fr C hs tail K Dp a next rest T.stages T.form
      (by rw [hn]; exact T.plan) S T.enough hd ht,
    dataAsks_of_one_own A.toRun.toTest w fr C (byNo hs) Dp _ _ S.door S.noMask S.tidy S.plainRows T.bat f1
      ⟨d1, d2, d3, say⟩⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shapeAsksO_of_heard
#print axioms AtPublicFiles.OfflineRows.trees_of_front_own
#print axioms AtPublicFiles.OfflineRows.left_of_shape_own
