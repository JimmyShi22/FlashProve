-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AsksAtHead.lean

What it proves. Under the head P5J.AtMg, at the test on G_u of the proof file's shared chain, at
every job of a proximity test with the seated parameters whose state on entry is doorUF's
(DoorsByShape.lean): at every input, whatever precedes the test, at all coins and at every list of
challenges that fits the declared rounds up to the end of the first fold, there are plain data with
two trees at which ShapeAsks (PlanB.lean) holds, at the table of codes codesFull2. The same at the
input, the front, the coins and the challenges that the condition at the second part's entry names
(OnFreeT.asks, Sim/TreesExact.lean): its first half, at codesFull2 for its K and 2 for the length of
its os, follows from its clause heardFit. That K and os are these two at a job is not shown here.
bs: the plan's eight blocks (the premise hb; there are such: blocks_head, NearAtHead.lean).

Names.
  tsLenOf, plain_ts, ts_of_front   the number of the plain data's trees is a function of the thin
      shape of the state in front.
  laidS_alike … planB_alike   the plan's test planB reads of the test's parameters no more than
      Alike (FrontAtHead.lean) holds; of the declared rounds' pairs the first halves alone.
  tsLenOf_alike   nor does tsLenOf.
  codes_two   the two written tables of codes are one.
  ts_real, ts_at, ts_head   at the typed sizes the number is 2.
  planB_head, formPubB_head   planB and the test for FormPub at the seated parameters.
  shapeAsks_head   the theorem.
  heardIn_byNo, shapeAsks_heard   at what OnFreeT names.

By what. frontAsks_head, alike_head_U, five_head and the laws on Alike (FrontAtHead.lean);
shapeAsks_of_draws (ShapeOfTwo.lean); thin_batT (FrontThin.lean); gpOfS_eq
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean); planB_U_full (Sim/TreesPlanAt.lean); formPubB_congr,
formPubB_U, nums_head_U, thin_head_U (Sim/FirstPubAtHead.lean); formPub_of_B (FormPubAt.lean);
shape_head_UF (MarksAtHead.lean); written_at_head, qAt_written (FitAtHead.lean); endOf_plan
(FrontAtHead.lean); planOk_head_U (NearAtHead.lean).

Limits.
- ShapeAsks is on the verifier's state and a term of the first fold's rounds. DataAsks, the second
  half of OnFreeT.asks, is on the prover's data: not treated here.
- The case in which the first fold's mask has come, alone: planB's clause planFromOk asks that the
  fold does not send its own mask.
- The theorems are also true of doorUF's fall-back: they are no statement that the state on entry is
  the verifier's.
- ts_real is of the form (realSized.all …) = true, which would be true for nothing if realSized
  were none; it is not (real_members, Johnson/Desc/K1/Law/CondReal.lean). The full size alone; no
  example of the head is shown here.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness of a protocol, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontAtHead
import Johnson.Desc.ProofFile.Honest.K12.ShapeOfTwo
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlanAt
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleNotice TableKey Group)
open OnBytes.Params (IoppStage)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts stageAt Laid batAt foldAt switchAt)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks)
open H2K.Member (piUFull)
open H2K.JointK (laidOf laidS)
open H2K.First (Plain gpOf)
open Johnson.Prover.Link (stageOr swTarget swNotices stepPlanL stepPlanOk lastPlanL lastPlanOk
  dealtB declAt planFromOk batT asked)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestJob TestCoins FrontAsks ShapeAsks FormPub frontFiveB frontPlainB₀ stA stN
  lettersOf planB planL switchPlanB byNo shapeAsks_of_draws formPubB formPub_of_B planB_U_full)
open ProofFile.Honest.K12.Thin (thin_batT)
open ProofFile.Honest.Sh (testSh TestSh ThinSh thinSh batThin gpOfS gpOfS_eq plainSh switchPubB claimsB)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 The number of the plain data's trees -/

/-- The number of the plain data's trees, on the thin shape of the state in front. 0 where batThin
returns nothing, where no claim is passed, and where gpOfS returns nothing. -/
def tsLenOf (p : P12) (a₀ : ThinSh) : ℕ :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS p aB (stA p) L with
      | some Dd => Dd.ts.length
      | none => 0
    | _ => 0
  | none => 0

/-- Where the library's function makes the plain data, they have that number of trees. -/
theorem plain_ts (p : P12) (t : T12) (hp : t.pass = .nothing) (he : p.early = true)
    (h : frontPlainB₀ p (thinSh t) = true) (G : Group) (hG : t.st.groups[t.g]? = some G)
    (Dp : Plain)
    (hD : gpOf p (batT t G {}) (stA p) (OnBytes.Means.layoutOf t.st G) = some Dp) :
    Dp.ts.length = tsLenOf p (thinSh t) := by
  unfold frontPlainB₀ at h
  unfold tsLenOf
  split at h
  · rename_i aB hB
    rw [hB]
    have eT := thin_batT p t G {} aB hp he hG hB
    split at h
    · rename_i L hL
      have eL : L = OnBytes.Means.layoutOf t.st G := by
        have k : (thinSh (batT t G {})).pass = .claim (OnBytes.Means.layoutOf t.st G) := rfl
        rw [eT, hL] at k
        injection k
      subst eL
      have k := gpOfS_eq p (batT t G {}) (stA p) (OnBytes.Means.layoutOf t.st G)
      rw [eT, hD] at k
      simp only [hL, k, Option.map_some]
      rfl
    · cases h
  · cases h

/-- **At FrontAsks' plain data**, where the five clauses on the shape hold. -/
theorem ts_of_front (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : J.p.early = true) (h : frontFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (S : FrontAsks J w fr K Dp) :
    Dp.ts.length = tsLenOf J.p (ProofFile.Honest.Sh.thinOf (testSh (J.rec₀ w fr))) := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, h5⟩, -⟩ := h
  rw [ProofFile.Honest.Sh.thinOf_eq] at h5 ⊢
  have hp : (J.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (J.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (J.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  have hc := S.claims
  unfold claimsB at hc
  cases hG : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G => exact plain_ts J.p _ hp he h5 G hG Dp (S.plain G hG).1

/-! ## 2 What planB reads of the parameters -/

section
variable {p q : P12} (A : Alike p q)
include A

theorem laidS_alike : (laidS p).map (·.1) = (laidS q).map (·.1) := by
  unfold laidS
  rw [List.map_drop, List.map_drop, A.decls]

theorem swTarget_alike (n : IoppStage) : swTarget p n = swTarget q n := by
  unfold swTarget
  rw [A.answers]

theorem swNotices_alike (n : IoppStage) (last : Bool) :
    swNotices p n last = swNotices q n last := by
  unfold swNotices
  rw [swTarget_alike A]

theorem switchPubB_alike (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (c n : IoppStage) (dS dC : Fmt.DeclaredRound) :
    switchPubB p K j cur next last c n dS dC = switchPubB q K j cur next last c n dS dC := by
  unfold switchPubB
  rw [A.early, A.answers, stageAt_alike A, swTarget_alike A, swNotices_alike A]

theorem switchPlanB_alike (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) :
    switchPlanB p K j cur next n = switchPlanB q K j cur next n := by
  unfold switchPlanB
  rw [A.early, A.answers, stageAt_alike A, A.idx, swTarget_alike A, swNotices_alike A]

theorem stageOr_alike (j : ℕ) (s : Fmt.M1.Stage) : stageOr p j s = stageOr q j s := by
  unfold stageOr
  rw [stageAt_alike A]

end

/-- Two lists of pairs with the same first halves. -/
theorem length_of_decls {l l' : Laid} (h : l.map (·.1) = l'.map (·.1)) : l.length = l'.length := by
  have := congrArg List.length h
  rwa [List.length_map, List.length_map] at this

theorem drop_decls {l l' : Laid} (h : l.map (·.1) = l'.map (·.1)) (n : ℕ) :
    (l.drop n).map (·.1) = (l'.drop n).map (·.1) := by
  rw [List.map_drop, List.map_drop, h]

theorem take_decls {l l' : Laid} (h : l.map (·.1) = l'.map (·.1)) (n : ℕ) :
    (l.take n).map (·.1) = (l'.take n).map (·.1) := by
  rw [List.map_take, List.map_take, h]

theorem declAt_decls {l l' : Laid} (h : l.map (·.1) = l'.map (·.1)) (i : ℕ) :
    declAt l i = declAt l' i := by
  unfold declAt
  rw [h]

theorem dealtB_decls {l l' : Laid} (h : l.map (·.1) = l'.map (·.1)) (cur : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (L : List (List VerifiableInference.Desc.K12.Told)) :
    dealtB cur rest L l = dealtB cur rest L l' := by
  have e1 : ∀ u : Laid, u.map (·.1.opens) = (u.map (·.1)).map (·.opens) := fun u => by
    rw [List.map_map]
    rfl
  have e2 : ∀ u : Laid, u.all (·.1.stored.isEmpty) = (u.map (·.1)).all (·.stored.isEmpty) :=
    fun u => by
      rw [List.all_map]
      rfl
  unfold dealtB
  rw [e1 l, e1 l', e2 l, e2 l', h]

section
variable {p q : P12} (A : Alike p q)
include A

theorem stepPlanOk_alike (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) {l l' : Laid}
    (h : l.map (·.1) = l'.map (·.1)) (c n : IoppStage) (dS dC : Fmt.DeclaredRound) :
    stepPlanOk p K j cur next last l c n dS dC = stepPlanOk q K j cur next last l' c n dS dC := by
  have e : ((l.drop (1 + cur.k)).take 2).length = ((l'.drop (1 + cur.k)).take 2).length :=
    length_of_decls (take_decls (drop_decls h _) _)
  have eb : (VerifiableInference.Desc.K12.basePar p next).label =
      (VerifiableInference.Desc.K12.basePar q next).label := by
    unfold VerifiableInference.Desc.K12.basePar
    simp only [A.nums]
  unfold stepPlanOk stepPlanL
  simp only [A.early, A.answers, stageAt_alike A, A.idx, A.nums, take_decls h, e, eb,
    swTarget_alike A, swNotices_alike A]

theorem lastPlanOk_alike (K : Codes) (j : ℕ) (cur : Fmt.M1.Stage) {l l' : Laid}
    (h : l.map (·.1) = l'.map (·.1)) (c : IoppStage) (d₁ d₂ : Fmt.DeclaredRound) :
    lastPlanOk p K j cur l c d₁ d₂ = lastPlanOk q K j cur l' c d₁ d₂ := by
  unfold lastPlanOk lastPlanL
  simp only [stageAt_alike A, length_of_decls h]

theorem planFromOk_alike (K : Codes) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l l' : Laid), l.map (·.1) = l'.map (·.1) →
    planFromOk p rest j cur l K = planFromOk q rest j cur l' K
  | [], j, cur, l, l', h => by
    simp only [planFromOk, lastPlanOk_alike A K j cur h, stageOr_alike A, declAt_decls h,
      dealtB_decls h, A.nums]
  | next :: rest, j, cur, l, l', h => by
    simp only [planFromOk, stepPlanOk_alike A K j cur next rest.isEmpty h, stageOr_alike A,
      declAt_decls h, dealtB_decls h, A.nums,
      planFromOk_alike K rest (j + 1) next _ _ (drop_decls h (cur.k + 3))]

/-- **planB reads no more.** -/
theorem planB_alike (K : Codes) (nT : ℕ) : planB p K nT = planB q K nT := by
  have hS := laidS_alike A
  have r1 : ∀ (u : P12) (a : Fmt.M1.Stage),
      (foldAt guardedProximityTestParts u 0 a (laidS u) : Block T12 Unit).rounds =
        ((laidS u).take (1 + a.k)).map (·.1) := fun _ _ => rfl
  have r2 : ∀ (u : P12) (a next : Fmt.M1.Stage) (last : Bool),
      (switchAt guardedProximityTestParts u 0 a next last (laidS u) : Block T12 Unit).rounds =
        (((laidS u).drop (1 + a.k)).take 2).map (·.1) := fun _ _ _ _ => rfl
  have r3 : ∀ u : P12, (batAt guardedProximityTestParts u (laidOf u) : Block T12 Unit).rounds =
      ((laidOf u).take 1).map (·.1) := fun _ => rfl
  have s1 : ∀ n, (((laidS p).drop n).map asked) = (((laidS q).drop n).map asked) := fun n => by
    have e : ∀ u : Laid, u.map asked = (u.map (·.1)).map fun d => d.items.filter (· != .root) :=
      fun u => by
        rw [List.map_map]
        rfl
    rw [e, e, drop_decls hS]
  unfold planB planL VerifiableInference.Desc.Block.openings
  simp only [A.nums, lettersOf_alike A, switchPubB_alike A, switchPlanB_alike A, stageAt_alike A,
    r1, r2, r3, take_decls hS, take_decls A.decls, take_decls (drop_decls hS _), s1,
    planFromOk_alike A K _ _ _ _ _ (drop_decls hS _)]

theorem tsLenOf_alike (a : ThinSh) : tsLenOf p a = tsLenOf q a := by
  unfold tsLenOf
  simp only [batThin_alike A, gpOfS_alike A, stA_alike A]

end

/-! ## 3 At the typed sizes, and under the head -/

/-- **The two written tables of codes are one.** -/
theorem codes_two : H2K.Member.codesFull = codesFull2 := by decide +kernel

theorem ts_real : (realSized.all fun q =>
    decide (tsLenOf piUFull (ProofFile.Honest.Sh.thinOf
      (Desc.K14.Shape.doorU (endOf (planOf q.2 q.1.shape).P (sentOf q.1.shape)))) = 2)) = true := by
  decide +kernel

theorem ts_at {x : OnBytes.Params.LinSized} (hx : realSized = some (x, codesFull2)) :
    tsLenOf piUFull (ProofFile.Honest.Sh.thinOf
      (Desc.K14.Shape.doorU (endOf (planOf codesFull2 x.shape).P (sentOf x.shape)))) = 2 := by
  have k := ts_real
  rw [hx] at k
  simpa only [Option.all_some, decide_eq_true_eq] using k

/-- Under the head the number of trees at the plan's term is 2. -/
theorem ts_head (h : P5J.AtMg o Z D r Zp Np cF) :
    tsLenOf (fourOf Np).U (ProofFile.Honest.Sh.thinOf
      (Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)))) = 2 := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [tsLenOf_alike (alike_head_U h), qAt_written Wr Np,
    endOf_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
  exact ts_at hx

/-- **Under the head the plan's test holds at the seated parameters, at two trees.** -/
theorem planB_head (h : P5J.AtMg o Z D r Zp Np cF) : planB (fourOf Np).U codesFull2 2 = true := by
  rw [planB_alike (alike_head_U h), ← codes_two]
  exact planB_U_full

theorem formPubB_head (h : P5J.AtMg o Z D r Zp Np cF) : formPubB (fourOf Np).U = true := by
  rw [formPubB_congr (nums_head_U h) (thin_head_U h)]
  exact formPubB_U

/-- **ShapeAsks under the head**, at every input, whatever precedes the test, at all coins and at
every list of challenges that fits the declared rounds up to the end of the first fold. True of the
fall-back too: no statement that the state on entry is the verifier's. -/
theorem shapeAsks_head (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (J : TestJob W X) (hp : J.p = (fourOf Np).U)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hJ : J.rec₀ = doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) (w : W)
    (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn)
    (hd : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true) :
    ∃ Dp : Plain, Dp.ts.length = 2 ∧ ShapeAsks J w fr C (byNo ds) codesFull2 Dp := by
  obtain ⟨Dp, S⟩ := frontAsks_head h bs hb J hp key cols hJ w fr
  have he : J.p.early = true := by
    rw [hp]
    exact H2K.JointK.early_of_planOk _ (planOk_head_U h)
  have hN : testSh (J.rec₀ w fr) =
      Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) := by
    rw [hJ]
    exact shape_head_UF h bs hb key cols w fr
  have h5 : frontFiveB J.p codesFull2 (testSh (J.rec₀ w fr)) = true := by
    rw [hN, hp]
    exact five_head h
  have hts : Dp.ts.length = 2 := by
    rw [ts_of_front J w fr codesFull2 Dp he h5 S, hN, hp]
    exact ts_head h
  have hB : formPubB J.p = true := by
    rw [hp]
    exact formPubB_head h
  have hP : planB J.p codesFull2 Dp.ts.length = true := by
    rw [hts, hp]
    exact planB_head h
  refine ⟨Dp, hts, ?_⟩
  cases hst : J.p.nums.stages with
  | nil =>
    unfold formPubB at hB
    rw [hst] at hB
    cases hB
  | cons a l1 =>
    cases l1 with
    | nil =>
      unfold formPubB at hB
      rw [hst] at hB
      cases hB
    | cons next rest =>
      rw [hst] at hd
      exact shapeAsks_of_draws J w fr C ds codesFull2 Dp a next rest hst
        (formPub_of_B J.p a next rest hst hB) hP S hd

/-! ## 4 At what the condition at the second part's entry names -/

theorem heardIn_byNo (J : TestJob W X) (m : ProofFile.Honest.Mid W X) :
    heardIn J m = byNo (m.st.lately (firstLen J.p.nums.stages)) := rfl

/-- **The first half of OnFreeT.asks, at codesFull2 and a list of two, follows from its clause
heardFit**, under the head. True of the fall-back too: no statement that the state on entry is the
verifier's. -/
theorem shapeAsks_heard (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (J : TestJob W X) (hp : J.p = (fourOf Np).U)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hJ : J.rec₀ = doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols)
    (mem : ℕ → Stretch) (m : ProofFile.Honest.Mid W X)
    (hd : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      (m.st.lately (firstLen J.p.nums.stages)) = true) :
    ∃ Dp : Plain, Dp.ts.length = 2 ∧
      ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) codesFull2 Dp := by
  rw [heardIn_byNo]
  exact shapeAsks_head h bs hb J hp key cols hJ _ _ _ _ hd

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tsLenOf
#print axioms ProofFile.Honest.K12.Light.plain_ts
#print axioms ProofFile.Honest.K12.Light.ts_of_front
#print axioms ProofFile.Honest.K12.Light.laidS_alike
#print axioms ProofFile.Honest.K12.Light.swTarget_alike
#print axioms ProofFile.Honest.K12.Light.swNotices_alike
#print axioms ProofFile.Honest.K12.Light.switchPubB_alike
#print axioms ProofFile.Honest.K12.Light.switchPlanB_alike
#print axioms ProofFile.Honest.K12.Light.stageOr_alike
#print axioms ProofFile.Honest.K12.Light.length_of_decls
#print axioms ProofFile.Honest.K12.Light.drop_decls
#print axioms ProofFile.Honest.K12.Light.take_decls
#print axioms ProofFile.Honest.K12.Light.declAt_decls
#print axioms ProofFile.Honest.K12.Light.dealtB_decls
#print axioms ProofFile.Honest.K12.Light.stepPlanOk_alike
#print axioms ProofFile.Honest.K12.Light.lastPlanOk_alike
#print axioms ProofFile.Honest.K12.Light.planFromOk_alike
#print axioms ProofFile.Honest.K12.Light.planB_alike
#print axioms ProofFile.Honest.K12.Light.tsLenOf_alike
#print axioms ProofFile.Honest.K12.Light.codes_two
#print axioms ProofFile.Honest.K12.Light.ts_real
#print axioms ProofFile.Honest.K12.Light.ts_at
#print axioms ProofFile.Honest.K12.Light.ts_head
#print axioms ProofFile.Honest.K12.Light.planB_head
#print axioms ProofFile.Honest.K12.Light.formPubB_head
#print axioms ProofFile.Honest.K12.Light.shapeAsks_head
#print axioms ProofFile.Honest.K12.Light.heardIn_byNo
#print axioms ProofFile.Honest.K12.Light.shapeAsks_heard
