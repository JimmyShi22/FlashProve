-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontAtHead.lean

What it proves. Under the head P5J.AtMg, at the proof file's shared chain. (1) The code numbers of
the seated parameters of the test on G_u are the written ones (idx_head_U). (2) The functions on
shapes that the door of a proximity test is told by (testCore; frontFiveB and what it calls) read of
the test's parameters no more than the numbers, the code numbers, the two fields early and answers,
and the declared rounds: two sets of parameters that agree in these give the same values. (3) At the
written parameters and the typed sizes these functions are evaluated by the kernel. So: at every job
of a proximity test with the seated parameters whose state on entry is doorUF's, at every input and
whatever precedes the test there are plain data at which FrontAsks (ShapeAll.lean) holds, at the
table of codes codesFull2; and at doorOmegaF's state the
three tests that read the rows hold, the shape is one term, and layFits is true at jobAtOmega with
that state function. bs: the plan's eight blocks (the premise hb; there are such: blocks_head,
NearAtHead.lean); pO: the seated parameters of the test on G_omega (hO; places_at_head,
FitAtHead.lean).

Names.
  idx_real, idx_head_U   (1).
  Alike   two sets of parameters agree in what is read.
  stageAt_alike … testCore_alike   (2) for testCore and what it calls.
  opensOf_alike … frontFiveB_alike   (2) for frontFiveB and what it calls.
  alike_head_U   under the head the seated parameters and the written ones are alike.
  front_real, front_at, lengths_real   (3).
  endOf_plan, endOmega_plan, fallOmega_plan, endOmega_alike, fallOmega_alike   the terms at the head
      are those at the typed sizes.
  five_head, three_fallOmega_head, near_fallOmega_head, lengths_head   (3) under the head.
  frontAsks_head   FrontAsks at the test on G_u.
  three_head_OmegaF, shape_head_OmegaF, near_head_OmegaF, layFits_head_OmegaF   at the test on
      G_omega.

By what. places_idx, idx_of_planOk (Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean); Written.shape
(Johnson/Goal/Numbers/WrittenAtZ.lean); early_of_planOk, answers_of_planOk
(Johnson/Desc/K12/Law/Top.lean). In this folder: nums_head_U, thin_head_U, decls_thin
(Sim/FirstPubAtHead.lean); planOk_head_U, facts_at_head, layFitsNear_head_Omega, pubBehind_plan
(NearAtHead.lean); written_at_head, qAt_written (FitAtHead.lean); frontAsks_all (FrontAtShape.lean);
three_head_UF, shape_head_UF, planOk_head_eight (MarksAtHead.lean); three_doorOmegaF,
shape_doorOmegaF, near_doorOmegaF (DoorsByShape.lean); layFits_near (PubNear.lean).

Limits.
- FrontAsks is on the verifier's state alone: nothing on the prover's data, nothing on the test's
  own challenges. The case in which the first fold's mask has come, alone: so at the test on G_u,
  not at the test on G_omega.
- The theorems are also true of the fall-backs: they do not tell a fold that failed from one that
  returned, and they are no statement that the state on entry is the verifier's. At the test on
  G_omega the state is the fall-back at every honest run, as long as a part is handed no opened
  column (JobShared.lean's limits).
- endOmega (DoorsByShape.lean) is what testCore returns at the plan's term, or a default where it
  returns nothing. Whether it returns at the real plan's term is not evaluated here; it does
  (core_head, CoreAtHead.lean), so that file's limit (where testCore returns nothing,
  shape_doorOmegaF speaks of the fall-back alone) does not apply under the head.
- idx_real, front_real and lengths_real are of the form (realSized.all …) = true, which would be
  true for nothing if realSized were none; it is not (real_members,
  Johnson/Desc/K1/Law/CondReal.lean).
  The full size alone; no example of the head is shown here.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.MarksAtHead
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead
import Johnson.Desc.K12.Law.Sizes.IdxAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleNotice TableKey)
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts stageAt codesFit)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB CoreSh)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks first withU)
open Desc.K14.Shape (doorO)
open H2K.Member (piUFull)
open H2K.JointK (laidOf laidS)
open H2K.Pub (walkL pubL pubOk)
open Johnson.Prover.Link (stageOr)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestJob FrontAsks frontFiveB frontPlainB₀ frontAsks_all stA stN lettersOf)
open ProofFile.Honest.K12.Thin (frontPubB)
open ProofFile.Honest.Sh (claimsB testSh TestSh ThinSh testCore testThin stagesThin batThin foldThin
  maskThin baseThin switchThin switchBody gpOfS gpLS gpAllS gpOkS labelsLS labelsOkS commonB
  batOwesB frontOwesB doorB)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 The code numbers -/

theorem idx_real : (realSized.all fun q =>
    decide (H2K.Sizes.nosOf q.1.shape.testU = piUFull.idx)) = true := by
  decide +kernel

/-- **Under the head the code numbers of the seated parameters of the test on G_u are the written
ones.** -/
theorem idx_head_U (h : P5J.AtMg o Z D r Zp Np cF) : (fourOf Np).U.idx = piUFull.idx := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have e1 : (fourOf Np).U.idx = Np.U.idx := H2K.Sizes.idx_of_planOk _ _ (planOk_head_U h)
  have e2 := (H2K.Sizes.places_idx Zp.made Np h.laid.places).2.1
  have e3 : Zp.made.p.chains.made.sized.proof.batch.shape = x.shape := Wr.shape
  have k := idx_real
  rw [hx] at k
  simp only [Option.all_some, decide_eq_true_eq] at k
  rw [e1, e2, e3]
  exact k

/-! ## 2 What the functions on shapes read of the parameters -/

/-- Two sets of parameters agree in the numbers, the code numbers, early, answers and the declared
rounds. -/
structure Alike (p q : P12) : Prop where
  nums : p.nums = q.nums
  idx : p.idx = q.idx
  early : p.early = q.early
  answers : p.answers = q.answers
  decls : (laidOf p).map (·.1) = (laidOf q).map (·.1)

section
variable {p q : P12} (A : Alike p q)
include A

theorem stageAt_alike (j : ℕ) (s : Fmt.M1.Stage) : stageAt p j s = stageAt q j s := by
  unfold stageAt
  rw [A.idx]

theorem batThin_alike (a : ThinSh) : batThin p a = batThin q a := by
  unfold batThin
  rw [A.idx, A.early]

theorem maskThin_alike (F : OnBytes.FoldShape) (a : ThinSh) : maskThin p F a = maskThin q F a := by
  unfold maskThin
  rw [A.nums]

theorem foldThin_alike (j : ℕ) (cur : Fmt.M1.Stage) (a : ThinSh) :
    foldThin p j cur a = foldThin q j cur a := by
  unfold foldThin
  simp only [stageAt_alike A, A.idx, maskThin_alike A]

theorem baseThin_alike (j : ℕ) (cur : Fmt.M1.Stage) (a : ThinSh) :
    baseThin p j cur a = baseThin q j cur a := by
  unfold baseThin
  simp only [stageAt_alike A]

theorem switchBody_alike (last : Bool) (nx : OnBytes.Params.IoppStage) (asked : List ℕ) (gp : ℕ)
    (a : ThinSh) (id : ℕ) :
    switchBody p last nx asked gp a id = switchBody q last nx asked gp a id := by
  unfold switchBody
  simp only [A.nums]

theorem switchThin_alike (j : ℕ) (nxt : Fmt.M1.Stage) (last : Bool) (a : ThinSh) :
    switchThin p j nxt last a = switchThin q j nxt last a := by
  unfold switchThin
  simp only [stageAt_alike A, switchBody_alike A]

theorem stagesThin_alike : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (a : ThinSh),
    stagesThin p rest j cur a = stagesThin q rest j cur a
  | [], j, cur, a => baseThin_alike A j cur a
  | nxt :: rest, j, cur, a => by
    simp only [stagesThin, foldThin_alike A, switchThin_alike A, stagesThin_alike rest]

theorem testThin_alike (a : ThinSh) : testThin p a = testThin q a := by
  unfold testThin
  simp only [A.nums, batThin_alike A, stagesThin_alike A]

/-- **testCore reads no more.** -/
theorem testCore_alike (c : CoreSh) (g : ℕ) (mask : Option ℕ) :
    testCore p c g mask = testCore q c g mask := by
  unfold testCore
  rw [testThin_alike A]

theorem opensOf_alike (k : ℕ) : H2K.First.opensOf p k = H2K.First.opensOf q k := by
  have e : ∀ u : P12, H2K.First.opensOf u k =
      (((((laidOf u).map (·.1)).drop 1).drop (1 + k)).take 2).flatMap (·.opens) := by
    intro u
    rw [← List.map_drop, ← List.map_drop, ← List.map_take, List.flatMap_map]
    rfl
  rw [e p, e q, A.decls]

theorem gpOfS_alike (a : ThinSh) (s : Fmt.M1.Stage) (L : OnBytes.GroupLayout) :
    gpOfS p a s L = gpOfS q a s L := by
  unfold gpOfS
  simp only [stageAt_alike A, maskThin_alike A, opensOf_alike A]

theorem gpLS_alike (a : Fmt.M1.Stage) (kept : ℕ) (Dd : ProofFile.Honest.Sh.PlainS) :
    gpLS p a kept Dd = gpLS q a kept Dd := by
  unfold gpLS
  simp only [A.nums]

theorem gpOkS_alike (a : TestSh) : gpOkS p a = gpOkS q a := by
  unfold gpOkS gpAllS
  simp only [A.nums, gpOfS_alike A, gpLS_alike A]

theorem labelsOkS_alike (a : TestSh) : labelsOkS p a = labelsOkS q a := by
  unfold labelsOkS labelsLS
  simp only [A.nums, gpOfS_alike A]

theorem commonB_alike (cur nxt : Fmt.M1.Stage) (c : CoreSh) (g : ℕ) (i n : ℕ × ℕ) :
    commonB p cur nxt c g i n = commonB q cur nxt c g i n := by
  unfold commonB
  simp only [A.idx]

theorem codesFit_alike (S : OnBytes.Statement) : codesFit p S = codesFit q S := by
  unfold codesFit
  rw [A.nums, A.idx]

theorem batOwesB_alike (cut : List Fmt.DeclaredRound) (a : TestSh) :
    batOwesB p cut a = batOwesB q cut a := by
  unfold batOwesB
  simp only [A.early, codesFit_alike A, gpOkS_alike A, labelsOkS_alike A]

theorem walkL_alike (K : Codes) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (a : Fmt.M1.Stage)
    (l : List H2K.Pub.WR), walkL p K j a rest l = walkL q K j a rest l
  | [], j, a, l => by
    simp only [walkL, A.idx, A.nums]
  | b :: rest, j, a, l => by
    simp only [walkL, A.idx, A.nums, walkL_alike K rest]

theorem pubOk_alike (K : Codes) : pubOk p K = pubOk q K := by
  unfold pubOk pubL
  simp only [A.nums, walkL_alike A]

theorem frontOwesB_alike (a : TestSh) : frontOwesB p a = frontOwesB q a := by
  unfold frontOwesB
  rw [A.nums, pubOk_alike A]

theorem doorB_alike (cur nxt : Fmt.M1.Stage) (cutB : List Fmt.DeclaredRound) (i n : ℕ × ℕ)
    (a : TestSh) : doorB p cur nxt cutB i n a = doorB q cur nxt cutB i n a := by
  unfold doorB
  rw [commonB_alike A, batOwesB_alike A, frontOwesB_alike A]

theorem stA_alike : stA p = stA q := by
  unfold stA
  rw [A.nums]

theorem stN_alike : stN p = stN q := by
  unfold stN
  rw [A.nums]

theorem lettersOf_alike (a next : Fmt.M1.Stage) : lettersOf p a next = lettersOf q a next := by
  have e : ∀ (u : P12) (n : ℕ), (((laidS u).drop n).take 2).map (·.1) =
      ((((laidOf u).map (·.1)).drop 1).drop n).take 2 := by
    intro u n
    unfold laidS
    rw [List.map_take, List.map_drop, List.map_drop]
  unfold lettersOf stageOr
  simp only [e, A.decls, A.idx, stageAt_alike A]

theorem frontPlainB₀_alike (a : ThinSh) : frontPlainB₀ p a = frontPlainB₀ q a := by
  unfold frontPlainB₀
  simp only [batThin_alike A, gpOfS_alike A, gpLS_alike A, stA_alike A]

theorem frontPubB_alike (a : ThinSh) : frontPubB p a = frontPubB q a := by
  unfold frontPubB
  simp only [batThin_alike A, lettersOf_alike A, stA_alike A, stN_alike A]

/-- **frontFiveB reads no more.** -/
theorem frontFiveB_alike (K : Codes) (N : TestSh) : frontFiveB p K N = frontFiveB q K N := by
  have e : ((laidOf p).take 1).map (·.1) = ((laidOf q).take 1).map (·.1) := by
    rw [List.map_take, List.map_take, A.decls]
  unfold frontFiveB
  simp only [e, doorB_alike A, lettersOf_alike A, stA_alike A, stN_alike A, frontPlainB₀_alike A,
    frontPubB_alike A]

end

/-! ## 3 Under the head -/

/-- **Under the head the seated parameters of the test on G_u and the written ones are alike.** -/
theorem alike_head_U (h : P5J.AtMg o Z D r Zp Np cF) : Alike (fourOf Np).U piUFull where
  nums := nums_head_U h
  idx := idx_head_U h
  early := (H2K.JointK.early_of_planOk _ (planOk_head_U h)).trans (by decide)
  answers := (H2K.JointK.answers_of_planOk _ (planOk_head_U h)).trans (by decide)
  decls := by rw [decls_thin, decls_thin, thin_head_U h]

/-- endOf does not read the list of messages that must be fixed before the point. -/
theorem endOf_plan (set : OnBytes.Params.Setting) (sc : OnBytes.Params.Scope) (codes : Codes)
    (S : LinShape) (item : ℕ) (l l' : List (ℕ × ℕ)) (s : Array OracleNotice) :
    endOf ⟨set, sc, codes, S, item, l⟩ s = endOf ⟨set, sc, codes, S, item, l'⟩ s := rfl

/-- endOmega at parameters that are alike. -/
theorem endOmega_alike {p q : P12} (A : Alike p q) (Q : P14) (s : Array OracleNotice) :
    endOmega Q s p = endOmega Q s q := by
  unfold endOmega
  rw [testCore_alike A]

theorem fallOmega_alike {p q : P12} (A : Alike p q) (Q : P14) (s : Array OracleNotice) :
    fallOmega Q s p = fallOmega Q s q := by
  unfold fallOmega
  rw [endOmega_alike A]

/-- endOmega does not read that list either. -/
theorem endOmega_plan (set : OnBytes.Params.Setting) (sc : OnBytes.Params.Scope) (codes : Codes)
    (S : LinShape) (item : ℕ) (l l' : List (ℕ × ℕ)) (s : Array OracleNotice) (p : P12) :
    endOmega ⟨set, sc, codes, S, item, l⟩ s p = endOmega ⟨set, sc, codes, S, item, l'⟩ s p := by
  unfold endOmega
  rw [endOf_plan set sc codes S item l l' s]

theorem fallOmega_plan (set : OnBytes.Params.Setting) (sc : OnBytes.Params.Scope) (codes : Codes)
    (S : LinShape) (item : ℕ) (l l' : List (ℕ × ℕ)) (s : Array OracleNotice) (p : P12) :
    fallOmega ⟨set, sc, codes, S, item, l⟩ s p = fallOmega ⟨set, sc, codes, S, item, l'⟩ s p := by
  unfold fallOmega
  rw [endOmega_plan set sc codes S item l l' s p]

/-- At the typed sizes and the written parameters: the five clauses on the shape at the test on G_u;
the three tests at fallOmega, and the part that layFits reads of it. -/
theorem front_real : (realSized.all fun q =>
    frontFiveB piUFull q.2
        (Desc.K14.Shape.doorU (endOf (planOf q.2 q.1.shape).P (sentOf q.1.shape))) &&
      stTidyB (fallOmega (planOf q.2 q.1.shape).P (sentOf q.1.shape) piUFull).st &&
      stPlainB (fallOmega (planOf q.2 q.1.shape).P (sentOf q.1.shape) piUFull).st &&
      claimsB (fallOmega (planOf q.2 q.1.shape).P (sentOf q.1.shape) piUFull) &&
      decide (pubNear (fallOmega (planOf q.2 q.1.shape).P (sentOf q.1.shape) piUFull) =
        nearOf (pubBehind (planOf q.2 q.1.shape).P (sentOf q.1.shape)) 1)) = true := by
  decide +kernel

/-- What front_real says at the size that realSized returns. -/
theorem front_at {x : OnBytes.Params.LinSized} (hx : realSized = some (x, codesFull2)) :
    frontFiveB piUFull codesFull2
        (Desc.K14.Shape.doorU (endOf (planOf codesFull2 x.shape).P (sentOf x.shape))) = true ∧
      Three (fallOmega (planOf codesFull2 x.shape).P (sentOf x.shape) piUFull) ∧
      pubNear (fallOmega (planOf codesFull2 x.shape).P (sentOf x.shape) piUFull) =
        nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 1 := by
  have k := front_real
  rw [hx] at k
  simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at k
  exact ⟨k.1.1.1.1, ⟨k.1.1.1.2, k.1.1.2, k.1.2⟩, k.2⟩

/-- Under the head the five clauses on the shape hold at the plan's term. -/
theorem five_head (h : P5J.AtMg o Z D r Zp Np cF) :
    frontFiveB (fourOf Np).U codesFull2
      (Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S))) = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [frontFiveB_alike (alike_head_U h), qAt_written Wr Np,
    endOf_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
  exact (front_at hx).1

/-- **FrontAsks at every input and whatever precedes the test on G_u, under the head**: there are
plain data, which may hang on both. True of the fall-back too: no statement that the state on entry
is the verifier's. -/
theorem frontAsks_head (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (J : TestJob W X) (hp : J.p = (fourOf Np).U)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hJ : J.rec₀ = doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) (w : W)
    (fr : Front X) : ∃ Dp, FrontAsks J w fr codesFull2 Dp :=
  frontAsks_all J codesFull2 (Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)))
    (by rw [hp]; exact H2K.JointK.early_of_planOk _ (planOk_head_U h))
    (fun w fr => by rw [hJ]; exact shape_head_UF h bs hb key cols w fr)
    (by rw [hp]; exact five_head h)
    (fun w fr => by
      rw [hJ]
      exact ⟨(three_head_UF h bs hb key cols w fr).tidy,
        (three_head_UF h bs hb key cols w fr).plain,
        (three_head_UF h bs hb key cols w fr).claims⟩) w fr

/-- Under the head the three tests hold at the fall-back of the test on G_omega. -/
theorem three_fallOmega_head (h : P5J.AtMg o Z D r Zp Np cF) :
    Three (fallOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U) := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [fallOmega_alike (alike_head_U h), qAt_written Wr Np,
    fallOmega_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
  exact (front_at hx).2.1

theorem near_fallOmega_head (h : P5J.AtMg o Z D r Zp Np cF) :
    pubNear (fallOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U) =
      nearOf (pubBehind (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) 1 := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [fallOmega_alike (alike_head_U h), qAt_written Wr Np,
    fallOmega_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) [], pubBehind_plan]
  exact (front_at hx).2.2

theorem lengths_real : (realSized.all fun q => q.2.lengthsOk) = true := by decide +kernel

theorem lengths_head (h : P5J.AtMg o Z D r Zp Np cF) : (K1.qAt Zp Np).codes.lengthsOk = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := lengths_real
  rw [hx] at k
  rw [qAt_written Wr Np]
  exact k

/-- **The three tests at doorOmegaF's state, under the head.** True of the fall-back too: no
statement that the state on entry is the verifier's. -/
theorem three_head_OmegaF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (w : W) (fr : Front X) :
    Three (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols w fr) := by
  obtain ⟨hS, hM, hw⟩ := facts_at_head h
  exact three_doorOmegaF (K1.qAt Zp Np) bs hb (planOk_head_eight h bs hb) hS hM _ hw
    (lengths_head h) _ (planOk_head_U h) (three_fallOmega_head h) key cols w fr

/-- **The shape of doorOmegaF's state is one term, under the head.** True of the fall-back too: no
statement that the state on entry is the verifier's. -/
theorem shape_head_OmegaF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (w : W) (fr : Front X) :
    testSh (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols w fr) =
      doorO (endOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U) := by
  obtain ⟨hS, -, hw⟩ := facts_at_head h
  exact shape_doorOmegaF (K1.qAt Zp Np) bs hb hS _ hw _ (planOk_head_U h) key cols w fr

/-- **The part that layFits reads of doorOmegaF's state is the plan's, under the head.** True of the
fall-back too: no statement that the state on entry is the verifier's. -/
theorem near_head_OmegaF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (w : W) (fr : Front X) :
    pubNear (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols w fr) =
      nearOf (pubBehind (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) 1 := by
  obtain ⟨hS, hM, hw⟩ := facts_at_head h
  exact near_doorOmegaF (K1.qAt Zp Np) bs hb hS hM _ hw _ (planOk_head_U h) (near_fallOmega_head h)
    key cols w fr

/-- **layFits at jobAtOmega with doorOmegaF, under the head.** No statement that the state on entry
is the verifier's: at every honest run it is the fall-back, as long as a part is handed no opened
column. -/
theorem layFits_head_OmegaF (h : P5J.AtMg o Z D r Zp Np cF) (pO : P12)
    (hO : (fourOf Np).O = some pO) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) :
    (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols) weights rand
      omega?).layFits
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols w fr) =
        true := by
  rw [layFits_near, near_head_OmegaF h bs hb key cols w fr]
  exact layFitsNear_head_Omega h pO hO _ weights rand omega?

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.idx_real
#print axioms ProofFile.Honest.K12.Light.idx_head_U
#print axioms ProofFile.Honest.K12.Light.Alike
#print axioms ProofFile.Honest.K12.Light.stageAt_alike
#print axioms ProofFile.Honest.K12.Light.batThin_alike
#print axioms ProofFile.Honest.K12.Light.maskThin_alike
#print axioms ProofFile.Honest.K12.Light.foldThin_alike
#print axioms ProofFile.Honest.K12.Light.baseThin_alike
#print axioms ProofFile.Honest.K12.Light.switchBody_alike
#print axioms ProofFile.Honest.K12.Light.switchThin_alike
#print axioms ProofFile.Honest.K12.Light.stagesThin_alike
#print axioms ProofFile.Honest.K12.Light.testThin_alike
#print axioms ProofFile.Honest.K12.Light.testCore_alike
#print axioms ProofFile.Honest.K12.Light.opensOf_alike
#print axioms ProofFile.Honest.K12.Light.gpOfS_alike
#print axioms ProofFile.Honest.K12.Light.gpLS_alike
#print axioms ProofFile.Honest.K12.Light.gpOkS_alike
#print axioms ProofFile.Honest.K12.Light.labelsOkS_alike
#print axioms ProofFile.Honest.K12.Light.commonB_alike
#print axioms ProofFile.Honest.K12.Light.codesFit_alike
#print axioms ProofFile.Honest.K12.Light.batOwesB_alike
#print axioms ProofFile.Honest.K12.Light.walkL_alike
#print axioms ProofFile.Honest.K12.Light.pubOk_alike
#print axioms ProofFile.Honest.K12.Light.frontOwesB_alike
#print axioms ProofFile.Honest.K12.Light.doorB_alike
#print axioms ProofFile.Honest.K12.Light.stA_alike
#print axioms ProofFile.Honest.K12.Light.stN_alike
#print axioms ProofFile.Honest.K12.Light.lettersOf_alike
#print axioms ProofFile.Honest.K12.Light.frontPlainB₀_alike
#print axioms ProofFile.Honest.K12.Light.frontPubB_alike
#print axioms ProofFile.Honest.K12.Light.frontFiveB_alike
#print axioms ProofFile.Honest.K12.Light.alike_head_U
#print axioms ProofFile.Honest.K12.Light.endOf_plan
#print axioms ProofFile.Honest.K12.Light.endOmega_alike
#print axioms ProofFile.Honest.K12.Light.fallOmega_alike
#print axioms ProofFile.Honest.K12.Light.endOmega_plan
#print axioms ProofFile.Honest.K12.Light.fallOmega_plan
#print axioms ProofFile.Honest.K12.Light.front_real
#print axioms ProofFile.Honest.K12.Light.front_at
#print axioms ProofFile.Honest.K12.Light.five_head
#print axioms ProofFile.Honest.K12.Light.frontAsks_head
#print axioms ProofFile.Honest.K12.Light.three_fallOmega_head
#print axioms ProofFile.Honest.K12.Light.near_fallOmega_head
#print axioms ProofFile.Honest.K12.Light.lengths_real
#print axioms ProofFile.Honest.K12.Light.lengths_head
#print axioms ProofFile.Honest.K12.Light.three_head_OmegaF
#print axioms ProofFile.Honest.K12.Light.shape_head_OmegaF
#print axioms ProofFile.Honest.K12.Light.near_head_OmegaF
#print axioms ProofFile.Honest.K12.Light.layFits_head_OmegaF
