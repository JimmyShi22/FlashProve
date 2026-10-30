-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OAtHead.lean: the closed lines of OLines.lean under the library's
head (`P5J.AtMg`), at the seated place of the proof file's proximity test on G_omega, and what follows of them
at every job at that place whose state on entry is `doorOmegaF`.

  `pubOwnAt_alike`, `foldF_alike`, `frontPubOwnB_alike`, `frontOwnFiveB_alike`, `treesAtOmega_alike`   what the
                 tests read of a place: no more than `Alike` holds
  `headShape`, `omegaShape_head`   the shape of the door's state at the plan is `omegaShape` at the written
                 value
  `five_head_O`, `group_head_O`, `ts_head_O`, `many_head_O`, `width_head_O`, `own_head_O`, `bat_head_O`,
  `formPubB_head_O`, `k_head_O`, `depths_head_O`   the lines at the seated place
  `ts_of_front_own`   the number of the plain data's trees is a function of the thin shape
  `frontAsksO_head`   `FrontAsksO` (K12/Own/ShapeAsksOwn.lean) at every input and front

By what. `alike_head_O`, `planOB_head_O` (PlanAtSeat.lean); `alike_head_U`, `endOmega_alike`, `endOmega_plan`,
`three_head_OmegaF`, `shape_head_OmegaF` (K12/FrontAtHead.lean); `plain_ts` (K12/AsksAtHead.lean); `frontAsksO_all`
(K12/Own/FrontOwnFive.lean).

Limits.
- Public numbers and shapes under the head. True of the door's fall-back too: no statement that the state
  on entry is the verifier's: that is `enters`'s (OAccepted.lean).
- Conditional on the head. The full size alone.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes (Codes TableKey Group)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (codesFull2)
open Johnson.Prover.Link (batCut)
open Desc.K14 (St blocks)
open Desc.K14.Shape (doorO)
open H2K.JointK (laidOf)
open H2K.First (Plain)
open H2K.Member (piOFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.K12 (TestJob stA stN lettersOf frontPlainB₀)
open ProofFile.Honest.K12.Own (FrontAsksO frontOwnFiveB frontPubOwnB frontAsksO_all pubOwnAt foldF pass_of_five)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (Alike ManyJob jobAtOmega doorOmegaF endOmega sentOf tsLenOf manyFitsS
  widthFits widthFits_plan emptyOmega shapes_plan_Omega batThin_alike stA_alike stN_alike lettersOf_alike
  doorB_alike frontPlainB₀_alike tsLenOf_alike manyFitsS_alike depthOf_alike endOmega_alike endOmega_plan
  alike_head_U written_at_head qAt_written nums_head_O thin_head_O planOk_head_O formPubB_O formPubB_congr
  plain_ts three_head_OmegaF shape_head_OmegaF)
open ProofFile.Honest.Sh (TestSh testSh thinOf claimsB batThin)

section
variable {p q : P12} (A : Alike p q)
include A

theorem foldF_alike (L : OnBytes.GroupLayout) : foldF p L = foldF q L := by
  unfold foldF
  simp only [lettersOf_alike A, stA_alike A, stN_alike A]

theorem pubOwnAt_alike (L : OnBytes.GroupLayout) (id : Nat) (c : VerifiableInference.Desc.Ground.Sh.CoreSh) :
    pubOwnAt p L id c = pubOwnAt q L id c := by
  unfold pubOwnAt
  simp only [lettersOf_alike A, stA_alike A, stN_alike A]

theorem frontPubOwnB_alike (a : ProofFile.Honest.Sh.ThinSh) : frontPubOwnB p a = frontPubOwnB q a := by
  unfold frontPubOwnB
  simp only [batThin_alike A, pubOwnAt_alike A, foldF_alike A, A.nums]

/-- **`frontOwnFiveB` reads no more.** -/
theorem frontOwnFiveB_alike (K : Codes) (N : TestSh) :
    frontOwnFiveB p K N = frontOwnFiveB q K N := by
  have e : ((laidOf p).take 1).map (·.1) = ((laidOf q).take 1).map (·.1) := by
    rw [List.map_take, List.map_take, A.decls]
  unfold frontOwnFiveB
  simp only [e, doorB_alike A, lettersOf_alike A, stA_alike A, stN_alike A, frontPlainB₀_alike A,
    frontPubOwnB_alike A]

theorem treesAtOmega_alike : treesAtOmega p = treesAtOmega q := by
  unfold treesAtOmega
  rw [depthOf_alike A, depthOf_alike A, A.nums]

end

/-- **The number of the plain data's trees is a function of the thin shape of the state in front.** -/
theorem ts_of_front_own {W X : Type} (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
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

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- The one shape of the door's state at the test on G_omega, at the plan. -/
abbrev headShape (Zp : ProofFile.Pub) (Np : H2U.Places4) : TestSh :=
  doorO (endOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U)

/-- **Under the head that shape is `omegaShape` at the written value.** -/
theorem omegaShape_head (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ x, realSized = some (x, codesFull2) ∧ headShape Zp Np = omegaShape (x, codesFull2) ∧
      (K1.qAt Zp Np).codes = codesFull2 ∧ (K1.qAt Zp Np).S = x.shape := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  refine ⟨x, hx, ?_, by rw [qAt_written Wr Np], by rw [qAt_written Wr Np]⟩
  show doorO (endOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U) = _
  rw [endOmega_alike (alike_head_U h), qAt_written Wr Np,
    endOmega_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
  rfl

/-- **All the shape's clauses, at the seated place.** -/
theorem five_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    frontOwnFiveB pO codesFull2 (headShape Zp Np) = true := by
  obtain ⟨x, hx, e, -, -⟩ := omegaShape_head h
  rw [frontOwnFiveB_alike (alike_head_O h hO), e]
  have k := five_real
  rw [hx] at k
  simp only [Option.all_some] at k
  exact k

/-- **The group under test has one open row, and the members 2 and 3.** -/
theorem group_head_O (h : P5J.AtMg o Z D r Zp Np cF) :
    ((headShape Zp Np).core.st.groups[(headShape Zp Np).g]?).map rowsMembers = some (1, [2, 3]) := by
  obtain ⟨x, hx, e, -, -⟩ := omegaShape_head h
  rw [e]
  have k := group_real
  rw [hx] at k
  simpa only [Option.all_some, decide_eq_true_eq] using k

/-- **The plain data have three trees.** -/
theorem ts_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    tsLenOf pO (thinOf (headShape Zp Np)) = 3 := by
  obtain ⟨x, hx, e, -, -⟩ := omegaShape_head h
  rw [tsLenOf_alike (alike_head_O h hO), e]
  have k := ts_real_O
  rw [hx] at k
  simpa only [Option.all_some, decide_eq_true_eq] using k

/-- **`manyFitsS` at every job at the seated place.** -/
theorem many_head_O {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → Nat → OnBytes.E)) :
    manyFitsS pO ((jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).mems.map (·.shape))
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).trees
      (thinOf (headShape Zp Np)) = true := by
  obtain ⟨x, hx, e, eC, eS⟩ := omegaShape_head h
  have e1 := shapes_plan_Omega (K1.qAt Zp Np) 0 pO door weights rand omega?
  have e2 : (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).trees = treesAtOmega pO := rfl
  rw [e, e1, e2, eC, eS, manyFitsS_alike (alike_head_O h hO), treesAtOmega_alike (alike_head_O h hO)]
  have k := many_real_O
  rw [hx] at k
  simp only [Option.all_some] at k
  exact k

/-- **The widths of the sending's two trees.** -/
theorem width_head_O (h : P5J.AtMg o Z D r Zp Np cF) (n : Nat) :
    widthFits (jobOmega ⟨K1.qAt Zp Np, n⟩) 0 = true ∧
      widthFits (jobOmega ⟨K1.qAt Zp Np, n⟩) 1 = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := width_real_O
  rw [hx] at k
  have k' : (widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 0 &&
      widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 1) = true := k
  simp only [Bool.and_eq_true] at k'
  refine ⟨?_, ?_⟩
  · rw [(widthFits_plan _ 0).2, qAt_written Wr Np]
    exact k'.1
  · rw [(widthFits_plan _ 1).2, qAt_written Wr Np]
    exact k'.2

/-- The place's flag: the first fold sends its own table. -/
theorem own_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    pO.nums.ownMask = true := by
  rw [nums_head_O h hO]
  exact fresh_O

theorem bat_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    batCut (((laidOf pO).take 1).map (·.1)) = true := by
  rw [List.map_take, (alike_head_O h hO).decls, ← List.map_take]
  exact bat_O

theorem formPubB_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    formPubB pO = true := by
  rw [formPubB_congr (nums_head_O h hO) (thin_head_O h hO)]
  exact formPubB_O

/-- k = h + g at the first stage of the seated place. -/
theorem k_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (pO.nums.stages.headD default).k =
      (sgOf (pO.nums.stages.headD default)).h + (sgOf (pO.nums.stages.headD default)).g := by
  rw [nums_head_O h hO]
  exact first_k_O

/-- The depths of the trees that the test on G_omega opens. -/
theorem depths_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    Light.depthOf pO 0 = 22 ∧ Light.depthOf pO 1 = 13 ∧ (pO.nums.stages.headD default).Z.a = 13 := by
  unfold Light.depthOf
  rw [nums_head_O h hO]
  exact ⟨rfl, rfl, rfl⟩

/-- **`FrontAsksO` at every input and front, under the head**: there are plain data, which may hang on both.
True of the fall-back too: no statement that the state on entry is the verifier's. -/
theorem frontAsksO_head {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) (J : TestJob W X)
    (hp : J.p = pO) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hJ : J.rec₀ = doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols)
    (w : W) (fr : Front X) : ∃ Dp, FrontAsksO J w fr codesFull2 Dp :=
  frontAsksO_all J codesFull2 (headShape Zp Np)
    (by rw [hp]; exact H2K.JointK.early_of_planOk _ (planOk_head_O h hO))
    (fun w fr => by rw [hJ]; exact shape_head_OmegaF h bs hb key cols w fr)
    (by rw [hp]; exact five_head_O h hO)
    (fun w fr => by
      rw [hJ]
      exact ⟨(three_head_OmegaF h bs hb key cols w fr).tidy,
        (three_head_OmegaF h bs hb key cols w fr).plain,
        (three_head_OmegaF h bs hb key cols w fr).claims⟩) w fr

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.frontOwnFiveB_alike
#print axioms ProofFile.Honest.K12.AtFile.ts_of_front_own
#print axioms ProofFile.Honest.K12.AtFile.omegaShape_head
#print axioms ProofFile.Honest.K12.AtFile.five_head_O
#print axioms ProofFile.Honest.K12.AtFile.group_head_O
#print axioms ProofFile.Honest.K12.AtFile.ts_head_O
#print axioms ProofFile.Honest.K12.AtFile.many_head_O
#print axioms ProofFile.Honest.K12.AtFile.width_head_O
#print axioms ProofFile.Honest.K12.AtFile.own_head_O
#print axioms ProofFile.Honest.K12.AtFile.bat_head_O
#print axioms ProofFile.Honest.K12.AtFile.formPubB_head_O
#print axioms ProofFile.Honest.K12.AtFile.k_head_O
#print axioms ProofFile.Honest.K12.AtFile.depths_head_O
#print axioms ProofFile.Honest.K12.AtFile.frontAsksO_head
