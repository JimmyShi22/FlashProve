-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FitAtHead.lean: FitShared.lean's four public checks on members and
fresh table are true at the proof file's own plan of the shared chain and at the places at which the
description seats the chain's two proximity tests, under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean). With what FitSharedLaw.lean concludes from them at these arguments. It
imports Mathlib.

  `fits_at_head`   `sharedFitsU` and `freshFitsU` at the plan `qAt Zp Np`
                 (Johnson/Desc/K1/Law/SitsShared.lean) and the place `(fourOf Np).U`
                 (AtProof/Places.lean); `sharedFitsOmega` and `freshFitsOmega` at the same plan and
                 the place pO with `(fourOf Np).O = some pO`
  `rowsFit_head_U`, `rowsFit_head_Omega`   so `RunJob.rowsFit` is true at `jobAtU` and `jobAtOmega`
                 at these arguments, for every state function, every pair of readers, every vector
                 passed in, every input, whatever precedes the test, and all random values
  `freshFits_head_U`, `freshFits_head_Omega`   `TestJob.freshFits` is true there
  `freshDue_head`, `dueFresh_head`   the sender's count of the first fresh table's random values is
                 the test's, and it is 167
  `freshCoef_head`, `freshTail_head`, `freshTest_head`, `freshSums_head`   the numbers at which the
                 sender, the test's first state and the first fold's rounds read the table's
                 coefficients and tails
  `planOf`, `four_real`   the plan with the typed setting at given codes and a given shape; the
                 four checks at the typed sizes (`realSized`, Johnson/Desc/K1/Law/CondReal.lean)
                 and the written places `piUFull`, `piOFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean), evaluated by Lean's kernel
  `qAt_written`, `written_at_head`, `places_at_head`   under the head the plan is the typed one,
                 and the seated places have the written places' stages and own-mask flags

By what. Under the head the library's `Sh.written_of_made` gives its equations on the public part
(`Written`, Johnson/Goal/Numbers/WrittenAtZ.lean), so the plan holds the written codes and the typed
shape. `nums_at_head` (StagesAtHead.lean) with the library's `place_U_of_full`, `place_O_of_full`,
`more_U_of_full` and `more_O_of_full` gives the places' numbers. The checks read of a plan its codes
and shape alone, and of a place its first stage and its own-mask flag alone. The rest is one
evaluation. Johnson/Desc/ProofFile/Honest/K14/SendingsAtHead.lean has an equation like `qAt_written`
(`p14_of_written`) and the call in `written_at_head`; both are typed anew here, so that this file
needs neither that file nor what lies beneath it.

Limits.
- The full size alone: the head holds in the goals' scope, and the numbers are those of the written
  literals. Into `realSized` the first stages' sizes are written by hand; that the planner's sizes
  at the public files are these is what `Written` says.
- The theorems speak of the plan `qAt Zp Np` and of the seated places. That a job which a caller
  builds is `jobAtU` or `jobAtOmega` at these very arguments is up to that caller.
- The checks are made of `jobU` and `jobOmega` (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean,
  imported through JobShared.lean), a file of another folder: what the theorems say changes if that
  file changes. Johnson/Desc/ProofFile/Honest/K14/Parts.lean and four files of
  Johnson/Desc/ProofFile/Honest/ (Frame, ForKinds, Side, Sum) lie beneath as well.
- `qAt` is the library's. SendingsAtHead.lean states the check `sendingsFit` at a definition with
  the same short name (`ProofFile.Honest.K14.qAt`), whose defining file this one does not import. No
  theorem here says that the two are equal. That file's theorems stand under `P5J.AtMgA`, which
  gives the head used here by its parent field.
- The number 0 in `⟨qAt Zp Np, 0⟩` is the field `atPoint`, the number of the round "LIN point"; the
  checks do not read it.
- No example of the head is shown here. The library's side has one at the full size
  (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), and `real_members`
  (Johnson/Desc/K1/Law/CondReal.lean) says that `realSized` returns a value, so `four_real` is not
  empty.
- Other checks on these jobs are not treated here: `StagesOk` (StagesAtHead.lean,
  StagesOfPlan.lean), `ManyJob.layFits` (NearAtHead.lean), `OnBytes.linOk` (`linOk_at_head`,
  Johnson/Desc/ProofFile/Honest/K14/SendingsAtFilling.lean), and `sendingsFit` (SendFitAtHead.lean).
- The limits of FitShared.lean apply: no definition evaluates the checks; they speak of lengths,
  counts and numbers of random values, not of the values.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K12.FitSharedLaw
import Johnson.Desc.K1.Law.SitsShared
import Johnson.Desc.K14.Law.SharedConstCodesMade
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.K12.Law.Sizes.MoreAtScope
import Johnson.Desc.K1.Law.CondReal
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes)
open OnBytes.Params (LinSized LinShape recordSet)
open VerifiableInference.Desc.K1 (qAt realSized)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.G (codesFull2)
open Desc.K14 (p14Of beforePointOf)
open Desc.K14.Law (Written)
open H2K.Member (piUFull piOFull)
open H2K.JointK (pGomega)
open H2K.Pub (sgOf)
open Johnson.Prover.Link (packedN)
open ProofFile.Honest.K14 (SendPub jobU jobOmega laid dueOf)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 What the checks read -/

/-- The plan with the typed setting, the shared scope, item 0 and an empty list, at given codes and
a given shape; the number 0. -/
def planOf (codes : Codes) (S : LinShape) : SendPub := ⟨⟨recordSet, .shared, codes, S, 0, []⟩, 0⟩

theorem sharedFitsU_plan (A : SendPub) (p : P12) :
    sharedFitsU A p = sharedFitsU (planOf A.P.codes A.P.S) p := rfl

theorem sharedFitsOmega_plan (A : SendPub) (p : P12) :
    sharedFitsOmega A p = sharedFitsOmega (planOf A.P.codes A.P.S) p := rfl

theorem freshFitsU_plan (A : SendPub) (p : P12) :
    freshFitsU A p = freshFitsU (planOf A.P.codes A.P.S) p := rfl

theorem sharedFitsU_stages (A : SendPub) {p q : P12} (h : p.nums.stages = q.nums.stages) :
    sharedFitsU A p = sharedFitsU A q := by
  unfold sharedFitsU stage₀
  rw [h]

theorem sharedFitsOmega_stages (A : SendPub) {p q : P12} (h : p.nums.stages = q.nums.stages) :
    sharedFitsOmega A p = sharedFitsOmega A q := by
  unfold sharedFitsOmega stage₀
  rw [h]

theorem freshFitsU_stages (A : SendPub) {p q : P12} (h : p.nums.stages = q.nums.stages)
    (ho : p.nums.ownMask = q.nums.ownMask) : freshFitsU A p = freshFitsU A q := by
  unfold freshFitsU stage₀
  rw [h, ho]

/-! ## 2 At the typed sizes and the written places -/

theorem four_real : (realSized.all fun q =>
    sharedFitsU (planOf q.2 q.1.shape) piUFull && freshFitsU (planOf q.2 q.1.shape) piUFull &&
      sharedFitsOmega (planOf q.2 q.1.shape) piOFull && freshFitsOmega piOFull) = true := by
  decide +kernel

/-! ## 3 Under the head -/

/-- Under the library's equations on the public part the shared chain's plan is the typed one. -/
theorem qAt_written {Z : ProofFile.Pub} {x : LinSized} (Wr : Written Z x) (N : H2U.Places4) :
    qAt Z N = ⟨recordSet, .shared, codesFull2, x.shape, 0, beforePointOf N⟩ := by
  show p14Of Z.p.chains (beforePointOf N) = _
  unfold p14Of
  simp only [Wr.set, Wr.codes, Wr.shape, Wr.batch, Bool.false_eq_true, if_false]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem written_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ x, realSized = some (x, codesFull2) ∧ Written Zp x :=
  Desc.K14.Law.Sh.written_of_made h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- Under the head the two seated places have the written places' stages and own-mask flags. -/
theorem places_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).U.nums.stages = piUFull.nums.stages ∧
    (fourOf Np).U.nums.ownMask = piUFull.nums.ownMask ∧
    ∃ pO, (fourOf Np).O = some pO ∧ pO.nums.stages = piOFull.nums.stages ∧
      pO.nums.ownMask = piOFull.nums.ownMask := by
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  obtain ⟨_, nU, ⟨nO, hO, nOm⟩, _⟩ := nums_at_head h
  refine ⟨?_, ?_, pGomega nO, ?_, ?_, ?_⟩
  · rw [nU]
    exact (H2K.Sizes.place_U_of_full A h.laid.places).1
  · rw [nU]
    exact (H2K.Sizes.more_U_of_full A h.laid.places).2.1
  · show Np.O.map _ = _
    rw [hO]
    rfl
  · rw [nOm]
    exact (H2K.Sizes.place_O_of_full A h.laid.places nO hO).1
  · rw [nOm]
    exact (H2K.Sizes.more_O_of_full A h.laid.places nO hO).2.1

/-- **The four public checks at the shared chain's own plan and at the seated places, under the
head.** -/
theorem fits_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    sharedFitsU ⟨qAt Zp Np, 0⟩ (fourOf Np).U = true ∧
    freshFitsU ⟨qAt Zp Np, 0⟩ (fourOf Np).U = true ∧
    ∃ pO, (fourOf Np).O = some pO ∧ sharedFitsOmega ⟨qAt Zp Np, 0⟩ pO = true ∧
      freshFitsOmega pO = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨sU, oU, pO, hO, sO, oO⟩ := places_at_head h
  have k := four_real
  rw [hx] at k
  have k' : (sharedFitsU (planOf codesFull2 x.shape) piUFull &&
      freshFitsU (planOf codesFull2 x.shape) piUFull &&
      sharedFitsOmega (planOf codesFull2 x.shape) piOFull && freshFitsOmega piOFull) = true := k
  simp only [Bool.and_eq_true] at k'
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := k'
  refine ⟨?_, ?_, pO, hO, ?_, ?_⟩
  · rw [sharedFitsU_plan, qAt_written Wr Np, sharedFitsU_stages _ sU]
    exact k1
  · rw [freshFitsU_plan, qAt_written Wr Np, freshFitsU_stages _ sU oU]
    exact k2
  · rw [sharedFitsOmega_plan, qAt_written Wr Np, sharedFitsOmega_stages _ sO]
    exact k3
  · show pO.nums.ownMask = true
    rw [oO]
    exact k4

/-! ## 4 What follows at the two jobs -/

variable {W X : Type}

theorem rowsFit_head_U (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (mem : ℕ → Stretch) :
    (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.rowsFit w fr mem = true :=
  rowsFit_atU _ _ (fits_at_head h).1 door weights rand u? w fr mem

theorem rowsFit_head_Omega (h : P5J.AtMg o Z D r Zp Np cF) (pO : P12)
    (hO : (fourOf Np).O = some pO) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X)
    (mem : ℕ → Stretch) :
    (jobAtOmega ⟨qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.rowsFit w fr mem = true := by
  obtain ⟨_, _, q, hq, a, _⟩ := fits_at_head h
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  exact rowsFit_atOmega _ _ a door weights rand omega? w fr mem

theorem freshFits_head_U (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest.freshFits = true :=
  freshFits_atU _ _ (fits_at_head h).2.1 door weights rand u?

theorem freshFits_head_Omega (h : P5J.AtMg o Z D r Zp Np cF) (pO : P12)
    (hO : (fourOf Np).O = some pO) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega ⟨qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest.freshFits = true := by
  obtain ⟨_, _, q, hq, _, b⟩ := fits_at_head h
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  exact freshFits_atOmega _ _ b door weights rand omega?

theorem freshDue_head (h : P5J.AtMg o Z D r Zp Np cF) :
    dueOf (jobU ⟨qAt Zp Np, 0⟩).Q.codes (shapeAt (jobU ⟨qAt Zp Np, 0⟩) 1)
        ((jobU ⟨qAt Zp Np, 0⟩).sort 1) = dueFresh (stage₀ (fourOf Np).U) :=
  freshDue_atU _ _ (fits_at_head h).2.1

/-- At the first stage k = 7, h = 0 and the mask code's tail has 152 entries. -/
theorem dueFresh_head (h : P5J.AtMg o Z D r Zp Np cF) : dueFresh (stage₀ (fourOf Np).U) = 167 := by
  unfold stage₀
  rw [(places_at_head h).1]
  rfl

theorem freshCoef_head (h : P5J.AtMg o Z D r Zp Np cF) (v cs : ℕ → OnBytes.E) (b j : ℕ) :
    (laid (jobU ⟨qAt Zp Np, 0⟩).Q.codes (shapeAt (jobU ⟨qAt Zp Np, 0⟩) 1) v cs
        ((jobU ⟨qAt Zp Np, 0⟩).sort 1)).mask b j =
      OnBytes.E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two (stage₀ (fourOf Np).U).k
        (stage₀ (fourOf Np).U).h
        ⟨fun l t => (cs (coefAt (stage₀ (fourOf Np).U).k l t)).triple,
          (cs (2 * ((stage₀ (fourOf Np).U).k - 1))).triple⟩ b).getD j Fmt.Fld.zeroE) :=
  freshCoef_atU _ _ (fits_at_head h).2.1 v cs b j

theorem freshTail_head (h : P5J.AtMg o Z D r Zp Np cF) (v cs : ℕ → OnBytes.E) (b q : ℕ) :
    (laid (jobU ⟨qAt Zp Np, 0⟩).Q.codes (shapeAt (jobU ⟨qAt Zp Np, 0⟩) 1) v cs
        ((jobU ⟨qAt Zp Np, 0⟩).sort 1)).maskTail b q =
      cs (2 * (stage₀ (fourOf Np).U).k + 1 + b * (stage₀ (fourOf Np).U).Z.r + q) :=
  freshTail_atU _ _ (fits_at_head h).2.1 v cs b q

theorem freshTest_head (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (C : TestCoins) :
    ((jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest.first w fr C).fM =
      packedN (sgOf (stage₀ (fourOf Np).U))
        (byName ((sgOf (stage₀ (fourOf Np).U)).h + (sgOf (stage₀ (fourOf Np).U)).g)
          (fun l t => C.hide (coefAt (stage₀ (fourOf Np).U).k l t))
          (C.hide (2 * ((stage₀ (fourOf Np).U).k - 1)))) :=
  freshTest_atU _ _ (fits_at_head h).2.1 door weights rand u? w fr C

theorem freshSums_head (h : P5J.AtMg o Z D r Zp Np cF) (C : TestCoins) :
    (coinsOf (fourOf Np).U.nums.stages C.hide C.rest).W (sgOf (stage₀ (fourOf Np).U)) 0 =
      byName ((sgOf (stage₀ (fourOf Np).U)).h + (sgOf (stage₀ (fourOf Np).U)).g)
        (fun l t => C.hide (coefAt (stage₀ (fourOf Np).U).k l t))
        (C.hide (2 * ((stage₀ (fourOf Np).U).k - 1))) :=
  freshSums_atU ⟨qAt Zp Np, 0⟩ _ (fits_at_head h).2.1 C

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sharedFitsU_plan
#print axioms ProofFile.Honest.K12.Light.sharedFitsOmega_plan
#print axioms ProofFile.Honest.K12.Light.freshFitsU_plan
#print axioms ProofFile.Honest.K12.Light.sharedFitsU_stages
#print axioms ProofFile.Honest.K12.Light.sharedFitsOmega_stages
#print axioms ProofFile.Honest.K12.Light.freshFitsU_stages
#print axioms ProofFile.Honest.K12.Light.four_real
#print axioms ProofFile.Honest.K12.Light.qAt_written
#print axioms ProofFile.Honest.K12.Light.written_at_head
#print axioms ProofFile.Honest.K12.Light.places_at_head
#print axioms ProofFile.Honest.K12.Light.fits_at_head
#print axioms ProofFile.Honest.K12.Light.rowsFit_head_U
#print axioms ProofFile.Honest.K12.Light.rowsFit_head_Omega
#print axioms ProofFile.Honest.K12.Light.freshFits_head_U
#print axioms ProofFile.Honest.K12.Light.freshFits_head_Omega
#print axioms ProofFile.Honest.K12.Light.freshDue_head
#print axioms ProofFile.Honest.K12.Light.dueFresh_head
#print axioms ProofFile.Honest.K12.Light.freshCoef_head
#print axioms ProofFile.Honest.K12.Light.freshTail_head
#print axioms ProofFile.Honest.K12.Light.freshTest_head
#print axioms ProofFile.Honest.K12.Light.freshSums_head
#print axioms ProofFile.Honest.K12.Light.planOf
