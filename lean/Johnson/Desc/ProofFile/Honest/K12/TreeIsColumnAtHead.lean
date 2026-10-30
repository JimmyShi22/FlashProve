-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreeIsColumnAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean) the two public checks `colFitsU` and `colFitsOmega` (TreeIsColumnAt.lean) are
true at the proof file's own plan `qAt Zp Np` (Johnson/Desc/K1/Law/SitsShared.lean) and the seated
places; and so, at the jobs `jobAtU` and `jobAtOmega` there, the column of a tree that the first
round of positions opens is, at every position, the column of the table that the sending built. Of
the premises of TreeIsColumnAt.lean's four statements the public ones are paid here; the three that
are not public stay. It imports Mathlib.

  `colFitsU_plan`, `colFitsOmega_plan`, `colFitsU_stages`, `colFitsOmega_stages`   the checks read
                 of a plan its codes and shape, and of a place its stages
  `col_real`     both checks at the typed sizes and the written places `piUFull`, `piOFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean): one evaluation by Lean's kernel
  `colFits_head`   both checks under the head, at every number n of "LIN point"
  `room_head_U`  2 k + 1 ≤ h + Z.l at the first stage of the seated place of the test on G_u
  `tree0_head_U`, `tree1_head_U`, `tree0_head_Omega`, `tree1_head_Omega`   the four statements

By what. `written_at_head`, `qAt_written`, `places_at_head`, `fits_at_head` (FitAtHead.lean);
`sendingsFit_head` (SendFitAtHead.lean); the four statements of TreeIsColumnAt.lean, called.

Limits.
- Three premises are not public and are shown nowhere here: `SameCut`, `SameFresh` (FreshAtJob.lean)
  and "the same vector". That a member's random values are the sender's, cut from the message's
  offset on, is up to the book of lent values; that the vector which the member carries is the one
  that the sender computed at its own state is up to the caller.
- Nothing on a tree's depth. Nothing on the third tree of `jobAtOmega`.
- Nothing says that a table with these columns was sent, or that a run lists them.
- The state on entry is any function. The n in `⟨qAt Zp Np, n⟩` is the field `atPoint` of `SendPub`
  (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean), the number of the round "LIN point": every
  statement here holds at every n; which n a played sending has is not treated.
- The full size alone. No example of the head is shown here.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt
import Johnson.Desc.ProofFile.Honest.K12.SendFitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (zeroE)
open VerifiableInference.Desc.K1 (qAt realSized)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.G (codesFull2)
open H2K.Member (piUFull piOFull)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf columnOf Ask)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 What the checks read -/

theorem colFitsU_plan (A : SendPub) (p : P12) :
    colFitsU A p = colFitsU (planOf A.P.codes A.P.S) p := rfl

theorem colFitsOmega_plan (A : SendPub) (p : P12) :
    colFitsOmega A p = colFitsOmega (planOf A.P.codes A.P.S) p := rfl

theorem colFitsU_stages (A : SendPub) {p q : P12} (h : p.nums.stages = q.nums.stages) :
    colFitsU A p = colFitsU A q := by
  unfold colFitsU stage₀
  rw [h]

theorem colFitsOmega_stages (A : SendPub) {p q : P12} (h : p.nums.stages = q.nums.stages) :
    colFitsOmega A p = colFitsOmega A q := by
  unfold colFitsOmega stage₀
  rw [h]

/-! ## 2 At the typed sizes and the written places -/

theorem col_real : (realSized.all fun q =>
    colFitsU (planOf q.2 q.1.shape) piUFull && colFitsOmega (planOf q.2 q.1.shape) piOFull) =
      true := by
  decide +kernel

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The two checks at the shared chain's own plan and at the seated places, under the head.** -/
theorem colFits_head (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) :
    colFitsU ⟨qAt Zp Np, n⟩ (fourOf Np).U = true ∧
      ∃ pO, (fourOf Np).O = some pO ∧ colFitsOmega ⟨qAt Zp Np, n⟩ pO = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨sU, _, pO, hO, sO, _⟩ := places_at_head h
  have k := col_real
  rw [hx] at k
  have k' : (colFitsU (planOf codesFull2 x.shape) piUFull &&
      colFitsOmega (planOf codesFull2 x.shape) piOFull) = true := k
  simp only [Bool.and_eq_true] at k'
  refine ⟨?_, pO, hO, ?_⟩
  · rw [colFitsU_plan, qAt_written Wr Np, colFitsU_stages _ sU]
    exact k'.1
  · rw [colFitsOmega_plan, qAt_written Wr Np, colFitsOmega_stages _ sO]
    exact k'.2

theorem room_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    2 * (stage₀ (fourOf Np).U).k + 1 ≤ (stage₀ (fourOf Np).U).h + (stage₀ (fourOf Np).U).Z.l := by
  unfold stage₀
  rw [(places_at_head h).1]
  decide

/-! ## 4 The four statements at the real plan -/

section Jobs
variable {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) (door : W → Front X → T12)
  (weights : W → Weights) (rand : W → TableRand) (v? : Option (W → Front X → ℕ → OnBytes.E))
  (w : W) (fr : Front X) (C : TestCoins) (st : State Ask Unit) (cs : Array OnBytes.E) (x : ℕ)

include h in
/-- **o_u's tree, with the first fresh table that rides in it.** -/
theorem tree0_head_U (cut : SameCut (jobU ⟨qAt Zp Np, n⟩) 0 cs (C.mem 0))
    (ride : SameFresh (stage₀ (fourOf Np).U) (fun i =>
      cs.getD (offsetOf (jobU ⟨qAt Zp Np, n⟩).Q.codes (jobU ⟨qAt Zp Np, n⟩).Q.sent
        (jobU ⟨qAt Zp Np, n⟩).sort 1 + i) zeroE) C)
    (hv : vecAt (jobU ⟨qAt Zp Np, n⟩) 0 (askOf ⟨qAt Zp Np, n⟩ weights rand) v? w fr =
      (jobU ⟨qAt Zp Np, n⟩).data st 0) :
    (((jobAtU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v?).toRun.toTest.first w fr
        C)).getD 0 (0, fun _ => [])).2 x =
      columnOf (jobU ⟨qAt Zp Np, n⟩).Q.codes (jobU ⟨qAt Zp Np, n⟩).Q.sent
        ((jobU ⟨qAt Zp Np, n⟩).rows st cs) 0 x :=
  tree0_atU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v? (sendingsFit_head h) w fr C st cs x
    (colFits_head h n).1 ((freshFitsU_plan ⟨qAt Zp Np, n⟩ _).trans (fits_at_head h).2.1)
    (room_head_U h) cut ride hv

include h in
/-- **o_sp's tree, at the test on G_u.** -/
theorem tree1_head_U (cut : SameCut (jobOmega ⟨qAt Zp Np, n⟩) 1 cs (C.mem 1)) :
    (((jobAtU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v?).toRun.toTest.first w fr
        C)).getD 1 (0, fun _ => [])).2 x =
      columnOf (jobOmega ⟨qAt Zp Np, n⟩).Q.codes (jobOmega ⟨qAt Zp Np, n⟩).Q.sent
        ((jobOmega ⟨qAt Zp Np, n⟩).rows st cs) 1 x :=
  tree1_atU ⟨qAt Zp Np, n⟩ (fourOf Np).U door weights rand v? (sendingsFit_head h) w fr C st cs x
    (colFits_head h n).1 cut

include h in
/-- **o_omega's tree.** -/
theorem tree0_head_Omega (pO : P12) (hO : (fourOf Np).O = some pO)
    (cut : SameCut (jobOmega ⟨qAt Zp Np, n⟩) 0 cs (C.mem 0))
    (hv : vecAt (jobOmega ⟨qAt Zp Np, n⟩) 0 (askOf ⟨qAt Zp Np, n⟩ weights rand) v? w fr =
      (jobOmega ⟨qAt Zp Np, n⟩).data st 0) :
    (((jobAtOmega ⟨qAt Zp Np, n⟩ pO door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtOmega ⟨qAt Zp Np, n⟩ pO door weights rand v?).toRun.toTest.first w fr C)).getD 0
        (0, fun _ => [])).2 x =
      columnOf (jobOmega ⟨qAt Zp Np, n⟩).Q.codes (jobOmega ⟨qAt Zp Np, n⟩).Q.sent
        ((jobOmega ⟨qAt Zp Np, n⟩).rows st cs) 0 x := by
  obtain ⟨_, q, hq, a⟩ := colFits_head h n
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  exact tree0_atOmega ⟨qAt Zp Np, n⟩ q door weights rand v? (sendingsFit_head h) w fr C st cs x a
    cut hv

include h in
/-- **o_sp's tree, at the test on G_omega.** -/
theorem tree1_head_Omega (pO : P12) (hO : (fourOf Np).O = some pO)
    (cut : SameCut (jobOmega ⟨qAt Zp Np, n⟩) 1 cs (C.mem 1)) :
    (((jobAtOmega ⟨qAt Zp Np, n⟩ pO door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtOmega ⟨qAt Zp Np, n⟩ pO door weights rand v?).toRun.toTest.first w fr C)).getD 1
        (0, fun _ => [])).2 x =
      columnOf (jobOmega ⟨qAt Zp Np, n⟩).Q.codes (jobOmega ⟨qAt Zp Np, n⟩).Q.sent
        ((jobOmega ⟨qAt Zp Np, n⟩).rows st cs) 1 x := by
  obtain ⟨_, q, hq, a⟩ := colFits_head h n
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  exact tree1_atOmega ⟨qAt Zp Np, n⟩ q door weights rand v? (sendingsFit_head h) w fr C st cs x a
    cut

end Jobs

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.colFitsU_plan
#print axioms ProofFile.Honest.K12.Light.colFitsOmega_plan
#print axioms ProofFile.Honest.K12.Light.colFitsU_stages
#print axioms ProofFile.Honest.K12.Light.colFitsOmega_stages
#print axioms ProofFile.Honest.K12.Light.col_real
#print axioms ProofFile.Honest.K12.Light.colFits_head
#print axioms ProofFile.Honest.K12.Light.room_head_U
#print axioms ProofFile.Honest.K12.Light.tree0_head_U
#print axioms ProofFile.Honest.K12.Light.tree1_head_U
#print axioms ProofFile.Honest.K12.Light.tree0_head_Omega
#print axioms ProofFile.Honest.K12.Light.tree1_head_Omega
