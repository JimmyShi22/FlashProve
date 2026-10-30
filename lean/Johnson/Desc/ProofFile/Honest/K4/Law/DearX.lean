-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/DearX.lean: CONDITIONAL.

What is here. THE TEST ON THE PUBLIC PARAMETERS `k4PublicX` (Law/PublicX.lean) ACCEPTS UNDER h :
AtMgA, the hypothesis on the public files: ALL FOURTEEN CLAUSES, AT EACH OF THE TWELVE GROUPS. So
the hypothesis `k4PublicX (P5J.At.X Zp) = true` of `k4_accepted_one` (Law/PublicOne.lean) falls.
(What its hypothesis half holds of the plan stays: Law/DearTop.lean's head.) By other writers'
statements, called at the lines of the library's `refPub_in_scope`
(Johnson/Road/K4/RefInScope.lean): `light_head` (Johnson/Road/K4/C/PublicLight.lean: ten clauses) ·
`laidLayers_of_layout` (C/LaidPub.lean) · `joinB_of` (C/JoinBOf.lean) · `pansB_plan`
(C/PansBPlan.lean) · `claimsB_plan` (C/ClaimsBPlan.lean), with the closed facts `freeReads`,
`freePlan` and `freeNums` (C/Free/; `light_head` brings four more: `freeDepth`, `freeSlots`,
`freeTables`, `freePoints`) and the library's `vocab_at_head` (Johnson/P5J/VocabAtHead.lean).
Statements with their proofs: calls.

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). h IS `publicX_head`'s ONLY HYPOTHESIS. The eight others take g <
12 and name what the plan has at the group (hG; hu and ht in two of them): that the plan has it
there is `plan_head`'s, under h and g < 12; hu and ht are had inside `shapeB_head` and
`hearPB_head`, which call these two and do not ask them. Nothing is evaluated here. THE FULL SIZE
ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function, alone. THE BOUND 12 IS THE FULL SIZE's
NUMBER OF GROUPS: a group from 12 on is not tested. TEN OF THE FOURTEEN CLAUSES OF THE TEST ON THE
PLAN REST WHOLLY ON CHECKS BY LEAN's OWN KERNEL (`kernel_rfl`: seven facts under
Johnson/Road/K4/C/Free/, over Johnson/Road/K4/RowHead/ClosedAt.lean and ClosedTies.lean); three more
lean on one such fact beside a law; no independent checker has replayed them. A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one: ALL NINE STATEMENTS
REST ON STATEMENTS OF FILES UNDER Johnson/Goal/: through the library's `refPub_in_scope`
(`Meaning.P34.pub34_all`), through `twins_head`'s call of `Hd.scan_of_scope`, and `claimsB_head`
through the library's `vocab_at_head` beside. Transitive imports, by a program's walk over import
lines. Opening every module that it reaches: 54 modules under Johnson/Goal/, 48 whose name holds
RecCompile, 140 under ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/
(so these are floors): 21 under Johnson/Goal/, 46 whose name holds RecCompile, 2 under ThirdParty/.
By both: none under Johnson/D/; none of RecCompile's Honest*, Both or PassH*.
No property is claimed.

  `laidKeys_head`   under h the host's count of the padding keys is the layout's.
  `joinB_head`   under h each call's factor in the join is there (`joinB`).
  `pansB_head`   under h the panels' test accepts at the blank environment (`pansB`).
  `claimsB_head`   under h the weight claims' test accepts (`claimsB`).
  `plan_head`   under h each of the twelve groups has a plan.
  `shapeB_head`, `hearPB_head`   under h `k4ShapeB` and `hearPB` accept at each group's plan.
  `publicB_head`   **`k4PublicB` at each group's plan, under h.**
  `publicX_head`   **`k4PublicX (P5J.At.X Zp) = true`, under h.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PublicX
import Johnson.Road.K4.C.PublicLight
import Johnson.Road.K4.C.LaidPub
import Johnson.Road.K4.C.JoinBOf
import Johnson.Road.K4.C.Free.FreeReads
import Johnson.Road.K4.C.PansBPlan
import Johnson.Road.K4.C.Free.FreePlan
import Johnson.Road.K4.C.ClaimsBPlan
import Johnson.P5J.VocabAtHead
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4.Rt (k4Takes planNumsB joinB pointsB)
open OnBytes.Desc.First.K4.RtPub (hearPB hearB tablesAt matsAt tablesB pansB claimsB blankEnv
  nclpOf)
open OnBytes.Road.K4 (refPub_in_scope)
open OnBytes.Road.K4.C (light_head twins_head twins_head_all laidLayers_of_layout joinB_of
  pansB_plan claimsB_plan)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (laidLayers)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **Under h the host's count of the padding keys is the layout's.** -/
theorem laidKeys_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    laidLayers (P5J.At.X Zp).layers = some (P5J.At.X Zp).layers.y.fo.pub := by
  obtain ⟨s0, hL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := hL (P5J.At.X Zp).layers.tokv
  exact laidLayers_of_layout (P := (P5J.At.X Zp).layers) L.hy L.S L.Z L.hN

/-- **Under h each call's factor in the join is there**, at the array and the places that the plan
names. -/
theorem joinB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) {iU3 : ℕ}
    (hu : hp.tl.ix.U.getD 2 none = some iU3)
    {rr : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    (ht : tablesAt (P5J.At.X Zp).layers g = some rr) :
    joinB (P5J.At.X Zp).layers hp g iU3 rr.1 = true := by
  obtain ⟨s0, hL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := hL (P5J.At.X Zp).layers.tokv
  have f := twins_head_all h _ OnBytes.Road.K4.C.Free.freeReads hg hG
  rw [hu, ht, Option.any_some, Option.any_some, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq] at f
  have hl := ht
  unfold OnBytes.Desc.First.K4.RtPub.tablesAt matsAt at hl
  have hm : ((P5J.At.X Zp).layers.tails.getD g {}).mats.map (fun M => (M.m, M.k)) =
      OnBytes.Road.matsR (P5J.At.X Zp).layers.y g := L.hmats
  rw [hm] at hl
  exact joinB_of (P := (P5J.At.X Zp).layers) L.hy L.S L.h4 L.hg L.hrd hl f.1 f.2

/-- **Under h the panels' test accepts**, at the blank environment, at the array and the places that
the plan names. -/
theorem pansB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) {iU3 : ℕ}
    (hu : hp.tl.ix.U.getD 2 none = some iU3)
    {rr : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    (ht : tablesAt (P5J.At.X Zp).layers g = some rr) :
    pansB (P5J.At.X Zp).layers (blankEnv (P5J.At.X Zp).layers hp g iU3 rr.1) hp.lamS
      (nclpOf hp g) = true := by
  obtain ⟨s0, hL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := hL (P5J.At.X Zp).layers.tokv
  have f := twins_head_all h _ OnBytes.Road.K4.C.Free.freeReads hg hG
  rw [hu, ht, Option.any_some, Option.any_some, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq] at f
  have p := twins_head_all h _ OnBytes.Road.K4.C.Free.freePlan hg hG
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at p
  have hl := ht
  unfold OnBytes.Desc.First.K4.RtPub.tablesAt matsAt at hl
  have hm : ((P5J.At.X Zp).layers.tails.getD g {}).mats.map (fun M => (M.m, M.k)) =
      OnBytes.Road.matsR (P5J.At.X Zp).layers.y g := L.hmats
  rw [hm] at hl
  exact pansB_plan (P := (P5J.At.X Zp).layers) L.hy L.S L.h4 L.hg L.hrd L.hN hl f.1 f.2 p.1.1 p.1.2
    p.2

/-- **Under h the weight claims' test accepts**, at each group's plan. -/
theorem claimsB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    claimsB (P5J.At.X Zp).layers hp g = true := by
  obtain ⟨s0, hL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := hL (P5J.At.X Zp).layers.tokv
  have p := twins_head_all h _ OnBytes.Road.K4.C.Free.freePlan hg hG
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at p
  have v := P5J.vocab_at_head h.toAtMg
  exact claimsB_plan (P := (P5J.At.X Zp).layers) L.hy L.S L.h4 L.hg L.hrd L.hN L.Z L.Zw L.hsL L.hlw
    (by
      show (P5J.At.X Zp).P.h.V = (P5J.At.X Zp).layers.V
      rw [v.1, v.2.2]) p.1.1 p.1.2

/-- **Under h each of the twelve groups has a plan.** -/
theorem plan_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    ∃ hp, (P5J.At.X Zp).G[g]? = some hp := by
  have t := List.all_eq_true.1 (twins_head h _ OnBytes.Road.K4.C.Free.freeNums) g
    (List.mem_range.2 hg)
  cases hG : (P5J.At.X Zp).G[g]? with
  | none =>
    rw [hG] at t
    cases t
  | some hp => exact ⟨hp, rfl⟩

/-- **Under h the five tests of `k4ShapeB` accept**, at each group's plan. -/
theorem shapeB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    k4ShapeB (parAt (P5J.At.X Zp).layers hp g) = true := by
  obtain ⟨-, a2, -, a4, a5, -, -, a8, a9, -⟩ := light_head h hg hG
  have aL := laidKeys_head h hg hG
  obtain ⟨iU3, hu⟩ := Option.isSome_iff_exists.mp a8
  unfold tablesB at a9
  cases ht : tablesAt (P5J.At.X Zp).layers g with
  | none =>
    rw [ht] at a9
    cases a9
  | some rr =>
    have hJ := joinB_head h hg hG hu ht
    unfold k4ShapeB
    show ((laidLayers (P5J.At.X Zp).layers == some (P5J.At.X Zp).layers.y.fo.pub) &&
      ((hp.tl.ix.U.getD 2 none).all fun iU3 =>
        (tablesAt (P5J.At.X Zp).layers g).all fun r =>
          joinB (P5J.At.X Zp).layers hp g iU3 r.1) &&
      (Forest.planeCols (P5J.At.X Zp).layers.y.fo (P5J.At.X Zp).layers.y.h.lmb).toBool &&
      decide ((P5J.At.X Zp).layers.y.h.la ≤ (P5J.At.X Zp).layers.y.fo.dT) &&
      ((P5J.At.X Zp).layers.y.fo.calls.size == (P5J.At.X Zp).layers.y.calls.size)) = true
    rw [aL, hu, ht, a5, a4]
    simp only [Option.all_some, beq_self_eq_true, Bool.true_and, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hJ, a2⟩

/-- **Under h the pure functions that the hearing calls return** (`hearPB`), at each group's
plan. -/
theorem hearPB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    hearPB (P5J.At.X Zp).layers hp g = true := by
  obtain ⟨-, -, -, -, -, -, a7, a8, a9, a10⟩ := light_head h hg hG
  have hCl := claimsB_head h hg hG
  obtain ⟨iU3, hu⟩ := Option.isSome_iff_exists.mp a8
  unfold tablesB at a9
  cases ht : tablesAt (P5J.At.X Zp).layers g with
  | none =>
    rw [ht] at a9
    cases a9
  | some rr =>
    rw [ht, Option.any_some] at a9 a10
    have hPJ := pansB_head h hg hG hu ht
    unfold hearPB hearB
    rw [a7, hu, ht]
    simp only [Option.any_some, Bool.true_and, Bool.and_eq_true]
    exact ⟨⟨⟨a9, hPJ⟩, hCl⟩, a10⟩

/-- **`k4PublicB` AT EACH GROUP's PLAN, UNDER h.** -/
theorem publicB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    k4PublicB (parAt (P5J.At.X Zp).layers hp g) = true := by
  obtain ⟨a1, -, a3, -, -, a6, -, -, -, -⟩ := light_head h hg hG
  unfold k4PublicB
  show (planNumsB (P5J.At.X Zp).layers hp g && hearPB (P5J.At.X Zp).layers hp g &&
    k4ShapeB (parAt (P5J.At.X Zp).layers hp g) &&
    decide (Forest.elems (P5J.At.X Zp).layers.y.fo + k4Takes (P5J.At.X Zp).layers hp g ≤ hp.ns) &&
    decide ((P5J.At.X Zp).layers.y.h.lt ≤ (P5J.At.X Zp).layers.y.fo.dT)) = true
  rw [a1, hearPB_head h hg hG, shapeB_head h hg hG, decide_eq_true a6, decide_eq_true a3]
  rfl

/-- CONDITIONAL: on h. **THE TEST ON THE PUBLIC PARAMETERS ACCEPTS UNDER h.** -/
theorem publicX_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    k4PublicX (P5J.At.X Zp) = true := by
  unfold k4PublicX
  refine List.all_eq_true.2 fun g hg => ?_
  obtain ⟨hp, hG⟩ := plan_head h (List.mem_range.1 hg)
  rw [hG, Option.any_some]
  exact publicB_head h (List.mem_range.1 hg) hG

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.laidKeys_head
#print axioms ProofFile.Honest.K4.joinB_head
#print axioms ProofFile.Honest.K4.pansB_head
#print axioms ProofFile.Honest.K4.claimsB_head
#print axioms ProofFile.Honest.K4.plan_head
#print axioms ProofFile.Honest.K4.shapeB_head
#print axioms ProofFile.Honest.K4.hearPB_head
#print axioms ProofFile.Honest.K4.publicB_head
#print axioms ProofFile.Honest.K4.publicX_head
