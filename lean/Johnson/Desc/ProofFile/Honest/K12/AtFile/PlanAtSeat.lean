-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/PlanAtSeat.lean: the tests on the plan of the proof file's
three proximity tests, carried from the written places to the seated places, under the library's head
(`P5J.AtMg`): and so `PlanPlays` (K12/PlaysK12.lean) at every job at a seated place. The seated
places and the written ones differ in their pieces, which no test here reads.

  `tablesFitB_bare`, `newWideB_stages`   the two tests read of a bare job no more than the numbers and
                 `thinOf` (Sim/FirstPubAtHead.lean)
  `planPlaysB_congr`   `planPlaysB` is one at two places with the same numbers and the same `thinOf`
                 whose blocks pass their test on the plan
  `planPlaysB_head_U`, `planPlaysB_head_O`, `planPlaysB_head_W`   the test at the seated places
  `planPlays_head_U`, `planPlays_head_O`, `planPlays_head_W`   `PlanPlays` at every job at a seated
                 place whose word on the fresh table is the place's
  `idx_real_O`, `idx_head_O`, `alike_head_O`   the code numbers at G_omega; the seated place and the
                 written one are alike (`Alike`, K12/FrontAtHead.lean)
  `oracles_length`, `alike_renum`   two alike places whose blocks pass stay alike when renumbered
  `planOB_alike`, `planOB_head_O`   the plan's half of the own twin (`planOB`, Own/PlanOwn.lean) at the
                 seated place of the test on G_omega

By what. `plan_U`, `plan_O`, `plan_W` (PlanKernel.lean); `nums_head_U`, `thin_head_U`, `tabB_congr`,
`asked_thin` (Sim/FirstPubAtHead.lean); `nums_head_O`, `thin_head_O`, `planOk_head_O`, `omega_of_four`
(Sim/FirstPubOwnAtHead.lean); `nums_head_W` (AtFullSide/K12/RestTiesAtHeadW.lean), `reads_head_W`,
`facts_WFull` (Sim/FirstAnyAtHeadW.lean), `thin_of_reads` (Sim/ThinOfReads.lean); `planB_alike`'s proof
(K12/AsksAtHead.lean) for `planOB_alike`.

Limits.
- Public numbers alone: no run, no half, no thread. `PlanPlays` is one premise of `playsOn_k12`.
- The numbers 3, 7 and 0 are the places' field `free`: that `E.sent` is that number at a stand is a
  fact on the chain (`Made`, with the chain's counts), not said here.
- Conditional on the head. The full size alone.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanKernel
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.Own.PlanOwn
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.ThinOfReads
import AtFullSide.K12.RestTiesAtHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes (Codes)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf laidS)
open H2K.Member (piUFull piOFull piWFull)
open Johnson.Prover.Link (asked)
open ProofFile.Honest.K12 (TestJob PlanPlays planPlaysB planPlays_of_B bare bare_own tablesFitB newWideB
  sentBefore depthAt)
open ProofFile.Honest.K12.Own (planOB planOL renumP)
open ProofFile.Honest.K12.AtProof (fourOf placeO)
open ProofFile.Honest.K12.Light (thinOf pairOf pairs_of_planOk tablesFitB_eq tabB_congr asked_thin Alike
  nums_head_U thin_head_U planOk_head_U nums_head_O thin_head_O planOk_head_O omega_of_four
  nums_head_W reads_head_W facts_WFull thin_of_reads written_at_head laidS_alike take_decls
  drop_decls lettersOf_alike switchPubB_alike switchPlanB_alike stageAt_alike planFromOk_alike)

variable {W X W' X' : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 What the test reads of a place -/

theorem tablesFitB_bare {p q : P12} (hn : p.nums = q.nums) (hT : thinOf p = thinOf q) (own : Bool) :
    tablesFitB (bare p own) = tablesFitB (bare q own) := by
  rw [tablesFitB_eq, tablesFitB_eq, bare_own, bare_own]
  exact ProofFile.Honest.K12.Light.tabB_congr hn hT own

/-- `newWideB` reads of a job its stages and its word on the fresh table. -/
theorem newWideB_stages (J : TestJob W X) (J' : TestJob W' X')
    (hs : J.p.nums.stages = J'.p.nums.stages) (hf : J.fresh.isNone = J'.fresh.isNone)
    (decls : List Fmt.DeclaredRound) (sent : ℕ) : newWideB J decls sent = newWideB J' decls sent := by
  unfold newWideB sentBefore depthAt
  rw [hs, hf]

/-- **The test on the plan is one at two places with the same numbers and the same `thinOf`**, whose
blocks pass their test on the plan. -/
theorem planPlaysB_congr {p q : P12} (hn : p.nums = q.nums) (hT : thinOf p = thinOf q)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true) (own : Bool) (sent : ℕ) :
    planPlaysB p own sent = planPlaysB q own sent := by
  have hst : p.nums.stages = q.nums.stages := congrArg (·.stages) hn
  have hr : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds = (proximityTestKind guardedProximityTestParts q : Block T12 Unit).rounds := by
    refine Option.some.inj ?_
    rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts p hp,
      ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts q hq, hn]
  have ha : (laidOf p).map asked = (laidOf q).map asked := by
    rw [asked_thin, asked_thin, hT]
  have hw : ∀ decls, newWideB (bare p own) decls sent = newWideB (bare q own) decls sent :=
    fun decls => newWideB_stages _ _ hst (by rw [bare_own, bare_own]) decls sent
  unfold planPlaysB
  rw [hst]
  cases q.nums.stages with
  | nil => rfl
  | cons s rest => rw [hp, hq, ha, hr, tablesFitB_bare hn hT own, hw]

/-! ## 2 At the seated places -/

/-- **At the seated place of the test on G_u**, under the head. -/
theorem planPlaysB_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    planPlaysB (fourOf Np).U false 3 = true := by
  rw [planPlaysB_congr (nums_head_U h) (thin_head_U h) (ProofFile.Honest.K12.Light.planOk_head_U h)
    VerifiableInference.Desc.K12.Coin.At.closed_UFull.plan]
  exact plan_U

/-- **At the seated place of the test on G_omega**, under the head. -/
theorem planPlaysB_head_O (h : P5J.AtMg o Z D r Zp Np cF) {pO : P12}
    (hO : (fourOf Np).O = some pO) : planPlaysB pO true 7 = true := by
  rw [planPlaysB_congr (nums_head_O h hO) (thin_head_O h hO) (planOk_head_O h hO)
    VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan]
  exact plan_O

/-- **At the seated place of the last chain's test**, under the head. -/
theorem planPlaysB_head_W (h : P5J.AtMg o Z D r Zp Np cF) :
    planPlaysB (fourOf Np).W false 0 = true := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_W h
  rw [planPlaysB_congr (nums_head_W h)
    (thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_WFull.plan) h4 facts_WFull.plan]
  exact plan_W

/-- **`PlanPlays` at every job at the seated place of the test on G_u** whose fresh table has come
earlier. -/
theorem planPlays_head_U (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) : PlanPlays J s rest 3 :=
  planPlays_of_B J s rest hst 3 (by
    rw [hJ, hfr]
    exact planPlaysB_head_U h)

/-- **`PlanPlays` at every job at the seated place of the test on G_omega** whose first fold sends
its own table. -/
theorem planPlays_head_O (h : P5J.AtMg o Z D r Zp Np cF) {pO : P12}
    (hO : (fourOf Np).O = some pO) (J : TestJob W X) (hJ : J.p = pO)
    (hfr : J.fresh.isNone = true) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: rest) : PlanPlays J s rest 7 :=
  planPlays_of_B J s rest hst 7 (by
    rw [hJ, hfr]
    exact planPlaysB_head_O h hO)

/-- **`PlanPlays` at every job at the seated place of the last chain's test** whose fresh table has
come earlier. -/
theorem planPlays_head_W (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false) (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) : PlanPlays J s rest 0 :=
  planPlays_of_B J s rest hst 0 (by
    rw [hJ, hfr]
    exact planPlaysB_head_W h)

/-! ## 3 The plan's half at the test on G_omega -/

theorem idx_real_O : (realSized.all fun q =>
    decide (H2K.Sizes.nosOf q.1.shape.testOmega = piOFull.idx)) = true := by
  decide +kernel

/-- **Under the head the code numbers of the seated place of the test on G_omega are the written
ones.** -/
theorem idx_head_O (h : P5J.AtMg o Z D r Zp Np cF) {pO : P12} (hO : (fourOf Np).O = some pO) :
    pO.idx = piOFull.idx := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have hk := planOk_head_O h hO
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  have e1 := H2K.Sizes.idx_of_planOk _ nO hk
  have e2 := (H2K.Sizes.places_idx Zp.made Np h.laid.places).2.2.1 nO h1
  have e3 : Zp.made.p.chains.made.sized.proof.batch.shape = x.shape := Wr.shape
  have k := idx_real_O
  rw [hx] at k
  simp only [Option.all_some, decide_eq_true_eq] at k
  refine e1.trans (e2.trans ?_)
  rw [e3]
  exact k

/-- **Under the head the seated place of the test on G_omega and the written one are alike.** -/
theorem alike_head_O (h : P5J.AtMg o Z D r Zp Np cF) {pO : P12} (hO : (fourOf Np).O = some pO) :
    Alike pO piOFull where
  nums := nums_head_O h hO
  idx := idx_head_O h hO
  early := (H2K.JointK.early_of_planOk _ (planOk_head_O h hO)).trans (by decide)
  answers := (H2K.JointK.answers_of_planOk _ (planOk_head_O h hO)).trans (by decide)
  decls := by rw [ProofFile.Honest.K12.Light.decls_thin, ProofFile.Honest.K12.Light.decls_thin, thin_head_O h hO]

/-- Two places with the same numbers whose blocks pass declare as many lists of oracle messages. -/
theorem oracles_length {p q : P12} (hn : p.nums = q.nums)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true) :
    p.oracles.length = q.oracles.length := by
  have e : p.oracles.map (·.map pairOf) = q.oracles.map (·.map pairOf) := by
    refine Option.some.inj ?_
    rw [← pairs_of_planOk guardedProximityTestParts p hp, ← pairs_of_planOk guardedProximityTestParts q hq, hn]
  simpa only [List.length_map] using congrArg List.length e

/-- The first halves of a list zipped with two lists of one length are one. -/
theorem map_fst_zip_length {α β γ : Type} : ∀ (l : List α) (m : List β) (m' : List γ),
    m.length = m'.length → (l.zip m).map (·.1) = (l.zip m').map (·.1)
  | [], _, _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | a :: l, b :: m, c :: m', h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_fst_zip_length l m m' (by simpa using h)]

/-- **Two alike places with as many lists of oracle messages stay alike when renumbered.** -/
theorem alike_renum {p q : P12} (A : Alike p q) (ho : p.oracles.length = q.oracles.length) :
    Alike (renumP p) (renumP q) where
  nums := by
    show ProofFile.Honest.K12.Own.renum p.nums = ProofFile.Honest.K12.Own.renum q.nums
    rw [A.nums]
  idx := A.idx
  early := A.early
  answers := A.answers
  decls := by
    show (((H2U.roundsOfNums (ProofFile.Honest.K12.Own.renum p.nums)).getD []).zip p.oracles).map (·.1) =
      (((H2U.roundsOfNums (ProofFile.Honest.K12.Own.renum q.nums)).getD []).zip q.oracles).map (·.1)
    rw [A.nums]
    exact map_fst_zip_length _ _ _ ho

/-- **`planOB` reads no more**: the text of `planB_alike`, at the renumbered place beside. -/
theorem planOB_alike {p q : P12} (A : Alike p q) (ho : p.oracles.length = q.oracles.length)
    (K : Codes) (nT : ℕ) : planOB p K nT = planOB q K nT := by
  have hS := laidS_alike A
  have r1 : ∀ (u : P12) (a : Fmt.M1.Stage),
      (VerifiableInference.Desc.K12.foldAt guardedProximityTestParts u 0 a (laidS u) : Block T12 Unit).rounds =
        ((laidS u).take (1 + a.k)).map (·.1) := fun _ _ => rfl
  have r2 : ∀ (u : P12) (a next : Fmt.M1.Stage) (last : Bool),
      (VerifiableInference.Desc.K12.switchAt guardedProximityTestParts u 0 a next last (laidS u) :
        Block T12 Unit).rounds = (((laidS u).drop (1 + a.k)).take 2).map (·.1) :=
    fun _ _ _ _ => rfl
  have r3 : ∀ u : P12, (VerifiableInference.Desc.K12.batAt guardedProximityTestParts u (laidOf u) :
      Block T12 Unit).rounds = ((laidOf u).take 1).map (·.1) := fun _ => rfl
  have s1 : ∀ n, (((laidS p).drop n).map asked) = (((laidS q).drop n).map asked) := fun n => by
    have e : ∀ u : VerifiableInference.Desc.K12.Laid, u.map asked =
        (u.map (·.1)).map fun d => d.items.filter (· != .root) := fun u => by
      rw [List.map_map]
      rfl
    rw [e, e, drop_decls hS]
  unfold planOB planOL VerifiableInference.Desc.Block.openings
  simp only [A.nums, lettersOf_alike A, switchPubB_alike A, switchPlanB_alike A, stageAt_alike A,
    r1, r2, r3, take_decls hS, take_decls A.decls, take_decls (drop_decls hS _), s1,
    planFromOk_alike (alike_renum A ho) K _ _ _ _ _ (drop_decls hS _)]

/-- **The plan's half at the seated place of the test on G_omega, at three trees**, under the head. -/
theorem planOB_head_O (h : P5J.AtMg o Z D r Zp Np cF) {pO : P12} (hO : (fourOf Np).O = some pO) :
    planOB pO H2K.Member.codesFull 3 = true := by
  rw [planOB_alike (alike_head_O h hO) (oracles_length (nums_head_O h hO) (planOk_head_O h hO)
    VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan)]
  exact ProofFile.Honest.K12.Own.planOB_O_full

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.planPlaysB_congr
#print axioms ProofFile.Honest.K12.AtFile.planPlays_head_U
#print axioms ProofFile.Honest.K12.AtFile.planPlays_head_O
#print axioms ProofFile.Honest.K12.AtFile.planPlays_head_W
#print axioms ProofFile.Honest.K12.AtFile.alike_head_O
#print axioms ProofFile.Honest.K12.AtFile.planOB_head_O
