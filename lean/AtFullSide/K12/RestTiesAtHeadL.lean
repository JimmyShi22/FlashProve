-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/RestTiesAtHeadL.lean: UNDER THE HEAD, AT THE FIRST CHAIN's PROXIMITY TEST: the seated
place and the library's written place `piLFull` (Johnson/Desc/K12/Law/PlacesFull.lean) are alike
(`Alike`, Johnson/Desc/ProofFile/Honest/K12/FrontAtHead.lean); so the plan's half `planB`
(Johnson/Desc/ProofFile/Honest/K12/PlanB.lean) says yes at the seated place; so `PubTiesT`
(Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExact.lean), the public premise of the frame's sentence
at the test's second member, holds there with no named premise. Statements and proofs; no
definition.

  `nums_head_L`   all seven numbers of the seated place are the written place's
  `idx_head_L`, `alike_head_L`   the code numbers; the two places are alike
  `planB_head_L`   the plan's half at the seated place, at one first tree
  `pubTiesT_at_head_L`   `pubTiesT_head_L` (RestTiesAtWL.lean in this folder) without its premise

By what. The seven numbers: the stages, `ownMask` and the declared rounds: `reads_head_L`
(FirstAnyAtHeadL.lean in this folder); the rows: `rows_of_rounds`; the work: `place_L_of_full`; the
first trees: `first_reads`, `rdsAt_reads`; the number of trees in front, 77: `stretch_at_L`; the
number of the chain's first tree, 0: `places_firstTree`; `nums_ext` (Johnson/Desc/K12/Law/,
Johnson/Desc/K12/Law/Sizes/, Johnson/Loose/H2K12/CondAtLast.lean). The code numbers:
`idxFull_of_configure`, `idx_L_of_full`, `idx_of_planOk`
(Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean) at `pub_configure`
(Johnson/Desc/ProofFile/Law/PlainMade.lean). That the last test's stages are the typed list:
`stages_of_pubPlain` at `layoutGroupsAre` (AtFullSide/LayoutRead/GroupsPaid.lean), as `reads_head_L`
spends it. `planB_alike` (AsksAtHead.lean) over `planB_L_full` (RestTiesAtWL.lean).

Limits.
- A PUBLIC PREMISE THAT IS MET IS NOT A SENTENCE WITH CONTENT. At this test the condition `onFreeT`
  asks `stPlainB` of the job's state on entry, which has been evaluated false at the verifier's
  state at one honest run (Johnson/Desc/ProofFile/Honest/K12/AtProof/LotL.lean's first limit).
  `exact_free_trees_dense` (Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExactDense.lean) takes the
  same `PubTiesT`: it is that sentence which this premise could serve. Its condition `onFreeTD` has
  no member shown in these files at this place.
- `OpenTies`, the sentence's other public premise, is not treated; nor which table of codes the
  state on entry bears at this place.
- hfr: the job's fresh table has come earlier. That the lot's job at this place says so at the full
  size is not shown here.
- This place alone.
- The head has members at the goals' two named sets of files, at the concrete earlier hash
  (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); no theorem here lays this file's
  statements at them.
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.RestTiesAtWL
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.K12.Law.Sizes.IdxAtScope
import Johnson.Desc.K12.Law.Sizes.ClosedAtScope
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12 guardedProximityTestParts)
open H2K.Member (piLFull codesFull)
open H2K.JointK (descN pL)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head all seven numbers of the seated place of the first chain's test are the written
place's.** -/
theorem nums_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).L.nums = piLFull.nums := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_L h
  obtain ⟨Z', N', c', _, hZ', hN', e, _, pre, l, J₀, hb, _, hJ₀⟩ :=
    H2K.JointK.k12_sits o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  have hpin : VerifiableInference.PlanWritten.seatPinnedProof Z.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := by
    rw [← e]
    exact LPFD.asks_written h.laid.asks
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope hpin).1
  have hL := H2K.JointK.stages_of_pubPlain Johnson.AtFull.LayoutRead.layoutGroupsAre h.scope
    h.laid.pub
  have nL : (pL N').nums = N'.L.nums := H2K.Made.nums_of_planOk _ N'.L h4
  have S := H2K.JointK.stretch_at_L o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
    h.laid.places hp A hL hW ProofFile.sameReply pre l J₀ hb hJ₀
  exact H2K.Sizes.nums_ext (H2K.JointK.rows_of_rounds h3 H2K.Member.rounds_LFull)
    ((congrArg (·.work) nL).trans (H2K.Sizes.place_L_of_full A h.laid.places hL).2.1) h1 h2
    (H2K.Sizes.first_reads h4 facts_LFull.plan h1 h2
      (H2K.Sizes.rdsAt_reads h4 facts_LFull.plan h3))
    ((congrArg (·.free) nL).trans S.2.2.2)
    ((congrArg (·.firstTree) nL).trans (H2K.Made.places_firstTree Z'.made N' h.laid.places).1)

/-- **Under the head the code numbers of that seated place are the written ones.** -/
theorem idx_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).L.idx = piLFull.idx := by
  have e1 : (fourOf Np).L.idx = Np.L.idx :=
    H2K.Sizes.idx_of_planOk _ _ (reads_head_L h).2.2.2
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  have hL := H2K.JointK.stages_of_pubPlain Johnson.AtFull.LayoutRead.layoutGroupsAre h.scope
    h.laid.pub
  obtain ⟨_, _, hc, _, _⟩ := ProofFile.Law.pub_configure h.laid.pub
  exact e1.trans (H2K.Sizes.idx_L_of_full (H2K.Sizes.idxFull_of_configure A hL hc) h.laid.places)

/-- **Under the head the seated place and the written one are alike.** -/
theorem alike_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) : Alike (fourOf Np).L piLFull where
  nums := nums_head_L h
  idx := idx_head_L h
  early := (H2K.JointK.early_of_planOk _ (reads_head_L h).2.2.2).trans (by decide)
  answers := (H2K.JointK.answers_of_planOk _ (reads_head_L h).2.2.2).trans (by decide)
  decls := by
    obtain ⟨h1, h2, h3, h4⟩ := reads_head_L h
    rw [decls_thin, decls_thin, thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_LFull.plan]

/-- **Under the head the plan's half holds at the seated place, at one first tree.** -/
theorem planB_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    planB (fourOf Np).L codesFull 1 = true := by
  rw [planB_alike (alike_head_L h)]
  exact planB_L_full

/-- **`PubTiesT` under the head, at every job at the place whose fresh table has come earlier.** -/
theorem pubTiesT_at_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).L) (ho : Js.own = false) : PubTiesT J Js codesFull 1 :=
  pubTiesT_head_L h J Js hJ hfr hs ho (planB_head_L h)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.nums_head_L
#print axioms ProofFile.Honest.K12.Light.idx_head_L
#print axioms ProofFile.Honest.K12.Light.alike_head_L
#print axioms ProofFile.Honest.K12.Light.planB_head_L
#print axioms ProofFile.Honest.K12.Light.pubTiesT_at_head_L
