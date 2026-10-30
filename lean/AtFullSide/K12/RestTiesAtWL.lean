-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/RestTiesAtWL.lean: `PubTiesT`
(Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExact.lean), the public premise of the frame's sentence
at a proximity test's second member (`exact_free_trees`, same file), HELD AGAINST TWO PLACES OF THE
PROOF FILE: the request's own test on the last chain and the first chain's test. Statements and
proofs; no definition.

What comes out. At the library's written places (`piWFull`, `piLFull`,
Johnson/Desc/K12/Law/PlacesFull.lean) all eight clauses hold, at every job whose fresh table has
come earlier. Under the head seven of the eight hold at the seated places; the eighth, the plan's
half `planB` (Johnson/Desc/ProofFile/Honest/K12/PlanB.lean), is a named premise there.

  `planB_L_full`, `planNo_L_two`, `reachT_L_full`, `restLen_WFull`, `restLen_LFull`   closed facts:
                 four by an evaluation in Lean's kernel (at two of them the limit maxRecDepth is
                 raised to 100000), the third by a law over one; the second: the number of trees is
                 read
  `pubTiesT_WFull`, `pubTiesT_LFull`   at the written places: three first trees; one
  `reachTB_reads`   `reachTB` reads the stages, `ownMask` and the declared rounds alone
  `pubTiesT_head_W`, `pubTiesT_head_L`   under the head

By what. At the written places: `reachT_W_full`, `reachTB_of_reachB` (Sim/TreesReach.lean),
`reach_L_full` (Sim/ReachAt.lean), `planB_W_full` (Sim/TreesPlanAt.lean), `facts_WFull`
(Sim/FirstAnyAtHeadW.lean), `facts_LFull` (AtFullSide/K12/FirstAnyAtHeadL.lean). Under the head:
`reads_head_W`, `facts_head_W`, `reads_head_L`, `facts_head_L` (same two files); `thin_of_reads`
(Sim/ThinOfReads.lean); `decls_thin`, `tablesFitB_eq` (Sim/FirstPubAtHead.lean).

Limits.
- `pubTiesT_head_L` MAY BE EMPTY AT THE VERY PLACE: under the head `planB` at the seated place is a
  premise, and whether it says yes there is not shown here; at the written place it does. At the
  request's own test the premise is paid: `planB_head_W` (RestTiesAtHeadW.lean in this folder).
  `planB_alike` (AsksAtHead.lean) carries `planB` over from `Alike` (FrontAtHead.lean), which asks
  all seven numbers, the code numbers, `early`, `answers` and the declared rounds; under the head
  the two files named above have the stages, `ownMask`, the declared rounds and the block's own
  test.
- A PUBLIC PREMISE THAT CAN BE MET IS NOT A SENTENCE WITH CONTENT: the sentence's condition
  `onFreeT` has no known member at a description of a file (at a small made-up file, under two
  premises on the run: Johnson/Desc/ProofFile/Honest/K12/Sim/RestMeetsSmall.lean). At the first
  chain's test it asks `stPlainB` of the job's state on entry, which has been evaluated false at the
  verifier's state at one honest run (Johnson/Desc/ProofFile/Honest/K12/AtProof/LotL.lean's first
  limit).
- `exact_free_trees_dense` (Sim/TreesExactDense.lean) takes the same `PubTiesT`: at the first
  chain's test it is that sentence which these clauses could serve.
- `OpenTies`, the sentence's other public premise, is not treated. Which table of codes the state on
  entry bears at these places (the condition asks that it be the K of `PubTiesT`) is not treated.
- The written places are closed terms that a program made off the print of a run
  (Sim/TreesPlanAt.lean's own limit).
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.FirstAnyAtHeadL
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlanAt
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12 guardedProximityTestParts)
open H2K.Member (piWFull piLFull codesFull)
open H2K.JointK (laidOf)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 At the written places, by an evaluation in Lean's kernel -/

set_option maxRecDepth 100000 in
theorem planB_L_full : planB piLFull codesFull 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The number of trees is read. -/
theorem planNo_L_two : planNo piLFull codesFull 2 = ["oS"] := by decide +kernel

theorem reachT_L_full : reachTB piLFull = true := reachTB_of_reachB _ reach_L_full

theorem restLen_WFull : restLen piWFull.nums.stages =
    2 + lenFrom (stN piWFull) (piWFull.nums.stages.drop 2) := by decide +kernel

theorem restLen_LFull : restLen piLFull.nums.stages =
    2 + lenFrom (stN piLFull) (piLFull.nums.stages.drop 2) := by decide +kernel

/-- **`PubTiesT` at every job at the written place of the request's own test** whose fresh table has
come earlier: at three first trees. -/
theorem pubTiesT_WFull {W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = piWFull)
    (hfr : J.fresh.isNone = false) (hs : Js.p = piWFull) (ho : Js.own = false) :
    PubTiesT J Js codesFull 3 := by
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact reachT_W_full
  · rw [hJ]
    exact planB_W_full
  · rw [hJ]
    exact facts_WFull.form
  · rw [hJ]
    exact facts_WFull.count
  · rw [hJ]
    exact restLen_WFull
  · rw [tablesFitB_eq, hfr, hJ]
    exact facts_WFull.tab

/-- **The same at the written place of the first chain's test**: at one first tree. -/
theorem pubTiesT_LFull {W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = piLFull)
    (hfr : J.fresh.isNone = false) (hs : Js.p = piLFull) (ho : Js.own = false) :
    PubTiesT J Js codesFull 1 := by
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact reachT_L_full
  · rw [hJ]
    exact planB_L_full
  · rw [hJ]
    exact facts_LFull.form
  · rw [hJ]
    exact facts_LFull.count
  · rw [hJ]
    exact restLen_LFull
  · rw [tablesFitB_eq, hfr, hJ]
    exact facts_LFull.tab

/-! ## 2 Under the head: all clauses but `plan` -/

/-- What `reachTB` reads of a place. -/
theorem reachTB_reads {p q : P12} (h1 : p.nums.stages = q.nums.stages)
    (h2 : p.nums.ownMask = q.nums.ownMask)
    (h3 : (laidOf p).map (·.1) = (laidOf q).map (·.1)) : reachTB p = reachTB q := by
  have e : ∀ (r : P12) (i : ℕ),
      declared r i = ((((laidOf r).map (·.1))[i]?).map (·.entry.poss)).getD 0 := fun r i => by
    unfold declared
    rw [List.getElem?_map, Option.map_map]
    rfl
  have ed : declared p = declared q := funext fun i => by rw [e p, e q, h3]
  unfold reachTB reachTL
  rw [h1, h2, ed]

/-- hplan: the plan's half at the seated place: a named premise. -/
theorem pubTiesT_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (hplan : planB (fourOf Np).W codesFull 3 = true) : PubTiesT J Js codesFull 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_W h
  have T := thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_WFull.plan
  have F := facts_head_W h
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, reachTB_reads h1 h2 (by rw [decls_thin, decls_thin, T])]
    exact reachT_W_full
  · rw [hJ]
    exact hplan
  · rw [hJ]
    exact F.form
  · rw [hJ]
    exact F.count
  · rw [hJ]
    show restLen (fourOf Np).W.nums.stages =
      2 + lenFrom ((fourOf Np).W.nums.stages.getD 1 default) ((fourOf Np).W.nums.stages.drop 2)
    rw [h1]
    exact restLen_WFull
  · rw [tablesFitB_eq, hfr, hJ]
    exact F.tab

theorem pubTiesT_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (hplan : planB (fourOf Np).L codesFull 1 = true) : PubTiesT J Js codesFull 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_L h
  have T := thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_LFull.plan
  have F := facts_head_L h
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, reachTB_reads h1 h2 (by rw [decls_thin, decls_thin, T])]
    exact reachT_L_full
  · rw [hJ]
    exact hplan
  · rw [hJ]
    exact F.form
  · rw [hJ]
    exact F.count
  · rw [hJ]
    show restLen (fourOf Np).L.nums.stages =
      2 + lenFrom ((fourOf Np).L.nums.stages.getD 1 default) ((fourOf Np).L.nums.stages.drop 2)
    rw [h1]
    exact restLen_LFull
  · rw [tablesFitB_eq, hfr, hJ]
    exact F.tab

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.planB_L_full
#print axioms ProofFile.Honest.K12.Light.planNo_L_two
#print axioms ProofFile.Honest.K12.Light.reachT_L_full
#print axioms ProofFile.Honest.K12.Light.restLen_WFull
#print axioms ProofFile.Honest.K12.Light.restLen_LFull
#print axioms ProofFile.Honest.K12.Light.pubTiesT_WFull
#print axioms ProofFile.Honest.K12.Light.pubTiesT_LFull
#print axioms ProofFile.Honest.K12.Light.reachTB_reads
#print axioms ProofFile.Honest.K12.Light.pubTiesT_head_W
#print axioms ProofFile.Honest.K12.Light.pubTiesT_head_L
