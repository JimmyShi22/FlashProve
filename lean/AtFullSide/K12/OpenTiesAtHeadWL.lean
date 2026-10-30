-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/OpenTiesAtHeadWL.lean: UNDER THE HEAD, AT THE REQUEST's OWN PROXIMITY TEST ON THE
LAST CHAIN AND AT THE FIRST CHAIN's: `OpenTies`
(Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExact.lean), the second public premise of the frame's
sentence at the test's second member; with `PubTiesT` (RestTiesAtHeadW.lean, RestTiesAtHeadL.lean in
this folder) both public premises in one statement; and so the sentence `exact_free_trees_dense`
(Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExactDense.lean) at the seated places. Statements and
proofs; no definition.

  `opens_WFull`, `opens_LFull`   closed facts, by an evaluation in Lean's kernel: at the written
                 place the second part's round number 1 is declared to open the place's own list of
                 first trees
  `first_head_W`, `first_head_L`   that list at the seated place: three trees taken over from the
                 two chains in front; one tree of the chain's own
  `openTies_head_W`, `openTies_head_L`   `OpenTies`
  `public_head_W`, `public_head_L`   both public premises
  `exact_rest_dense_head_W`, `exact_rest_dense_head_L`   the sentence
  `exact_rest_head_W`   at the request's own test also `exact_free_trees`, under the condition
                 `onFreeT`

By what. As `openTies_head_U` (Johnson/Desc/ProofFile/Honest/K12/Sim/RestTiesAtHeadU.lean), over
`alike_head_W`, `nums_head_W`, `alike_head_L`, `nums_head_L`.

Limits.
- THE SENTENCES ARE CONDITIONAL: `onFreeTD` and `onFreeT` stand in front of the arrow. These files
  show no member of either at a state of a run of the proof file's description at these two places:
  an instance, no member; it counts nothing.
- `onFreeT` asks the mark `stPlainB` of the job's state on entry. At the first chain's test that
  mark has been evaluated false at the verifier's state at one honest run
  (Johnson/Desc/ProofFile/Honest/K12/AtProof/LotL.lean's first limit): so no such sentence is laid
  there. At the request's own test it has not been evaluated, that we know.
- The side σ, the chain's number and the number of the first tree are letters: no side is seated
  here.
- hop IS A PREMISE ON THE SIMULATORS' JOB: that it names the place's first trees. No simulators' job
  is laid at these places here.
- GENERAL IN THE JOB's STATE ON ENTRY `rec₀`: neither public premise reads it. Which state on entry
  a job of record bears at these places, and whether the condition can hold at it, is not treated.
- Which table of codes the state on entry bears (the condition asks that it be `codesFull`) is not
  treated.
- The second member alone: nothing here joins the two members' sentences. The bound is `budOpened`.
- The head has members at the goals' two named sets of files, at the concrete earlier hash
  (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); no theorem here lays this file's
  statements at them.
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.RestTiesAtHeadW
import AtFullSide.K12.RestTiesAtHeadL
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExactDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open H2K.Member (piWFull piLFull codesFull)
open H2K.JointK (laidOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 At the written places -/

theorem opens_WFull :
    ((((laidOf piWFull).map (·.1)).drop (firstLen piWFull.nums.stages))[1]?).map (·.opens) =
      some piWFull.nums.first := by decide +kernel

theorem opens_LFull :
    ((((laidOf piLFull).map (·.1)).drop (firstLen piLFull.nums.stages))[1]?).map (·.opens) =
      some piLFull.nums.first := by decide +kernel

/-! ## 2 The request's own test -/

/-- **Under the head: the first trees of the seated place.** -/
theorem first_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    (fourOf Np).W.nums.first =
      [(⟨13, 3, false, 1⟩, .taken 0 1), (⟨22, 12, false, 82⟩, .taken 0 82),
        (⟨22, 36, false, 1⟩, .taken 1 1)] := by
  rw [nums_head_W h]
  rfl

/-- **`OpenTies` under the head, at the place's own list of first trees.** hop: the simulators' job
names these trees, each at its declared depth: a premise on a letter of Js. -/
theorem openTies_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).W) (chain : ℕ)
    (hop : Js.opens = (fourOf Np).W.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain (fourOf Np).W.nums.first := by
  refine ⟨?_, hop⟩
  have e : ((((laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some (fourOf Np).W.nums.first := by
    rw [hJ, (alike_head_W h).decls, nums_head_W h]
    exact opens_WFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **Both public premises of the second member's sentence, under the head,
at the request's own test.** General in the job's state on entry: neither premise reads it. -/
theorem public_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (chain : ℕ) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).W.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    PubTiesT J Js codesFull (fourOf Np).W.nums.first.length ∧
      OpenTies J Js chain (fourOf Np).W.nums.first := by
  refine ⟨?_, openTies_head_W h J Js hJ chain hop⟩
  rw [first_head_W h]
  exact pubTiesT_at_head_W h J Js hJ hfr hs ho

/-- **The dense sentence at the second member, under the head, at the request's own test**: at every
face, side and number of the first tree. Its condition `onFreeTD` stands in front of the arrow. -/
theorem exact_rest_dense_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {S Cl V W X Pb : Type}
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).W.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree
      (onFreeTD φ J Js codesFull chain (fourOf Np).W.nums.first) (budOpened J.p.nums.stages)
      (restMember J Js) :=
  exact_free_trees_dense φ σ J Js codesFull chain firstTree _
    (public_head_W h J Js chain hJ hfr hs ho hop).1
    (public_head_W h J Js chain hJ hfr hs ho hop).2

/-- **The sentence under the condition `onFreeT`, at the same place.** -/
theorem exact_rest_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {S Cl V W X Pb : Type}
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).W.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree
      (onFreeT φ J Js codesFull chain (fourOf Np).W.nums.first) (budOpened J.p.nums.stages)
      (restMember J Js) :=
  exact_free_trees φ σ J Js codesFull chain firstTree _
    (public_head_W h J Js chain hJ hfr hs ho hop).1
    (public_head_W h J Js chain hJ hfr hs ho hop).2

/-! ## 3 The first chain's test -/

/-- **Under the head: the first trees of the seated place.** -/
theorem first_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    (fourOf Np).L.nums.first =
      [(⟨23, 9, false, 76⟩, .own 76)] := by
  rw [nums_head_L h]
  rfl

/-- **`OpenTies` under the head, at the place's own list of first trees.** hop: the simulators' job
names these trees, each at its declared depth: a premise on a letter of Js. -/
theorem openTies_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).L) (chain : ℕ)
    (hop : Js.opens = (fourOf Np).L.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain (fourOf Np).L.nums.first := by
  refine ⟨?_, hop⟩
  have e : ((((laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some (fourOf Np).L.nums.first := by
    rw [hJ, (alike_head_L h).decls, nums_head_L h]
    exact opens_LFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **Both public premises of the second member's sentence, under the head,
at the first chain's test.** General in the job's state on entry: neither premise reads it. -/
theorem public_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (chain : ℕ) (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).L.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    PubTiesT J Js codesFull (fourOf Np).L.nums.first.length ∧
      OpenTies J Js chain (fourOf Np).L.nums.first := by
  refine ⟨?_, openTies_head_L h J Js hJ chain hop⟩
  rw [first_head_L h]
  exact pubTiesT_at_head_L h J Js hJ hfr hs ho

/-- **The dense sentence at the second member, under the head, at the first chain's test**: at every
face, side and number of the first tree. Its condition `onFreeTD` stands in front of the arrow. -/
theorem exact_rest_dense_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {S Cl V W X Pb : Type}
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).L.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree
      (onFreeTD φ J Js codesFull chain (fourOf Np).L.nums.first) (budOpened J.p.nums.stages)
      (restMember J Js) :=
  exact_free_trees_dense φ σ J Js codesFull chain firstTree _
    (public_head_L h J Js chain hJ hfr hs ho hop).1
    (public_head_L h J Js chain hJ hfr hs ho hop).2

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.opens_WFull
#print axioms ProofFile.Honest.K12.Light.opens_LFull
#print axioms ProofFile.Honest.K12.Light.first_head_W
#print axioms ProofFile.Honest.K12.Light.openTies_head_W
#print axioms ProofFile.Honest.K12.Light.public_head_W
#print axioms ProofFile.Honest.K12.Light.exact_rest_dense_head_W
#print axioms ProofFile.Honest.K12.Light.exact_rest_head_W
#print axioms ProofFile.Honest.K12.Light.first_head_L
#print axioms ProofFile.Honest.K12.Light.openTies_head_L
#print axioms ProofFile.Honest.K12.Light.public_head_L
#print axioms ProofFile.Honest.K12.Light.exact_rest_dense_head_L
