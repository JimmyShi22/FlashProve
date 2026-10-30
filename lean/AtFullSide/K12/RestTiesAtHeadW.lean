-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/RestTiesAtHeadW.lean: UNDER THE HEAD, AT THE REQUEST's OWN PROXIMITY TEST ON THE LAST
CHAIN: the seated place and the library's written place `piWFull`
(Johnson/Desc/K12/Law/PlacesFull.lean) are alike (`Alike`,
Johnson/Desc/ProofFile/Honest/K12/FrontAtHead.lean); so the plan's half `planB`
(Johnson/Desc/ProofFile/Honest/K12/PlanB.lean) says yes at the seated place; so `PubTiesT`
(Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExact.lean), the public premise of the frame's sentence
at the test's second member, holds there with no named premise. Statements and proofs; no
definition.

  `idx_real_W`   a closed fact, by an evaluation in Lean's kernel: at the real sizes the code
                 numbers of the request's own test are the written place's
  `nums_head_W`   all seven numbers of the seated place are the written place's
  `idx_head_W`, `alike_head_W`   the code numbers; the two places are alike
  `planB_head_W`   the plan's half at the seated place, at three first trees
  `pubTiesT_at_head_W`   `pubTiesT_head_W` (RestTiesAtWL.lean in this folder) without its premise

By what. The seven numbers: `more_W_of_full`, `place_W_of_full`, `first_W_of_full`, `nums_ext`
(Johnson/Desc/K12/Law/Sizes/); `free_at_seat_W`, `rounds_at_seat_W`, `plan_at_seat_W`
(Johnson/Loose/H2K12/); the seventh, the number of the chain's first tree: `firstTree_W`
(Johnson/Desc/K12/Law/FirstTreeOfMade.lean: the first chain's trees sent, and one), `pub_configure`
(Johnson/Desc/ProofFile/Law/PlainMade.lean), `pub_decl_at_laid`
(Johnson/Desc/ProofFile/Honest/K14/WrittenAtHead.lean: the public part's declared rounds are the
written ones) and `roots_first` (Johnson/AtFull/ProofRows/WrittenProof.lean: 83). The code numbers:
as `idx_head_U` (FrontAtHead.lean). `planB_alike` (AsksAtHead.lean) over `planB_W_full`
(Sim/TreesPlanAt.lean).

Over what it stands. A file of the kind K14's authors that is not in the library yet
(Johnson/Desc/ProofFile/Honest/K14/WrittenAtHead.lean, with WrittenBack.lean beneath it).

Limits.
- A PUBLIC PREMISE THAT IS MET IS NOT A SENTENCE WITH CONTENT: the sentence's condition `onFreeT`
  has no known member at a description of a file (at a small made-up file, under two premises on the
  run: Johnson/Desc/ProofFile/Honest/K12/Sim/RestMeetsSmall.lean).
- `OpenTies`, the sentence's other public premise, is not treated; nor which table of codes the
  state on entry bears at this place.
- This place alone. The head has members at the goals' two named sets of files, at the concrete
  earlier hash (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); no theorem here lays this
  file's statements at them.
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.RestTiesAtWL
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.K12.Law.FirstTreeOfMade
import Johnson.AtFull.ProofRows.WrittenProof
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 guardedProximityTestParts)
open H2K.Member (piWFull codesFull)
open H2K.JointK (descN pOwn)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem idx_real_W : (realSized.all fun q =>
    decide (H2K.Sizes.nosOf q.1.shape.testOwn = piWFull.idx)) = true := by
  decide +kernel

/-- **Under the head all seven numbers of the seated place of the request's own test are the written
place's.** -/
theorem nums_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).W.nums = piWFull.nums := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
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
  have nW : (pOwn N').nums = N'.W.nums := (R.nums hp).2.2.2
  have hD : Johnson.G.OfPlan.declPOf Z'.made = .ok Z'.D := by
    obtain ⟨_, _, _, _, q⟩ := ProofFile.Law.pub_configure h.laid.pub
    exact q
  have hft : N'.W.nums.firstTree = piWFull.nums.firstTree := by
    rw [H2K.Made.firstTree_W Z'.made N' Z'.D h.laid.places hD,
      ProofFile.Honest.K14.pub_decl_at_laid h.scope h.laid]
    show Johnson.G.OfPlan.rootsOf Johnson.AtFull.ProofRows.declProofFull.1 + 1 = 84
    rw [Johnson.AtFull.ProofRows.roots_first]
  refine nW.trans (H2K.Sizes.nums_ext (H2K.Sizes.more_W_of_full A h.laid.places).1
    (H2K.Sizes.place_W_of_full A h.laid.places).2.1 (H2K.Sizes.place_W_of_full A h.laid.places).1
    (H2K.Sizes.more_W_of_full A h.laid.places).2.1
    (H2K.Sizes.first_W_of_full A h.laid.places _
      (H2K.JointK.plan_at_seat_W o Z' ProofFile.pureRoad.links N' c' hp)
      (H2K.JointK.rounds_at_seat_W o Z' ProofFile.pureRoad.links N' c' h.laid.places hp A hW))
    (H2K.JointK.free_at_seat_W o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
      h.laid.places hp) hft)

/-- **Under the head the code numbers of that seated place are the written ones.** -/
theorem idx_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).W.idx = piWFull.idx := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have e1 : (fourOf Np).W.idx = Np.W.idx :=
    H2K.Sizes.idx_of_planOk _ _ (reads_head_W h).2.2.2
  have e2 := (H2K.Sizes.places_idx Zp.made Np h.laid.places).2.2.2
  have e3 : Zp.made.p.chains.made.sized.proof.batch.shape = x.shape := Wr.shape
  have k := idx_real_W
  rw [hx] at k
  simp only [Option.all_some, decide_eq_true_eq] at k
  rw [e1, e2, e3]
  exact k

/-- **Under the head the seated place and the written one are alike.** -/
theorem alike_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) : Alike (fourOf Np).W piWFull where
  nums := nums_head_W h
  idx := idx_head_W h
  early := (H2K.JointK.early_of_planOk _ (reads_head_W h).2.2.2).trans (by decide)
  answers := (H2K.JointK.answers_of_planOk _ (reads_head_W h).2.2.2).trans (by decide)
  decls := by
    obtain ⟨h1, h2, h3, h4⟩ := reads_head_W h
    rw [decls_thin, decls_thin, thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_WFull.plan]

/-- **Under the head the plan's half holds at the seated place, at three first trees.** -/
theorem planB_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    planB (fourOf Np).W codesFull 3 = true := by
  rw [planB_alike (alike_head_W h)]
  exact planB_W_full

/-- **`PubTiesT` under the head, at every job at the place whose fresh table has come earlier.** -/
theorem pubTiesT_at_head_W (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X Pb : Type} (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false) : PubTiesT J Js codesFull 3 :=
  pubTiesT_head_W h J Js hJ hfr hs ho (planB_head_W h)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.idx_real_W
#print axioms ProofFile.Honest.K12.Light.nums_head_W
#print axioms ProofFile.Honest.K12.Light.idx_head_W
#print axioms ProofFile.Honest.K12.Light.alike_head_W
#print axioms ProofFile.Honest.K12.Light.planB_head_W
#print axioms ProofFile.Honest.K12.Light.pubTiesT_at_head_W
