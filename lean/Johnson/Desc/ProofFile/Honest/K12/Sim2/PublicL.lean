-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of the slot at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/PublicL.lean: UNDER THE HEAD, AT THE FIRST CHAIN's LAST PROXIMITY TEST: the seated
place and the library's written place `piLFull` are alike (`Alike`, Honest/K12/FrontAtHead.lean), so the plan's half
`planB` says yes at the seated place; and `OpenTies`, at the one tree that the test's first switch opens, for the simulators'
job `simulatorJobAtFirstChainTest`. These pay two premises of `slot_firstChainTest` (Sim2/SlotL.lean). Twins of `alike_head_W`, `planB_head_W`
(AtFullSide/K12/RestTiesAtHeadW.lean) and `openTies_head_U` (Honest/K12/Sim/RestTiesAtHeadU.lean). Statements and proofs.

  `nos_proof_L`     by Lean's kernel: the code numbers of the written sized proof's last test are the written place's
  `idx_head_L`      the code numbers of the seated place are the written place's
  `nums_head_L`     all seven numbers of the seated place are the written place's
  `alike_head_L`    the two places are alike
  `planB_head_L`    the plan's half at the seated place, at one first tree
  `osL`, `osL_length`   the test's one first tree, written: one entry
  `opens_LFull`     by Lean's kernel: the second round of the test's second part opens `osL` at the written place
  `simulatorJobAtFirstChainTest`         the simulators' job: the numbers q, no own table, `stateAtFirstChainTest` (Sim2/DoorAtL.lean), the openings op
  `openTies_L`      `OpenTies` at every job at the place, at `simulatorJobAtFirstChainTest`, at the chain number 0 where op names `osL`

By what. The seven numbers: `stretch_at_L`, `rows_at_seat_L`, `rounds_at_seat_L`, `plan_at_seat_L` (Johnson/Loose/H2K12/
CondAtLast.lean), `place_L_of_full` (Law/Sizes/PlacesAtScope.lean), `first_reads` (Law/Sizes/ClosedAtScope.lean),
`places_firstTree` (Law/FirstTreeOfMade.lean). The code numbers: `places_idx`, `idx_of_planOk` (Law/Sizes/IdxAtScope.lean) and
`sized_proof_in_scope` (Johnson/Second/Seam/AnswersOneInScope.lean), paid by `pins_of_laid`.

Limits. A public premise that is met is no sentence with content: what `slot_firstChainTest` says stays conditional on `OnEntry`, which is
not shown at a run here. This place alone. The chain number 0 and the list of first trees are the written ones. Nothing on
completeness, soundness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorAtL
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import AtFullSide.K12.RestTiesAtWL
import Johnson.Second.Seam.AnswersOneInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts T12)
open VerifiableInference.Desc.K12.Coin.At (closed_LFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open H2K.Member (piLFull codesFull)
open H2K.JointK (pL)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The written sized proof's last test has the written place's code numbers. -/
theorem nos_proof_L : H2K.Sizes.nosOf proofSizedFull.request.last = piLFull.idx := by decide +kernel

/-- **Under the head the code numbers of the seated place are the written ones.** -/
theorem idx_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).L.idx = piLFull.idx := by
  have e1 : (fourOf Np).L.idx = Np.L.idx := H2K.Sizes.idx_of_planOk _ _ (reads_head_L h).2.2.2
  have e2 := (H2K.Sizes.places_idx Zp.made Np h.laid.places).1
  have e3 : Zp.made.p.chains.made.sized.proof = proofSizedFull :=
    Second.Seam.sized_proof_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1
  rw [e1, e2, e3]
  exact nos_proof_L

/-- **Under the head all seven numbers of the seated place are the written place's.** -/
theorem nums_head_L (h : P5J.AtMg o Z D r₀ Zp Np cF) : (fourOf Np).L.nums = piLFull.nums := by
  obtain ⟨Z', N', c', _, hZ', hN', e, _, pre, l, J₀, hb, _, hJ₀⟩ :=
    H2K.JointK.k12_sits o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (H2K.JointK.descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  have hpin : VerifiableInference.PlanWritten.seatPinnedProof Z.pol
      (H2K.JointK.descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := by
    rw [← e]
    exact LPFD.asks_written h.laid.asks
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope hpin).1
  have hL := H2K.JointK.stages_of_pubPlain Johnson.AtFull.LayoutRead.layoutGroupsAre h.scope
    h.laid.pub
  have pk := H2K.JointK.plan_at_seat_L o Z' ProofFile.pureRoad.links N' c' hp ProofFile.sameReply pre l J₀ hb hJ₀
  have nL : (pL N').nums = N'.L.nums := H2K.Made.nums_of_planOk _ N'.L pk
  have hR := H2K.JointK.rounds_at_seat_L o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
    h.laid.places hp A hL hW ProofFile.sameReply pre l J₀ hb hJ₀
  have hrows := H2K.JointK.rows_at_seat_L o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
    h.laid.places hp A hL hW ProofFile.sameReply pre l J₀ hb hJ₀
  have hfree := (H2K.JointK.stretch_at_L o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
    h.laid.places hp A hL hW ProofFile.sameReply pre l J₀ hb hJ₀).2.2.2
  have hst := H2K.Sizes.place_L_of_full A h.laid.places hL
  have hown : N'.L.nums.ownMask = piLFull.nums.ownMask := H2K.Member.places_ownL Z'.made N' h.laid.places
  have hfirst : N'.L.nums.first = piLFull.nums.first := by
    rw [← nL]
    exact H2K.Sizes.first_reads pk closed_LFull.plan (by rw [nL]; exact hst.1) (by rw [nL]; exact hown)
      (H2K.Sizes.rdsAt_reads pk closed_LFull.plan (by rw [nL]; exact hR))
  exact nL.trans (H2K.Sizes.nums_ext hrows hst.2.1 hst.1 hown hfirst (hfree.trans rfl)
    ((H2K.Made.places_firstTree Z'.made N' h.laid.places).1.trans rfl))

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

/-- The test's one first tree, as the written place lists it. -/
def osL : List (Fmt.Shape × Fmt.TreeSource) := piLFull.nums.first

theorem osL_length : osL.length = 1 := by decide +kernel

/-- The second round of the test's second part opens it. -/
theorem opens_LFull :
    ((((H2K.JointK.laidOf piLFull).map (·.1)).drop (firstLen piLFull.nums.stages))[1]?).map (·.opens) =
      some osL := by decide +kernel

/-- **The simulators' job at the first chain's last test.** -/
def simulatorJobAtFirstChainTest (Zp : ProofFile.Pub) (q : P12) (op : List (ℕ × ℕ × ℕ)) : SimJob ProofFile.Inst := ⟨q, false, stateAtFirstChainTest Zp, op⟩

/-- **`OpenTies` under the head, at every job at the place, at `simulatorJobAtFirstChainTest`.** -/
theorem openTies_L {W X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).L) (q : P12) (op : List (ℕ × ℕ × ℕ))
    (hop : op = osL.map fun x => ((srcOf 0 x.2).1, (srcOf 0 x.2).2, x.1.a)) :
    OpenTies J (simulatorJobAtFirstChainTest Zp q op) 0 osL := by
  refine ⟨?_, hop⟩
  have e : ((((H2K.JointK.laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some osL := by
    rw [hJ, (alike_head_L h).decls, nums_head_L h]
    exact opens_LFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.nos_proof_L
#print axioms ProofFile.Honest.K12.Sim2.idx_head_L
#print axioms ProofFile.Honest.K12.Sim2.nums_head_L
#print axioms ProofFile.Honest.K12.Sim2.alike_head_L
#print axioms ProofFile.Honest.K12.Sim2.planB_head_L
#print axioms ProofFile.Honest.K12.Sim2.osL_length
#print axioms ProofFile.Honest.K12.Sim2.opens_LFull
#print axioms ProofFile.Honest.K12.Sim2.simulatorJobAtFirstChainTest
#print axioms ProofFile.Honest.K12.Sim2.openTies_L
