-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the public ties under the head.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/AtHead.lean: UNDER THE HEAD, AT THE SEATED PLACE OF THE TEST ON G_omega: the public ties `PublicTiesOwn` (SimO/Free.lean) hold for `jobAtOmega`, and `OpenTies` at the test's one first list, for a simulators' job that names that list's openings. So `exact_free_own` is had there with no public premise left.

  `idx_head_omega`, `alike_head_omega`, `alike_renum_head`   the seated place and the written place are alike, and so are the two renumbered
  `planOB_alike`, `planOB_head`   the library's test `planOB` at alike places, and so under the head
  `reach_renum_head`, `declared_renum_head`   `reachTB` at the renumbered seated place; it declares as many positions by round as the place
  `publicTiesOwn_head`     **the public ties**
  `firstListAtOmega`, `firstListAtOmega_length`    the list that the test's first switch opens, written: three trees
  `openTies_head_omega`    `OpenTies` at every job at the place
  `exact_free_head_omega`, `exact_entry_head_omega`    **`ExactMember` at the second member of `jobAtOmega`, under the head**

Limits. CONDITIONAL on `onFreeOwn`, `OnEntryOwn`. The job is `jobAtOmega`. No property of the protocol is claimed: nothing on completeness, soundness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Entry
import Johnson.Desc.ProofFile.Honest.K12.SimO.Public
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts foldAt switchAt batAt Laid)
open Desc.K14 (St)
open H2K.Member (piOFull codesFull)
open H2K.JointK (laidOf laidS pGomega)
open ProofFile.Honest.Small (ExactMember)
open Johnson.Prover.Link
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Own (planOB planOL renumP renum planOB_O_full)

variable {V W X Pb : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- The code numbers at the test. -/
theorem idx_real_omega : (VerifiableInference.Desc.K1.realSized.all fun q =>
    decide (H2K.Sizes.nosOf q.1.shape.testOmega = piOFull.idx)) = true := by
  decide +kernel

/-- **Under the head the code numbers of the seated place are the written ones.** -/
theorem idx_head_omega (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    pO.idx = piOFull.idx := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  have e1 : (pGomega nO).idx = nO.idx := H2K.Sizes.idx_of_planOk _ _ (planOk_head_O h hO)
  have e2 := (H2K.Sizes.places_idx Zp.made Np h.laid.places).2.2.1 nO h1
  have e3 : Zp.made.p.chains.made.sized.proof.batch.shape = x.shape := Wr.shape
  have k := idx_real_omega
  rw [hx] at k
  simp only [Option.all_some, decide_eq_true_eq] at k
  rw [e1, e2, e3]
  exact k

theorem alike_head_omega (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    Alike pO piOFull where
  nums := nums_head_O h hO
  idx := idx_head_omega h hO
  early := (H2K.JointK.early_of_planOk pO (planOk_head_O h hO)).trans (by decide)
  answers := (H2K.JointK.answers_of_planOk pO (planOk_head_O h hO)).trans (by decide)
  decls := by rw [decls_thin, decls_thin, thin_head_O h hO]

/-- Where there are at least as many oracle lists as rounds, the declared rounds of a place are its rounds. -/
theorem rounds_of_enough_oracles (p : P12) (h : ((H2U.roundsOfNums p.nums).getD []).length ≤ p.oracles.length) :
    (laidOf p).map (·.1) = (H2U.roundsOfNums p.nums).getD [] := by
  unfold laidOf
  exact List.map_fst_zip h

theorem oracles_length_written :
    ((H2U.roundsOfNums piOFull.nums).getD []).length ≤ piOFull.oracles.length ∧
    ((H2U.roundsOfNums (renumP piOFull).nums).getD []).length =
      ((H2U.roundsOfNums piOFull.nums).getD []).length := by
  decide +kernel

theorem rounds_renum_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (laidOf (renumP pO)).map (·.1) = (laidOf (renumP piOFull)).map (·.1) := by
  have e1 : (renumP pO).nums = (renumP piOFull).nums := by
    show renum pO.nums = renum piOFull.nums
    rw [nums_head_O h hO]
  have hl : (laidOf pO).length = (laidOf piOFull).length := length_congr (thin_head_O h hO)
  have h1 : (laidOf piOFull).length = ((H2U.roundsOfNums piOFull.nums).getD []).length := by
    unfold laidOf
    rw [List.length_zip]
    exact Nat.min_eq_left oracles_length_written.1
  have h2 : (laidOf pO).length ≤ pO.oracles.length := by
    unfold laidOf
    rw [List.length_zip]
    exact Nat.min_le_right _ _
  have h3 := oracles_length_written.2
  have l1 : ((H2U.roundsOfNums (renumP pO).nums).getD []).length ≤ (renumP pO).oracles.length := by
    rw [e1]
    show _ ≤ pO.oracles.length
    omega
  have l2 : ((H2U.roundsOfNums (renumP piOFull).nums).getD []).length ≤ (renumP piOFull).oracles.length := by
    show _ ≤ piOFull.oracles.length
    have := oracles_length_written.1
    omega
  rw [rounds_of_enough_oracles _ l1, rounds_of_enough_oracles _ l2, e1]

theorem alike_renum_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    Alike (renumP pO) (renumP piOFull) where
  nums := by
    show renum pO.nums = renum piOFull.nums
    rw [nums_head_O h hO]
  idx := (alike_head_omega h hO).idx
  early := (alike_head_omega h hO).early
  answers := (alike_head_omega h hO).answers
  decls := rounds_renum_head h hO

/-- The library's test at alike places. -/
theorem planOB_alike {p q : P12} (A : Alike p q) (Ar : Alike (renumP p) (renumP q)) (K : OnBytes.Codes)
    (nT : ℕ) : planOB p K nT = planOB q K nT := by
  have hS := laidS_alike A
  have r1 : ∀ (u : P12) (a : Fmt.M1.Stage),
      (foldAt guardedProximityTestParts u 0 a (laidS u) : Block T12 Unit).rounds =
        ((laidS u).take (1 + a.k)).map (·.1) := fun _ _ => rfl
  have r2 : ∀ (u : P12) (a next : Fmt.M1.Stage) (last : Bool),
      (switchAt guardedProximityTestParts u 0 a next last (laidS u) : Block T12 Unit).rounds =
        (((laidS u).drop (1 + a.k)).take 2).map (·.1) := fun _ _ _ _ => rfl
  have r3 : ∀ u : P12, (batAt guardedProximityTestParts u (laidOf u) : Block T12 Unit).rounds =
      ((laidOf u).take 1).map (·.1) := fun _ => rfl
  have s1 : ∀ n, (((laidS p).drop n).map asked) = (((laidS q).drop n).map asked) := fun n => by
    have e : ∀ u : Laid, u.map asked = (u.map (·.1)).map fun d => d.items.filter (· != .root) :=
      fun u => by
        rw [List.map_map]
        rfl
    rw [e, e, drop_decls hS]
  unfold planOB planOL VerifiableInference.Desc.Block.openings
  simp only [A.nums, lettersOf_alike A, switchPubB_alike A, switchPlanB_alike A, stageAt_alike A,
    r1, r2, r3, take_decls hS, take_decls A.decls, take_decls (drop_decls hS _), s1,
    planFromOk_alike Ar K _ _ _ _ _ (drop_decls hS _)]

theorem planOB_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    planOB pO codesFull 3 = true := by
  rw [planOB_alike (alike_head_omega h hO) (alike_renum_head h hO)]
  exact planOB_O_full

theorem reach_renum_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    reachTB (renumP pO) = true := by
  have hs : (renumP pO).nums.stages = (renumP piOFull).nums.stages :=
    congrArg (·.stages) (nums_head_O h hO)
  rw [reachTB_reads hs rfl (rounds_renum_head h hO)]
  exact reach_renum_written

theorem declared_of_rounds {p q : P12} (h : ((laidOf p).map (·.1)).map (·.entry.poss) = ((laidOf q).map (·.1)).map (·.entry.poss))
    (i : ℕ) : declared p i = declared q i := by
  have e : ∀ r : P12, declared r i = (((((laidOf r).map (·.1)).map (·.entry.poss))[i]?)).getD 0 := fun r => by
    unfold declared
    rw [List.map_map, List.getElem?_map]
    rfl
  rw [e p, e q, h]

theorem declared_renum_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (i : ℕ) :
    declared (renumP pO) i = declared pO i := by
  refine declared_of_rounds ?_ i
  rw [rounds_renum_head h hO, positions_renum_written, decls_thin pO, thin_head_O h hO, ← decls_thin]

/-- **The public ties at `jobAtOmega`, under the head.** -/
theorem publicTiesOwn_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb) (hJ : Js.p = pO)
    (ho : Js.own = true) :
    PublicTiesOwn (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js codesFull 3 := by
  have F := firstPubOwn_head h hO door weights rand omega? Js hJ ho
  have hn := nums_head_O h hO
  have hf : pO.nums.ownMask = true := by
    rw [hn]
    decide +kernel
  refine ⟨hJ, ho, hf, reach_renum_head h hO, planOB_head h hO, declared_renum_head h hO, F.form, count_head_O h hO, ?_, F.tables⟩
  show restLen pO.nums.stages = 2 + lenFrom (stN pO) (pO.nums.stages.drop 2)
  unfold stN
  rw [hn]
  exact rounds_written

/-- The list that the test's first switch opens, as the written place has it. -/
def firstListAtOmega : List (Fmt.Shape × Fmt.TreeSource) :=
  ((((((laidOf piOFull).map (·.1)).drop (firstLen piOFull.nums.stages))[1]?).map (·.opens))).getD []

theorem firstListAtOmega_length : firstListAtOmega.length = 3 := by decide +kernel

theorem opens_at_written_omega :
    ((((laidOf piOFull).map (·.1)).drop (firstLen piOFull.nums.stages))[1]?).map (·.opens) = some firstListAtOmega := by
  decide +kernel

/-- **`OpenTies` at every job at the place.** -/
theorem openTies_head_omega {W' X' : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (J : TestJob W' X') (Js : SimJob Pb) (hp : J.p = pO) (chain : ℕ)
    (hop : Js.opens = firstListAtOmega.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain firstListAtOmega := by
  refine ⟨?_, hop⟩
  have e : ((((laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) = some firstListAtOmega := by
    rw [hp, decls_thin pO, thin_head_O h hO, ← decls_thin, nums_head_O h hO]
    exact opens_at_written_omega
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **The sentence at the second member, under the head.** -/
theorem exact_free_head_omega (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (φ : Face V W Pb) (σ : Side St ProofFile.Cl V W X Pb) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hJ : Js.p = pO) (ho : Js.own = true) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtOmega.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree
      (onFreeOwn φ (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js codesFull chain firstListAtOmega)
      (budOpened pO.nums.stages)
      (restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) :=
  exact_free_own φ σ _ Js codesFull chain firstTree firstListAtOmega
    (firstListAtOmega_length ▸ publicTiesOwn_head h hO door weights rand omega? Js hJ ho)
    (openTies_head_omega h hO _ Js rfl chain hop)

/-- **The sentence at the second member, under the head, at a state that stands in.** -/
theorem exact_entry_head_omega (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (φ : Face V W Pb) (σ : Side St ProofFile.Cl V W X Pb) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hJ : Js.p = pO) (ho : Js.own = true) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtOmega.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree
      (OnEntryOwn φ (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js codesFull chain firstListAtOmega)
      (budOpened pO.nums.stages)
      (restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) :=
  exact_entry_own φ σ _ Js codesFull chain firstTree firstListAtOmega
    (firstListAtOmega_length ▸ publicTiesOwn_head h hO door weights rand omega? Js hJ ho)
    (openTies_head_omega h hO _ Js rfl chain hop)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.exact_entry_head_omega
#print axioms ProofFile.Honest.K12.Light.alike_renum_head
#print axioms ProofFile.Honest.K12.Light.planOB_head
#print axioms ProofFile.Honest.K12.Light.reach_renum_head
#print axioms ProofFile.Honest.K12.Light.declared_renum_head
#print axioms ProofFile.Honest.K12.Light.publicTiesOwn_head
#print axioms ProofFile.Honest.K12.Light.firstListAtOmega_length
#print axioms ProofFile.Honest.K12.Light.openTies_head_omega
#print axioms ProofFile.Honest.K12.Light.exact_free_head_omega
