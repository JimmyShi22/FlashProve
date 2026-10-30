-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/StagesOfPlan.lean: `StagesOk` (RunBy.lean), the hypothesis of
`runBy_eq`, follows from the proximity test's own test on the plan. At every parameter p and
whatever the parts: where the block `proximityTestKind X p` (Johnson/Desc/K12/Frame.lean) passes its test on the
plan, p's stages pass `StagesOk`. No list of stages is written out here and no scope is asked.

  `stagesOk_of_sizesOk`   stages whose sizes fit together (`sizesOk`, Johnson/Desc/K12/Sizes.lean)
                 pass `StagesOk`
  `stagesOk_of_planOk`   the statement at a block
  `fourOf_eq`    `AtProof.fourOf N` (AtProof/Places.lean) is the library's four parameters `pGu`,
                 `pGomega`, `pOwn`, `pL` (Johnson/Desc/K12/Law/SitsChains.lean)
  `stagesOk_desc`   wherever the proof file's description is made (`ProofFile.onlineDescription` returns) and
                 passes its test on the plan, at any public files: at the four seated parameters,
                 Omega's where the plan has one
  `stagesOk_laid`, `stagesOk_laid_small`   two calls of it: where `LPFD.Full.proofDataAndDecisionOfPublicFiles` returns, and
                 where `LPFD.Small.laidPOf` returns
  `stagesOk_seated`   under the library's head (`P5J.AtMg`, Johnson/P5J/AtMg.lean): at the numbers
                 at which the proof file's description seats its four proximity tests
                 (`AtProof.fourOf Np`, AtProof/Places.lean), Omega's among them

By what. `sizesOk` is the first clause of the block's test on the plan (`sizesOk_of_planOk`,
Johnson/Prover/Link/LinkCoinFits.lean). Clause by clause it holds what `okFrom` and `switchFitB`
ask: two stages or more; at each stage h ≤ k, both message lengths powers of two, the mask code no
longer than the main code; at the last stage k = 0, so h = 0; at every other 2 k + 1 - h ≤ Z.l; from
a stage to the next the equation on the main tables' sizes and the bound on the mask table's room,
the bound with the number of answers, which is at least 1, where `switchFitB` has 1. Where the
description passes its test on the plan each seated block passes its own (`RowK12.plans` over
`k12_sits_row`, Johnson/Loose/H2K12/SitsRow.lean); where a value is laid, and so under the head, the
description does pass (`laidPOf_ok`, Johnson/Desc/Laid/ProofFullLaw.lean and ProofSmallLaw.lean); in
the goals' scope Omega's place is there (`omega_some_in_scope`,
Johnson/Loose/H2K12/OmegaIsSome.lean).

Limits. It speaks of the p whose block's test on the plan is shown. That a job is laid at that p is
for whoever lays the job to show: `jobAtU` and `jobAtOmega` (JobShared.lean) take their `P12` as a
parameter. "Seats": each entry of the kind in the description's three chains sits on the block at
these parameters: it declares the block's rounds, its test on the plan gives the block's, its yes
gives the block's yes (`RowK12`, `Sits`); that the entry is the block is not claimed there. One
direction: `StagesOk` asks less than `sizesOk`; among what it does not ask: that the codes are in
order, k ≤ 60, 1 ≤ k, a mask row against the answers, the first stage's message lengths, the last
stage's Z.a ≤ C.a. No converse is stated. `stagesOk_seated` stands under the head: that the head
holds is a theorem at one set of public files (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean). Of the head's fields, `scope` is spent for Omega's place
alone; U, W and L follow from the field `laid`. `stagesOk_laid` is not empty either:
`FlashProve.theProofLaid` unfolds to `LPFD.Full.proofDataAndDecisionOfPublicFiles` at `OnBytes.secondHashFunction`, and it returns at
these files (`proofLaid_zFull`, Johnson/AtFull/Top/LiveAtZFull.lean, whose two premises are proved
in the side library); no call of it is made here. That `LPFD.Full.proofDataAndDecisionOfPublicFiles` returns at any other
files is not shown. That `LPFD.Small.laidPOf` returns at given files is not shown here. By a search
of the library by that name no theorem there states it either: the name stands in a conclusion in
`laidPOf_of` and `laidOk_iff` (Johnson/Desc/Laid/ProofSmallLaw.lean) alone, the first under four
hypotheses, and neither is called. The key file's tests: at three of its four, at written parameter
sets, RunBySpecAt.lean. The library has a theorem of the same short name in another namespace,
`H2K.Made.stagesOk_of_planOk` (Johnson/Desc/K12/Law/MasksPlan.lean): same premise, and it ends in
`sizesOk`'s walk `stagesOk` (small s), not in `StagesOk`. `StagesOk` reads public numbers alone:
nothing here speaks of a random value. Words: the head is the structure `P5J.AtMg`; a test on the
plan is the field `planOk` of a block, or the definition `FileDescription.planOk` of a description; the
public part is what `ProofFile.pubPlain` makes of the three public files; the scope is `VerifierAndGoals.InScope`; a
place is a `VerifiableInference.Desc.Place`. It imports Mathlib. Nothing on completeness, soundness
or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.P5J.AtMg
import Johnson.Loose.H2K12.SitsRow
import Johnson.Loose.H2K12.OmegaIsSome
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.Laid.ProofSmallLaw
import Johnson.Prover.Link.LinkCoinFits
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt.M1 (Stage)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 Parts proximityTestKind guardedProximityTestParts sizesOk stagesOk stageOk stepOk pow2)
open H2K.JointK (descN pL pGu pGomega pOwn)
open ProofFile.Honest.K12.AtProof (four fourOf)

/-! ## 1 From the kind's own test on the plan -/

/-- What the walk over the stages holds at its first stage. -/
theorem walk_cons (a : ℕ) (before : Option Stage) (s : Stage) (rest : List Stage)
    (h : stagesOk a before (s :: rest) = true) :
    stageOk rest.isEmpty s = true ∧ (∀ p, before = some p → stepOk a p s = true) ∧
      stagesOk a (some s) rest = true := by
  cases before with
  | none =>
    have h' : (stageOk rest.isEmpty s && true && stagesOk a (some s) rest) = true := h
    simp only [Bool.and_eq_true] at h'
    exact ⟨h'.1.1, fun _ hp => (by cases hp), h'.2⟩
  | some q =>
    have h' : (stageOk rest.isEmpty s && stepOk a q s && stagesOk a (some s) rest) = true := h
    simp only [Bool.and_eq_true] at h'
    refine ⟨h'.1.1, fun p hp => ?_, h'.2⟩
    cases hp
    exact h'.1.2

/-- Of the conditions on a stage by itself, those that are spent here. -/
theorem stage_facts (last : Bool) (s : Stage) (h : stageOk last s = true) :
    pow2 s.C.l = true ∧ pow2 s.Z.l = true ∧ s.Z.a ≤ s.C.a ∧ s.h ≤ s.k ∧
      (if last then s.k == 0
        else decide (1 ≤ s.k) && decide (2 * s.k + 1 - s.h ≤ s.Z.l)) = true := by
  unfold stageOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.2, h.2⟩

/-- The walk over the stages gives `okFrom`, where a sample has an answer. -/
theorem okFrom_of_walk (a : ℕ) (ha : 1 ≤ a) : ∀ (rest : List Stage) (s : Stage)
    (before : Option Stage), stagesOk a before (s :: rest) = true → okFrom s rest = true
  | [], s, before, h => by
    obtain ⟨h1, _, _⟩ := walk_cons a before s [] h
    obtain ⟨_, _, _, hk, hl⟩ := stage_facts _ _ h1
    have k0 : s.k = 0 := eq_of_beq (hl : (s.k == 0) = true)
    have h0 : s.h = 0 := by omega
    show (s.k == 0 && s.h == 0) = true
    rw [k0, h0]
    rfl
  | n :: rest, s, before, h => by
    obtain ⟨h1, _, h3⟩ := walk_cons a before s (n :: rest) h
    obtain ⟨hn1, hstep, _⟩ := walk_cons a (some s) n rest h3
    have st := hstep s rfl
    obtain ⟨_, _, za, hk, hl⟩ := stage_facts _ _ h1
    obtain ⟨pC, pZ, _, _, _⟩ := stage_facts _ _ hn1
    have hl' : (decide (1 ≤ s.k) && decide (2 * s.k + 1 - s.h ≤ s.Z.l)) = true := hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl'
    unfold stepOk at st
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at st
    have ih := okFrom_of_walk a ha rest n (some s) h3
    have sw : switchFitB s n = true := by
      unfold pow2 at pC pZ
      unfold switchFitB pow2B
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at pC pZ ⊢
      refine ⟨⟨⟨⟨?_, ?_⟩, pC.symm⟩, pZ.symm⟩, za⟩
      · rw [Nat.mul_comm]
        exact st.1.1
      · have h2 := st.1.2
        rw [Nat.mul_comm n.Z.l] at h2
        omega
    show (decide (s.h ≤ s.k) && decide (2 * s.k + 1 ≤ s.h + s.Z.l) && switchFitB s n &&
      okFrom n rest) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hk, by omega⟩, sw⟩, ih⟩

/-- **Stages whose sizes fit together pass `StagesOk`.** -/
theorem stagesOk_of_sizesOk (l : List Stage) (a : ℕ) (h : sizesOk l a = true) :
    StagesOk l = true := by
  unfold sizesOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h2, ha⟩, hw⟩ := h
  match l, h2, hw with
  | [], h2, _ => simp at h2
  | [_], h2, _ => simp at h2
  | s :: n :: rest, _, hw => exact okFrom_of_walk a ha (n :: rest) s none hw

/-- **Where the proximity test's block passes its test on the plan, its stages pass `StagesOk`.**
Not `H2K.Made.stagesOk_of_planOk`, which ends in the walk `stagesOk`. -/
theorem stagesOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : StagesOk p.nums.stages = true :=
  stagesOk_of_sizesOk _ _ (Johnson.Prover.Link.sizesOk_of_planOk X p hp)

/-! ## 2 Where the value is laid; under the head -/

/-- The four parameters of AtProof/Places.lean are the library's. -/
theorem fourOf_eq (N : H2U.Places4) : fourOf N = ⟨pGu N, N.O.map pGomega, pOwn N, pL N⟩ := rfl

/-- **Wherever the proof file's description is made and passes its test on the plan**, at any public
files: the public part has its four places, and the stages at the parameters at which the
description seats the tests (`fourOf_eq`, `RowK12`) pass `StagesOk`; Omega's where the plan has that
place. -/
theorem stagesOk_desc (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst) (hF : ProofFile.onlineDescription o pol lay KL = .ok F)
    (hp : F.planOk = true) :
    ∃ Z N, ProofFile.pubPlain o pol lay KL = .ok Z ∧ four Z = some (fourOf N) ∧
      StagesOk (fourOf N).U.nums.stages = true ∧
      (∀ p, (fourOf N).O = some p → StagesOk p.nums.stages = true) ∧
      StagesOk (fourOf N).W.nums.stages = true ∧ StagesOk (fourOf N).L.nums.stages = true := by
  obtain ⟨Z, N, c, hZ, hN, rfl, R⟩ := H2K.JointK.k12_sits_row o pol lay KL F hF
  obtain ⟨kL, kU, kO, kW⟩ := R.plans hp
  refine ⟨Z, N, hZ, ?_, stagesOk_of_planOk guardedProximityTestParts (pGu N) kU, fun p hq => ?_,
    stagesOk_of_planOk guardedProximityTestParts (pOwn N) kW, stagesOk_of_planOk guardedProximityTestParts (pL N) kL⟩
  · unfold four
    rw [hN]
  · have e : N.O.map pGomega = some p := hq
    cases hO : N.O with
    | none =>
      rw [hO] at e
      cases e
    | some nO =>
      rw [hO] at e
      obtain rfl : pGomega nO = p := Option.some.inj e
      exact stagesOk_of_planOk guardedProximityTestParts (pGomega nO) (kO nO hO)

/-- The same where the value of the smaller size is laid. -/
theorem stagesOk_laid_small (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (D : OnBytes.Maker.WholeD) (r : LPFD.Small.RunPS)
    (hL : LPFD.Small.laidPOf o pol lay KL = .ok (D, r)) :
    ∃ Z N, ProofFile.pubPlain o pol lay KL = .ok Z ∧ four Z = some (fourOf N) ∧
      StagesOk (fourOf N).U.nums.stages = true ∧
      (∀ p, (fourOf N).O = some p → StagesOk p.nums.stages = true) ∧
      StagesOk (fourOf N).W.nums.stages = true ∧ StagesOk (fourOf N).L.nums.stages = true := by
  obtain ⟨F, hF, hp, _⟩ := LPFD.Small.laidPOf_ok hL
  exact stagesOk_desc o pol lay KL F hF hp

/-- **Wherever the proof file's value is laid**, at any public files: the public part has its four
places, and the stages at the parameters at which the description seats the tests (`fourOf_eq`,
`RowK12`) pass `StagesOk`; Omega's where the plan has that place. -/
theorem stagesOk_laid (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ Z N, ProofFile.pubPlain o pol lay KL = .ok Z ∧ four Z = some (fourOf N) ∧
      StagesOk (fourOf N).U.nums.stages = true ∧
      (∀ p, (fourOf N).O = some p → StagesOk p.nums.stages = true) ∧
      StagesOk (fourOf N).W.nums.stages = true ∧ StagesOk (fourOf N).L.nums.stages = true := by
  obtain ⟨F, hF, hp, _⟩ := LPFD.Full.laidPOf_ok hL
  exact stagesOk_desc o pol lay KL F hF hp

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head the public part has its four places, Omega's among them, and the stages at the
parameters at which the description seats the four tests (`fourOf_eq`, `RowK12`) pass `StagesOk`.**
-/
theorem stagesOk_seated (h : P5J.AtMg o Z D r Zp Np cF) :
    four Zp = some (fourOf Np) ∧ StagesOk (fourOf Np).U.nums.stages = true ∧
    (∃ p, (fourOf Np).O = some p ∧ StagesOk p.nums.stages = true) ∧
    StagesOk (fourOf Np).W.nums.stages = true ∧ StagesOk (fourOf Np).L.nums.stages = true := by
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
  obtain ⟨kL, kU, kO, kW⟩ := R.plans hp
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Z' ProofFile.pureRoad.links N' c' hp hpin
  refine ⟨?_, stagesOk_of_planOk guardedProximityTestParts (pGu N') kU,
    ⟨pGomega nO, ?_, stagesOk_of_planOk guardedProximityTestParts (pGomega nO) (kO nO hO)⟩,
    stagesOk_of_planOk guardedProximityTestParts (pOwn N') kW, stagesOk_of_planOk guardedProximityTestParts (pL N') kL⟩
  · unfold four
    rw [h.laid.places]
  · show N'.O.map _ = _
    rw [hO]
    rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.walk_cons
#print axioms ProofFile.Honest.K12.Light.stage_facts
#print axioms ProofFile.Honest.K12.Light.okFrom_of_walk
#print axioms ProofFile.Honest.K12.Light.stagesOk_of_sizesOk
#print axioms ProofFile.Honest.K12.Light.stagesOk_of_planOk
#print axioms ProofFile.Honest.K12.Light.fourOf_eq
#print axioms ProofFile.Honest.K12.Light.stagesOk_desc
#print axioms ProofFile.Honest.K12.Light.stagesOk_laid_small
#print axioms ProofFile.Honest.K12.Light.stagesOk_laid
#print axioms ProofFile.Honest.K12.Light.stagesOk_seated
