-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstSeatAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean), the side of the proximity test on G_u that is taken off the shared list of
the proof file's own description (`testSide`, Sim/Row.lean, at `(P5J.F0T o Zp Np cF).shared.blocksInOrder`)
is there; it passes the frame's test on sides (`Side.fits`); its members are the two that are
written out; and at the first of them the sentence `ExactMember` holds at the side's own `testOn`
and `testBud`. The job is `jobAtU` (JobShared.lean) at the proof file's own plan and the seated
place. It imports Mathlib.

  `find_at`, `find_gu`   the first block of that list at the place of the test on G_u stands at
                 that place and has the rounds and oracle messages of the test's own block (in the
                 proof it is the library's `guEntry`, Johnson/Desc/K12/Law/SitsChains.lean; the
                 statement does not name it)
  `count_UFull`, `count_head_U`   the place declares as many rounds as the two parts have moves: at
                 `piUFull` by Lean's kernel; at the seated place under the head
  `fits_of`      `Side.fits` at a side whose block has the rounds and oracle messages of the test's
                 own block, general in the place
  `seat_head_U`  the side is there, at every list of falls
  `seated_head_U`   whatever side `testSide` returns there: `fits`, the two members, the sentence

By what. The library's `k12_sits_row` (Johnson/Loose/H2K12/SitsRow.lean): the description is
`descN`; `guEntry` is in its shared list; whatever entry of that list bears the kind K12 is
`guEntry` or `omegaEntry`. Their places: `guEntry_place`, `omegaEntry_place`
(Johnson/Desc/K12/Law/SharedPlaces.lean). So nothing is read of what stands in front of the test.
`guEntry` has the rounds and oracle messages of the test's own block by unfolding; `zip_laid`
(PlaysK12.lean) at `planOk_head_U` (NearAtHead.lean); `members_of_seat` (Sim/ExactSide.lean);
`exact_first_head`, `nums_head_U`, `thin_head_U`, `length_congr` (Sim/FirstPubAtHead.lean).

The 0 in `⟨K1.qAt Zp Np, 0⟩` is the field `atPoint` of `SendPub`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean): the number, among the shared chain's rounds, of
"LIN point", by which the sender's vector is computed. It is compared with nothing here, and nothing
here says that 0 is that number at this plan.

Limits.
- The sentence is shown at a job whose state on entry is any function: nothing says that it is the
  verifier's state.
- It is shown at no job that is played: that a job which somebody lays is this one is up to whoever
  lays it.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- It is the spender's half: the 2 k + 1 values that the first member spends are sampled anew in the
  sentence. The same values stand in the sender's tree and in what the second part carries; nothing
  here joins these.
- The first member alone: no sentence is shown at the side's second member. Only where the fresh
  table came earlier: not at the test on G_omega.
- `testOn` asks nothing at the first member, and `testBud` nothing where the fold sends no table:
  the sentence holds at every On and bud (`exact_first`).
- No stand, front or challenges at which the sentence's own hypotheses hold are written here;
  Sim/MeetsAtHead.lean has them, under the head, at written letters, at the member as it is written
  out and at any side (`meets_head_U`).
- The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactSide
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.K12.Law.SharedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open H2K.Member (piUFull)
open H2K.JointK (descN laidOf guEntry omegaEntry pGu)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 The count, and `fits` -/

theorem count_UFull : (laidOf piUFull).length =
    firstLen piUFull.nums.stages + restLen piUFull.nums.stages := by decide +kernel

variable {S Cl V W X Pb : Type}

/-- **`Side.fits`**, where the side's block stands at the job's place and has the rounds and oracle
messages of the test's own block. -/
theorem fits_of (J : TestJob W X) (Js : SimJob Pb) (hJ : Js.p = J.p) (b : Block S Cl)
    (fall : S → List Fmt.Drawn → Option String) (hp : b.place = J.p.place)
    (hk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (ho : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles) (s t : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hc : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages) :
    (⟨b, testPairs J Js, fall⟩ : Side S Cl V W X Pb).fits = true := by
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages :=
    (congrArg List.length (rest_moves J s t rest hst)).trans (len_movesFrom J _ _ _)
  obtain ⟨rds, e1, e2⟩ := H2K.Made.rounds_of_planOk guardedProximityTestParts J.p hk
  have e3 : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds = rds :=
    Option.some.inj ((VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts J.p hk).symm.trans e1)
  have e4 : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles = J.p.oracles :=
    VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts J.p hk
  have e5 : (laidOf J.p).length = rds.length := by
    unfold laidOf
    rw [e1, Option.getD_some, List.length_zip, e2, Nat.min_self]
  unfold Side.fits
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ((firstSim Js).addr == ⟨b.place, 0⟩ && ((restSim Js).addr == ⟨b.place, 1⟩ && true)) = true
    have a0 : (firstSim Js).addr = ⟨b.place, 0⟩ := by
      rw [hp, ← hJ]
      unfold firstSim
      split <;> rfl
    have a1 : (restSim Js).addr = ⟨b.place, 1⟩ := by
      rw [hp, ← hJ]
      rfl
    rw [a0, a1]
    simp
  · show 0 + (firstPart J : Part V W X).moves.length + (restPart J : Part V W X).moves.length =
      b.rounds.length
    rw [l1, l2, hr, e3, ← e5, hc, Nat.zero_add]
  · show b.oracles.length = b.rounds.length
    rw [ho, hr, e4, e3, e2]

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem count_head_U (h : P5J.AtMg o Z D r Zp Np cF) : (laidOf (fourOf Np).U).length =
    firstLen (fourOf Np).U.nums.stages + restLen (fourOf Np).U.nums.stages := by
  rw [length_congr (thin_head_U h), nums_head_U h]
  exact count_UFull

/-- At a description that is `descN`: the first block of its shared list at the place of the test on
G_u stands at that place and has the rounds and oracle messages of the test's own block. F is a
letter, so that the blocks' types can follow it. -/
theorem find_at {mk : ProofFile.LinksBy} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst) (hF : F = descN o mk guardedProximityTestParts Zp N c)
    (R : H2K.JointK.RowK12 o mk Zp N c) :
    ∃ b, (F.shared.blocksInOrder.find? fun b => b.place == (⟨2, none, 9, .K12⟩ : Place)) = some b ∧
      b.place = ⟨2, none, 9, .K12⟩ ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit).oracles := by
  subst hF
  cases hf : (descN o mk guardedProximityTestParts Zp N c).shared.blocksInOrder.find?
      fun b => b.place == (⟨2, none, 9, .K12⟩ : Place) with
  | none =>
    have := List.find?_eq_none.1 hf _ R.gu.1
    rw [H2K.JointK.guEntry_place] at this
    exact (this (by simp)).elim
  | some b =>
    have hb : b.place = ⟨2, none, 9, .K12⟩ := by simpa using List.find?_some hf
    rcases R.sharedOnly b (List.mem_of_find?_eq_some hf) (by rw [hb]) with rfl | ⟨nO, _, rfl⟩
    · exact ⟨_, rfl, hb, rfl, rfl⟩
    · rw [H2K.JointK.omegaEntry_place] at hb
      cases hb

/-- **The first block of the description's shared list at the place of the test on G_u.** -/
theorem find_gu (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ b : Block St ProofFile.Cl,
      ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place == (fourOf Np).U.place) = some b ∧
      b.place = (fourOf Np).U.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).oracles := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hpl : (fourOf N').U.place = ⟨2, none, 9, .K12⟩ := H2K.JointK.place_of_p12At _ _
  rw [hpl]
  exact find_at (P5J.F0T o Z' N' cF) e R

section Side
variable (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12) (weights : W → Weights)
  (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
  (fs : List (Fall St))

include h in
/-- **The side is there.** -/
theorem seat_head_U : ∃ σ : Side St ProofFile.Cl V W X Pb,
    testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js fs =
        some σ := by
  obtain ⟨b, hf, _, _, _⟩ := find_gu h
  unfold testSide Side.seated
  exact ⟨_, by
    show Option.map _ ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b =>
      b.place == (fourOf Np).U.place) = _
    rw [hf]
    rfl⟩

include h in
/-- **Whatever side `testSide` returns there**: it passes the frame's test on sides; its members are
the two that are written out; and the sentence holds at the first, at the side's own On and bud. -/
theorem seated_head_U (hJ : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js fs = some σ) :
    σ.fits = true ∧
    σ.members =
      [firstMember (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js,
        restMember (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js] ∧
    ∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
      (testOn φ (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js)
      (testBud Js)
      (firstMember (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest
        Js) := by
  have hk := planOk_head_U h
  have hst : (fourOf Np).U.nums.stages = piUFull.nums.stages := congrArg (·.stages) (nums_head_U h)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piUFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  obtain ⟨b, hf, hp, hr, hor⟩ := find_gu h
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  have hf' : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place ==
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest.p.place) =
      some b := hf
  rw [hf'] at hσ'
  obtain rfl := Option.some.inj hσ'
  refine ⟨?_, ?_, fun φ chain firstTree => ?_⟩
  · exact fits_of _ Js hJ b _ hp hk hr hor s t rest (hst.trans hlit) (count_head_U h)
  · refine members_of_seat _ _ Js fs _ hσ ?_ s t rest (hst.trans hlit) (count_head_U h)
    show b.rounds.zip b.oracles = _
    rw [hr, hor]
    exact zip_laid (fourOf Np).U hk
  · exact exact_first_head h φ _ door weights rand u? Js hJ ho chain firstTree _ _

end Side

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.count_UFull
#print axioms ProofFile.Honest.K12.Light.fits_of
#print axioms ProofFile.Honest.K12.Light.count_head_U
#print axioms ProofFile.Honest.K12.Light.find_at
#print axioms ProofFile.Honest.K12.Light.find_gu
#print axioms ProofFile.Honest.K12.Light.seat_head_U
#print axioms ProofFile.Honest.K12.Light.seated_head_U
