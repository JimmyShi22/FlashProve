-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyAtHeadW.lean: `any_at_place`
(Sim/FirstAnyAtPlace.lean) under the library's head (`P5J.AtMg`), at the place at which the proof
file's description seats the second chain's own proximity test, `(fourOf Np).W`, off the
description's own second list (its field `second`, `FileDescription.second`; the place there bears chain
3): at every job at that place.

  `dsW`          seven challenges, each the one field element (1, 0, 0)
  `facts_WFull`  the seven public tests at the written place `piWFull`: six evaluated by Lean's
                 kernel, the block's test on the plan from the library's `closed_WFull`
  `reads_head_W`   under the head the seated place has the written place's stages, flag and declared
                 rounds, and its block passes its test on the plan
  `facts_head_W`, `k_head_W`   so the seven tests hold at the seated place; its first stage has k =
                 5
  `find_own_at`, `find_own`   the first block of the description's second list at the test's place
                 has the declared rounds and oracle messages of the test's own block
  `first_any_head_W`   the statement

By what. `k12_sits_row` (Johnson/Loose/H2K12/SitsRow.lean); `place_W_of_full`, `more_W_of_full`
(Johnson/Desc/K12/Law/Sizes/), `rounds_at_seat_W`, `plan_at_seat_W` (Johnson/Loose/H2K12/);
`ownEntry_place` (Johnson/Loose/H2K12/SitsRowKey.lean), `place_of_p12At`
(Johnson/Desc/K12/Law/SharedPlaces.lean), `seat_in_scope`
(Johnson/Goal/Numbers/PlanWrittenDescScope.lean), `atFull_of_pubPlain`
(Johnson/Loose/H2K12/AtFullPlain.lean); `thin_of_reads` (Sim/ThinOfReads.lean). `maxRecDepth` is
raised at two evaluations, as at the test on G_u.

Limits.
- At this place no job is typed at all. "At every job at the place" says nothing on whether any job
  there is the prover's. Who owns the fresh table that came earlier is not named: the job's field is
  any address. By the written place's list of first openings all three
  trees that the first reading round opens are taken from other chains: so whoever sent that table
  stands outside this chain. Nothing here says whether a book can lend its run to this part as
  spent.
- At this place there is no negative test and no small plan.
- All limits of Sim/FirstAnyAtPlace.lean stand. Among them: "every job" takes in jobs of which the
  sentence says nothing of any run, and no book is asked. The challenges are one list written by
  hand. The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Loose.H2K12.SitsRowKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piWFull)
open H2K.JointK (laidOf descN pOwn ownEntry)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 At the written place -/

/-- Seven challenges, each of one field element. -/
def dsW : List Fmt.Drawn := List.replicate 7 ⟨[(1, 0, 0)], [], [], none⟩

set_option maxRecDepth 100000 in
theorem formPubB_W : formPubB piWFull = true := by decide +kernel

theorem enough_W : firstLen piWFull.nums.stages ≤ (laidOf piWFull).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabB_W : tabB piWFull false = true := by decide +kernel

theorem count_WFull : (laidOf piWFull).length =
    firstLen piWFull.nums.stages + restLen piWFull.nums.stages := by decide +kernel

theorem quiet_WFull :
    quietB (((laidOf piWFull).take (firstLen piWFull.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_WFull :
    drawsFit (((laidOf piWFull).take (firstLen piWFull.nums.stages)).map (·.1)) dsW = true := by
  decide +kernel

theorem facts_WFull : PlaceFacts piWFull dsW :=
  ⟨VerifiableInference.Desc.K12.Coin.At.closed_WFull.plan, formPubB_W, enough_W, tabB_W,
    count_WFull, quiet_WFull, draws_WFull⟩

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem reads_head_W (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).W.nums.stages = piWFull.nums.stages ∧
    (fourOf Np).W.nums.ownMask = piWFull.nums.ownMask ∧
    H2U.roundsOfNums (fourOf Np).W.nums = H2U.roundsOfNums piWFull.nums ∧
    (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).planOk = true := by
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
  exact ⟨(congrArg (·.stages) nW).trans (H2K.Sizes.place_W_of_full A h.laid.places).1,
    (congrArg (·.ownMask) nW).trans (H2K.Sizes.more_W_of_full A h.laid.places).2.1,
    (congrArg H2U.roundsOfNums nW).trans
      (H2K.JointK.rounds_at_seat_W o Z' ProofFile.pureRoad.links N' c' h.laid.places hp A hW),
    H2K.JointK.plan_at_seat_W o Z' ProofFile.pureRoad.links N' c' hp⟩

theorem facts_head_W (h : P5J.AtMg o Z D r Zp Np cF) : PlaceFacts (fourOf Np).W dsW := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_W h
  exact facts_carry h1 (thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_WFull.plan) h4 facts_WFull

/-- Under the head the first stage of the seated place has k = 5. -/
theorem k_head_W (h : P5J.AtMg o Z D r Zp Np cF) :
    ((fourOf Np).W.nums.stages.headD default).k = 5 := by
  rw [(reads_head_W h).1]
  rfl

/-- At a description that is `descN`: the first block of its second list at the place of the own
test. F is a letter, so that the blocks' types can follow it. -/
theorem find_own_at {mk : ProofFile.LinksBy} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst) (hF : F = descN o mk guardedProximityTestParts Zp N c)
    (R : H2K.JointK.RowK12 o mk Zp N c) :
    ∃ b, (F.second.blocksInOrder.find? fun b => b.place == (⟨3, none, 2, .K12⟩ : Place)) = some b ∧
      b.place = ⟨3, none, 2, .K12⟩ ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pOwn N) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pOwn N) : Block T12 Unit).oracles := by
  subst hF
  have hpl : (ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Block T12 Unit)).place =
      ⟨3, none, 2, .K12⟩ := H2K.JointK.ownEntry_place ProofFile.Cl N.W
  cases hf : (descN o mk guardedProximityTestParts Zp N c).second.blocksInOrder.find?
      fun b => b.place == (⟨3, none, 2, .K12⟩ : Place) with
  | none =>
    have := List.find?_eq_none.1 hf _ R.own.1
    rw [hpl] at this
    exact (this (by simp)).elim
  | some b =>
    have hb : b.place = ⟨3, none, 2, .K12⟩ := by simpa using List.find?_some hf
    obtain rfl := R.own.2.2 b (List.mem_of_find?_eq_some hf) (by rw [hb])
    exact ⟨_, rfl, hb, rfl, rfl⟩

theorem find_own (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ b, ((P5J.F0T o Zp Np cF).second.blocksInOrder.find? fun b => b.place == (fourOf Np).W.place) =
        some b ∧
      b.place = (fourOf Np).W.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).oracles := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hpl : (fourOf N').W.place = ⟨3, none, 2, .K12⟩ := H2K.JointK.place_of_p12At _ _
  rw [hpl]
  exact find_own_at (P5J.F0T o Z' N' cF) e R

/-! ## 3 The statement -/

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **Under the head, at every job at the place of the second chain's own test.** -/
theorem first_any_head_W {V W X Pb : Type} (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).W) (ho : Js.own = false) :
    FirstPub J Js ∧
    (∀ fs : List (Fall (P5J.F0T o Zp Np cF).S₃),
      ∃ σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V W X Pb,
        testSide (P5J.F0T o Zp Np cF).second.blocksInOrder J Js fs = some σ) ∧
    ∀ (fs : List (Fall (P5J.F0T o Zp Np cF).S₃))
      (σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V W X Pb),
      testSide (P5J.F0T o Zp Np cF).second.blocksInOrder J Js fs = some σ →
      σ.fits = true ∧
      σ.members = [firstMember J Js, restMember J Js] ∧
      (∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
        (testOn φ J Js) (testBud Js) (firstMember J Js)) ∧
      firstMember J Js ∈ σ.members ∧
      ∀ (φ : Face V W Pb) (chain firstTree : ℕ)
        (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
        (asks : List (List (List ℕ))),
        testOn φ J Js (firstMember J Js) ca m (bareFront chain m) ∧
        m.seen = (bareFront chain m).seen ∧
        drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsW = true ∧
        testBud Js (firstMember (V := V) J Js).number dsW asks ∧
        (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
          dsW = true ∧
        (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsW ≠ some .hid ∧
        (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m dsW asks = some l ∧
          scalars l = 2 * J.s₀.k + 1 ∧ columns l = 0) ∧
        (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
            CsAll (firstMember (V := V) J Js).part.spends)).map
            (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsW asks) =
          (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
            (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsW asks := by
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_own h
  rw [← hJ] at hf hpl hr hor hs
  exact any_at_place J Js (hJ ▸ facts_head_W h) _ b hf hpl hr hor hfr hs ho

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dsW
#print axioms ProofFile.Honest.K12.Light.formPubB_W
#print axioms ProofFile.Honest.K12.Light.enough_W
#print axioms ProofFile.Honest.K12.Light.tabB_W
#print axioms ProofFile.Honest.K12.Light.count_WFull
#print axioms ProofFile.Honest.K12.Light.quiet_WFull
#print axioms ProofFile.Honest.K12.Light.draws_WFull
#print axioms ProofFile.Honest.K12.Light.facts_WFull
#print axioms ProofFile.Honest.K12.Light.reads_head_W
#print axioms ProofFile.Honest.K12.Light.facts_head_W
#print axioms ProofFile.Honest.K12.Light.k_head_W
#print axioms ProofFile.Honest.K12.Light.find_own_at
#print axioms ProofFile.Honest.K12.Light.find_own
#print axioms ProofFile.Honest.K12.Light.first_any_head_W
