-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/FirstAnyAtHeadL.lean: `any_at_place`
(Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyAtPlace.lean) under the library's head (`P5J.AtMg`),
at the place at which the proof file's description seats the first chain's last proximity test,
`(fourOf Np).L`, off the description's own first list: at every job at that place.

  `dsL`          three challenges, each the one field element (1, 0, 0)
  `facts_LFull`  the seven public tests at the written place `piLFull`: six evaluated by Lean's
                 kernel, the block's test on the plan from the library's `closed_LFull`
  `reads_head_L`   under the head the seated place has the written place's stages, flag and declared
                 rounds, and its block passes its test on the plan
  `facts_head_L`, `k_head_L`   so the seven tests hold at the seated place; its first stage has k =
                 1
  `find_last_at`, `find_last`   the first block of the description's first list at the test's place
                 has the declared rounds and oracle messages of the test's own block
  `first_any_head_L`   the statement

Why in the side library. The side library stands already beneath "under the head" here
(`reads_head_L`). That the record's stages of this test are the typed list is shown in the
main library under a premise on the layout file's lines on groups; that premise is a theorem here
(`layoutGroupsAre`, AtFullSide/LayoutRead/GroupsPaid.lean).

By what. `k12_sits` (Johnson/Loose/H2K12/SitsAtDescPure.lean); `stages_of_pubPlain`
(Johnson/Loose/H2K12/ChainAtLast.lean); `place_L_of_full` (Johnson/Desc/K12/Law/Sizes/),
`places_ownL` (Johnson/Desc/K12/Law/StretchLast.lean), `rounds_at_seat_L`, `plan_at_seat_L`
(Johnson/Loose/H2K12/CondAtLast.lean); `thin_of_reads` (Sim/ThinOfReads.lean). `maxRecDepth` is
raised at two evaluations, as at the test on G_u.

Limits.
- At this place no job is typed at all. "At every job at the place" says nothing on whether any job
  there is the prover's. Who owns the fresh table that came earlier is not named: the job's field is
  any address.
- At this test "every job" may hold no job whose state on entry is the verifier's at an honest run.
  By reading, no theorem (the head of Sim/Row.lean under Johnson/Desc/ProofFile/Honest/K12/): the
  verifier's state there holds targets that are symbols of opened columns of the run's own messages,
  and a job's state function is handed no random value and no column. The law beneath holds at every
  claim's row, so it is untouched.
- At this place there is no negative test and no small plan.
- All limits of Sim/FirstAnyAtPlace.lean stand. Among them: "every job" takes in jobs of which the
  sentence says nothing of any run, and no book is asked. The challenges are one list written by
  hand. The full size alone. No example of the head is shown here.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Loose.H2K12.ChainAtLast
import AtFullSide.LayoutRead.GroupsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piLFull)
open H2K.JointK (laidOf descN pL firstEntry firstCore FirstJ)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 At the written place -/

/-- Three challenges, each of one field element. -/
def dsL : List Fmt.Drawn := List.replicate 3 ⟨[(1, 0, 0)], [], [], none⟩

set_option maxRecDepth 100000 in
theorem formPubB_L : formPubB piLFull = true := by decide +kernel

theorem enough_L : firstLen piLFull.nums.stages ≤ (laidOf piLFull).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabB_L : tabB piLFull false = true := by decide +kernel

theorem count_LFull : (laidOf piLFull).length =
    firstLen piLFull.nums.stages + restLen piLFull.nums.stages := by decide +kernel

theorem quiet_LFull :
    quietB (((laidOf piLFull).take (firstLen piLFull.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_LFull :
    drawsFit (((laidOf piLFull).take (firstLen piLFull.nums.stages)).map (·.1)) dsL = true := by
  decide +kernel

theorem facts_LFull : PlaceFacts piLFull dsL :=
  ⟨VerifiableInference.Desc.K12.Coin.At.closed_LFull.plan, formPubB_L, enough_L, tabB_L,
    count_LFull, quiet_LFull, draws_LFull⟩

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem reads_head_L (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).L.nums.stages = piLFull.nums.stages ∧
    (fourOf Np).L.nums.ownMask = piLFull.nums.ownMask ∧
    H2U.roundsOfNums (fourOf Np).L.nums = H2U.roundsOfNums piLFull.nums ∧
    (proximityTestKind guardedProximityTestParts (fourOf Np).L : Block T12 Unit).planOk = true := by
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
  have pk := H2K.JointK.plan_at_seat_L o Z' ProofFile.pureRoad.links N' c' hp ProofFile.sameReply pre l J₀ hb
    hJ₀
  have nL : (pL N').nums = N'.L.nums := H2K.Made.nums_of_planOk _ N'.L pk
  exact ⟨(congrArg (·.stages) nL).trans (H2K.Sizes.place_L_of_full A h.laid.places hL).1,
    (congrArg (·.ownMask) nL).trans (H2K.Member.places_ownL Z'.made N' h.laid.places),
    (congrArg H2U.roundsOfNums nL).trans
      (H2K.JointK.rounds_at_seat_L o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
        h.laid.places hp A hL hW ProofFile.sameReply pre l J₀ hb hJ₀), pk⟩

theorem facts_head_L (h : P5J.AtMg o Z D r Zp Np cF) : PlaceFacts (fourOf Np).L dsL := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_L h
  exact facts_carry h1 (thin_of_reads guardedProximityTestParts h1 h2 h3 h4 facts_LFull.plan) h4 facts_LFull

/-- Under the head the first stage of the seated place has k = 1. -/
theorem k_head_L (h : P5J.AtMg o Z D r Zp Np cF) :
    ((fourOf Np).L.nums.stages.headD default).k = 1 := by
  rw [(reads_head_L h).1]
  rfl

/-- At a description that is `descN`: the first block of its first list at the place of the last
test. F is a letter, so that the blocks' types can follow it. -/
theorem find_last_at {mk : ProofFile.LinksBy} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst) (hF : F = descN o mk guardedProximityTestParts Zp N c)
    (J₀ : Block VerifiableInference.Desc.First.S ProofFile.Cl)
    (hmem : firstEntry ProofFile.sameReply J₀ ∈ c.blocksInOrder)
    (honly : ∀ E ∈ c.blocksInOrder, E.place.kind = .K12 → E = firstEntry ProofFile.sameReply J₀)
    (hJ₀ : FirstJ (pL N) J₀) :
    ∃ b, (F.first.blocksInOrder.find? fun b => b.place == (⟨1, none, 2, .K12⟩ : Place)) = some b ∧
      b.place = ⟨1, none, 2, .K12⟩ ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pL N) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pL N) : Block T12 Unit).oracles := by
  subst hF
  obtain ⟨nm, rfl⟩ := hJ₀
  have hpl : (firstEntry ProofFile.sameReply (firstCore (pL N) nm)).place = ⟨1, none, 2, .K12⟩ := rfl
  cases hf : (descN o mk guardedProximityTestParts Zp N c).first.blocksInOrder.find?
      fun b => b.place == (⟨1, none, 2, .K12⟩ : Place) with
  | none =>
    have := List.find?_eq_none.1 hf _ hmem
    rw [hpl] at this
    exact (this (by simp)).elim
  | some b =>
    have hb : b.place = ⟨1, none, 2, .K12⟩ := by simpa using List.find?_some hf
    obtain rfl := honly b (List.mem_of_find?_eq_some hf) (by rw [hb])
    exact ⟨_, rfl, hb, rfl, rfl⟩

theorem find_last (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ b, ((P5J.F0T o Zp Np cF).first.blocksInOrder.find? fun b => b.place == (fourOf Np).L.place) =
        some b ∧
      b.place = (fourOf Np).L.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (fourOf Np).L : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (fourOf Np).L : Block T12 Unit).oracles := by
  obtain ⟨Z', N', c', _, hZ', hN', e, _, pre, l, J₀, hb, honly, hJ₀⟩ :=
    H2K.JointK.k12_sits o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hpl : (fourOf N').L.place = ⟨1, none, 2, .K12⟩ := H2K.JointK.place_of_p12At _ _
  rw [hpl]
  exact find_last_at (P5J.F0T o Z' N' cF) e J₀
    (by rw [hb]; exact List.mem_append_right _ List.mem_cons_self) honly hJ₀

/-! ## 3 The statement -/

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **Under the head, at every job at the place of the first chain's last test.** -/
theorem first_any_head_L {V W X Pb : Type} (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).L) (ho : Js.own = false) :
    FirstPub J Js ∧
    (∀ fs : List (Fall (P5J.F0T o Zp Np cF).S₁),
      ∃ σ : Side (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl V W X Pb,
        testSide (P5J.F0T o Zp Np cF).first.blocksInOrder J Js fs = some σ) ∧
    ∀ (fs : List (Fall (P5J.F0T o Zp Np cF).S₁))
      (σ : Side (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl V W X Pb),
      testSide (P5J.F0T o Zp Np cF).first.blocksInOrder J Js fs = some σ →
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
        drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsL = true ∧
        testBud Js (firstMember (V := V) J Js).number dsL asks ∧
        (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
          dsL = true ∧
        (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsL ≠ some .hid ∧
        (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m dsL asks = some l ∧
          scalars l = 2 * J.s₀.k + 1 ∧ columns l = 0) ∧
        (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
            CsAll (firstMember (V := V) J Js).part.spends)).map
            (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsL asks) =
          (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
            (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsL asks := by
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_last h
  rw [← hJ] at hf hpl hr hor hs
  exact any_at_place J Js (hJ ▸ facts_head_L h) _ b hf hpl hr hor hfr hs ho

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dsL
#print axioms ProofFile.Honest.K12.Light.formPubB_L
#print axioms ProofFile.Honest.K12.Light.enough_L
#print axioms ProofFile.Honest.K12.Light.tabB_L
#print axioms ProofFile.Honest.K12.Light.count_LFull
#print axioms ProofFile.Honest.K12.Light.quiet_LFull
#print axioms ProofFile.Honest.K12.Light.draws_LFull
#print axioms ProofFile.Honest.K12.Light.facts_LFull
#print axioms ProofFile.Honest.K12.Light.reads_head_L
#print axioms ProofFile.Honest.K12.Light.facts_head_L
#print axioms ProofFile.Honest.K12.Light.k_head_L
#print axioms ProofFile.Honest.K12.Light.find_last_at
#print axioms ProofFile.Honest.K12.Light.find_last
#print axioms ProofFile.Honest.K12.Light.first_any_head_L
