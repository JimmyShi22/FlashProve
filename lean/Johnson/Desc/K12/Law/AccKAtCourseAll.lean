-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtCourse
import Johnson.Desc.K12.Law.TieOkMade
import Johnson.Desc.K12.Law.OwnMaskStep
import Johnson.Desc.PlanPasses
/-
Johnson/Desc/K12/Law/AccKAtCourseAll.lean: Johnson/Desc/K12/Law/AccKAtCourse.lean's course_atSeat | course_atSeat_own IN ONE STATEMENT, WITH EVERY PREMISE STRUCK THAT HAS BECOME A THEOREM; and the same FROM A YES OF A WRITTEN DESCRIPTION's DECISION (FileDescription.runEnd), where the kind's block's own test on the plan falls too. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS: AN ASSEMBLY.
STRUCK, AND BY WHAT: nzOk · dealOk · tieOk · logOk · ownTieOk: theorems of the frame's own test on the plan (‹x›Ok_of_planOk: Johnson/Desc/K12/Law/DealMade.lean · EntriesMade.lean · TieOkMade.lean, over MadeRounds.lean) · lastOk · aloneAt at the record behind the batching: of the step's yes (Johnson/Desc/K12/Law/OwnSeatStep.lean) · t0.mask = none, where the fold sends its own mask: of the step's yes (hmask_of_step: Johnson/Desc/K12/Law/OwnMaskStep.lean) · the batching's yes: k12_guards · canonOk: of viewWordsBelowPrime at the whole view (Johnson/Desc/K12/Law/CanonOfView.lean | CanonAtFold.lean) · AT A DESCRIPTION: planOk of the block in the list: runEnd_blocks (Johnson/Desc/PlanPasses.lean).
  YesAll X p F t0 r0 rs' cols     YesConst … ∧ (p.nums.ownMask = true → t0.mask = none ∧ YesOwn …): BOTH elder tops' whole conclusions; the own arm's where the place's numbers say that the first fold sends its own mask.
  yesAll_of_step       early · one answer · planOk · canonOk of the stretch · the kind's block's step's yes ⇒ the stretch is r0 :: rs' ∧ YesAll.
  step_same2 · seat_step2     as step_same | seat_step, with the list's block and the kind's block over two types of claims: Block.step reads neither.
  fold_cols_drop       the columns that a fold leaves are a tail of those that it was handed (block by block, by foldConsOk').
  AtSeatAll X p ft bs s s' v  AtSeat's text at Y := YesAll, GENERAL IN THE LIST's TYPE OF CLAIMS, with a third thing asked of the block B in the list: B.planOk = true → the kind's block's planOk = true; and one conjunct more: cols IS A TAIL OF THE VIEW's OPENED COLUMNS (∃ j, cols = v.opened.drop j).
  atSeatAll_of_steps   StepsAt and «every block of the list passes its test on the plan» ⇒ AtSeatAll.
  course_atSeat_all    runCore's yes · every block's planOk · early · one answer ⇒ AtSeatAll at each of the three chains.
  run_atSeat_all       F.runEnd x v₁ v₂ v₃ = .ok e · early · one answer ⇒ AtSeatAll at F's three flat lists, from F's own first records, at the three views. NO OTHER PREMISE.
  seat_planOk          laid by Chain.blocksInOrder, a seat's yes on the plan gives the inner block's: the third thing is paid at every seat of the form Block.inside.
No sorry and no axiom of our own stands in this file.
NO MEMBER IS SHOWN AT A REAL p.
WHAT IS LEFT AS PREMISES. (1) INSIDE AtSeatAll: the cut bs = pre ++ B :: l, and of B: its rounds are the kind's block's, its decision the kind's block's behind a door, its yes on the plan gives the kind's block's. AT THE FOUR WRITTEN SEATS THESE THREE ARE ⟨rfl, rfl⟩ AND seat_planOk (Johnson/Desc/K12/Law/AccKAtFinish.lean · AccKAtSeats.lean); THAT A WRITTEN DESCRIPTION's FLAT LIST HOLDS THE SEAT AT SOME CUT IS SHOWN BY NOBODY. Where no such B stands, AtSeatAll says nothing: SO OVER A DESCRIPTION WHOSE FLAT LIST HOLDS THE SEATS WRAPPED ONCE MORE (a variant of the driver: Block.guarded: the decision bound to a further test) the equation on B's decision is no rfl, and AtSeatAll is idle there until that wrap has a lemma of its own. (2) p.early = true · p.answers = 1.
LIMITS. (a) IT CARRIES A YES, NOT A PRICE: from the decision's course to «accK says yes at a typed transcript»: τ and W0 stand UNDER «THERE IS» in YesConst | YesOwn: these are the ∃-tops. A bound on chances is to ride on the form with τ and the tables GIVEN: that form is called at the seat in Johnson/Desc/K12/Law/AccKGivenAtCourse.lean, thin as its head says; no bound is carried there either. (b) "BAT"'s own round is outside τ. (c) Nothing on Doomed, on the library's game, on what a false claim costs.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (canonOk)
open H2K.Made (dealOk_of_planOk nzOk_of_planOk logOk_of_planOk tieOk_of_planOk ownTieOk_of_planOk)

/-- Both elder tops' whole conclusions: the constant arm's; and, where the first fold sends its own mask, that the record in front names no mask, and the own arm's. -/
def YesAll (X : Letters) (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) : Prop :=
  YesConst X p F t0 r0 rs' cols ∧
    (p.nums.ownMask = true → t0.mask = none ∧ YesOwn X p F t0 r0 rs' cols)

theorem yesAll_of_step (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 : T12) (F : ℕ) (mine : List Fmt.RoundView)
    (cols : List OpenedColumn) (hcan : canonOk mine = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 mine cols = .ok (tE, n)) :
    ∃ r0 rs', mine = r0 :: rs' ∧ YesAll X p F t0 r0 rs' cols := by
  have hnz := nzOk_of_planOk guardedProximityTestParts p hp
  have hdeal := dealOk_of_planOk guardedProximityTestParts p hp
  have htie := tieOk_of_planOk guardedProximityTestParts p hp
  have hlog := logOk_of_planOk guardedProximityTestParts p hp
  obtain ⟨r0, rs', rfl, hc⟩ :=
    yesConst_of_step X p he ha hp hnz hdeal htie hlog t0 F mine cols hcan tE n hstep
  refine ⟨r0, rs', rfl, hc, fun ho => ?_⟩
  have hm := hmask_of_step p he t0 tE F n r0 rs' cols hp hstep ho
  obtain ⟨r1, rs1, e, hy⟩ := yesOwn_of_step X p he ha hp hnz hdeal htie hlog ho
    (ownTieOk_of_planOk guardedProximityTestParts p hp) t0 F (r0 :: rs') cols hcan tE n hstep
  cases e
  exact ⟨hm, hy hm⟩

theorem step_same2 {S Cl Cl' : Type} (B : Block S Cl) (B' : Block S Cl') (hr : B.rounds = B'.rounds)
    (hd : B.decide = B'.decide) (F : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    B.step F s rs cols = B'.step F s rs cols := by
  unfold Block.step
  rw [hr, hd]

theorem seat_step2 {S T Cl Cl' : Type} (B : Block S Cl) (enter : S → Except String T)
    (b : Block T Cl') (leave : S → T → Except String S) (hr : B.rounds = b.rounds)
    (hd : B.decide = (Block.inside enter b leave).decide) (F : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : ℕ) (h : B.step F s rs cols = .ok (s', k)) :
    ∃ t t', enter s = .ok t ∧ b.step F t rs cols = .ok (t', k) ∧ leave s t' = .ok s' := by
  rw [step_same2 B (Block.inside enter b leave) hr hd] at h
  exact (inside_step enter b leave F s s' rs cols k).1 h

/-- The columns that a fold leaves are a tail of the columns that it was handed. -/
theorem fold_cols_drop {S Cl : Type} (ft : ℕ) : ∀ (bs : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft bs s rs cols = .ok out → ∃ j, out.2.2 = cols.drop j := by
  intro bs
  induction bs with
  | nil =>
    intro s rs cols out h
    have e : (s, rs, cols) = out := Except.ok.inj h
    exact ⟨0, by rw [← e]; rfl⟩
  | cons b l ih =>
    intro s rs cols out h
    obtain ⟨s', k, _, _, h2⟩ := foldConsOk' h
    obtain ⟨j, hj⟩ := ih s' _ _ out h2
    exact ⟨k + j, by rw [hj, List.drop_drop]⟩

/-- What is said of a chain's list of blocks, from s to s' at the view v, at every seat of the kind's block at p in it. -/
def AtSeatAll (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl)) (s s' : S)
    (v : Fmt.View) : Prop :=
  ∀ (pre : List (Block S Cl)) (B : Block S Cl) (l : List (Block S Cl))
    (enter : S → Except String T12) (leave : S → T12 → Except String S),
    bs = pre ++ B :: l → B.rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds →
    B.decide = (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave).decide →
    (B.planOk = true → (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) →
    ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
      (t : S),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
      (∃ j, cols = v.opened.drop j) ∧
      enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
      (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
      foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
        .ok (s', [], []) ∧
      YesAll X p ft t0 r0 rs' cols

theorem atSeatAll_of_steps (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (hpl : ∀ b ∈ bs, b.planOk = true) (h : H2K.First.StepsAt ft bs s s' v) :
    AtSeatAll X p ft bs s s' v := by
  intro pre B l enter leave hb hr hd hpB
  obtain ⟨m, cols, t, k, h0, h1, h2, h3⟩ := h pre B l hb
  have hp := hpB (hpl B (by rw [hb]; simp))
  obtain ⟨t0, tE, e1, e2, e4⟩ := seat_step2 B enter _ leave hr hd ft m t _ cols k h1
  obtain ⟨r0, rs', e3, hy⟩ := yesAll_of_step X p he ha hp t0 ft _ cols h3 tE k e2
  exact ⟨m, t0, r0, rs', cols, tE, k, t, h0, fold_cols_drop ft pre s _ _ _ h0, e1, e3, e3 ▸ e2, e4,
    h2, hy⟩

/-- From a yes of the decision's course. -/
theorem course_atSeat_all (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    {Cl S₁ S₂ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : S₁) (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : ℕ)
    (b₁ : List (Block S₁ Cl)) (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl))
    (fin : S₁ → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h1 : ∀ b ∈ b₁, b.planOk = true) (h2 : ∀ b ∈ b₂, b.planOk = true)
    (h3 : ∀ b ∈ b₃, b.planOk = true)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    AtSeatAll X p 0 b₁ s₁ e.1 (withEmptySealRound v₁) ∧ AtSeatAll X p 0 b₂ s₂ e.2.1 v₂ ∧
      ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧ AtSeatAll X p ft b₃ s₃ e.2.2 v₃ := by
  obtain ⟨a1, a2, s₃, hs, a3⟩ := H2K.First.runCore_steps_canon _ _ _ _ _ _ _ _ _ _ _ _ _ e h
  exact ⟨atSeatAll_of_steps X p he ha 0 _ _ _ _ h1 a1, atSeatAll_of_steps X p he ha 0 _ _ _ _ h2 a2,
    s₃, hs, atSeatAll_of_steps X p he ha ft _ _ _ _ h3 a3⟩

/-- FROM A YES OF A WRITTEN DESCRIPTION's DECISION: at every seat of the kind's block at p in each of its three flat lists. -/
theorem run_atSeat_all (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok e) :
    AtSeatAll X p 0 F.first.blocksInOrder (F.start₁ (F.pub x)) e.1 (withEmptySealRound v₁) ∧
      AtSeatAll X p 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) e.2.1 v₂ ∧
      ∃ s₃, F.start₃ (F.pub x) e.1 e.2.1 = .ok s₃ ∧
        AtSeatAll X p F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ e.2.2 v₃ := by
  obtain ⟨h1, h2, h3⟩ := Keeps.runEnd_blocks F x v₁ v₂ v₃ e h
  exact course_atSeat_all X p he ha _ _ _ _ _ _ _ _ _ _ v₁ v₂ v₃ e h1 h2 h3 h

/-- Laid by Chain.blocksInOrder, a seat's yes on the plan gives the inner block's. -/
theorem seat_planOk {S T Cl : Type} (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S)
    (h : ({ Block.inside enter b leave with
      planOk := (Block.inside enter b leave).planOk && (Block.inside enter b leave).hasNoClaimsAndNothingAfter } :
        Block S Cl).planOk = true) : b.planOk = true := by
  simp only [Block.inside, Bool.and_eq_true] at h
  exact h.1.1.1

end H2K.JointK

#print axioms H2K.JointK.yesAll_of_step
#print axioms H2K.JointK.seat_step2
#print axioms H2K.JointK.atSeatAll_of_steps
#print axioms H2K.JointK.course_atSeat_all
#print axioms H2K.JointK.run_atSeat_all
#print axioms H2K.JointK.seat_planOk
