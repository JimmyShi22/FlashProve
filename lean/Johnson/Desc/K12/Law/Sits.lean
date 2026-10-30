-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtCourseAll3
import Johnson.Desc.SeatGuard
import Johnson.Desc.BlockLaws
import Johnson.Top.H0.StepLaws.StepLaws
/-
Johnson/Desc/K12/Law/Sits.lean: A SEAT AT THE STEP. A block B of a chain's list SITS on a block K
behind a door (enter, leave): B declares K's rounds; B's yes on the plan gives K's; and wherever B's
step says yes, the door lets in, K's step says yes at the same rounds and columns and takes as many
columns, and the way out gives B's record. It is wider than IsSeat
(Johnson/Desc/K12/Law/AccKSeatsAll.lean), which asks an equation of decisions: so it also holds of a
seat behind which a block without a round is joined (Block.andThen hands its first block a cut of
the rounds: no equation of decisions as functions of all lists; at the step, where the rounds fit,
the two agree). NO SOUNDNESS IS CLAIMED. NOTHING ON
HIDING. NO NEW MATHEMATICS.
  Sits B K enter leave     the three things. GENERAL IN K: no word of the proximity test stands in
      it.
  sits_inside              Block.inside enter K leave sits on K behind its own door (by
      inside_step).
  Sits.same                a block with B's rounds and decision whose yes on the plan gives B's sits
      as B does: another name, another place, another type of claims (Block.retype), Chain.blocksInOrder's
      further test on the plan (Block.asBare).
  Sits.behind              a block with B's rounds whose decision is B's with a test g bound behind
      it (g is handed the record in front and the record behind): it sits behind the way out with g
      bound behind it: a guard on a mark; Block.guarded at a place that the guard does not leave
      free.
  Sits.retype · Sits.asBare · Sits.guarded · Sits.withRoundlessBlockBehind     the four named wrappers: by the two
      above; the last by andThen_step_noRound.
  isSeat_sits              IsSeat B p enter leave gives Sits B (proximityTestKind guardedProximityTestParts p) enter leave.
  atCut_of_sits            StepsAt, every block's yes on the plan, a cut of the list with a B that
      sits on proximityTestKind guardedProximityTestParts p: AtCut there (atSeatAll_of_steps3's proof, with the step's clause in
      seat_step2's place).
  run_atCut1 | run_atCut2 | run_atCut3     F.runEnd's yes, a cut of F's first | shared | second flat
      list with such a B: AtCut. NO OTHER PREMISE.
No sorry and no axiom of our own stands in this file.
LIMITS. ONE DIRECTION: from B's yes to K's; that B says yes wherever K does is not said and is false
behind a guard. Nothing is said of B's oracles, «before», name or place. That a written
description's list holds such a B: Johnson/Desc/K12/Law/SitsChains.lean and a file over the
seat. All limits of AccKAtCourseAll.lean | AccKGivenAtCourse.lean: A YES, NOT A PRICE.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)

/-- **A seat at the step.** -/
structure Sits {S T Cl Cl' : Type} (B : Block S Cl) (K : Block T Cl')
    (enter : S → Except String T) (leave : S → T → Except String S) : Prop where
  rounds : B.rounds = K.rounds
  plan : B.planOk = true → K.planOk = true
  step : ∀ (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ),
    B.step ft s rs cols = .ok (s', k) →
      ∃ t t', enter s = .ok t ∧ K.step ft t rs cols = .ok (t', k) ∧ leave s t' = .ok s'

theorem sits_inside {S T Cl : Type} (enter : S → Except String T) (K : Block T Cl)
    (leave : S → T → Except String S) : Sits (Block.inside enter K leave) K enter leave where
  rounds := rfl
  plan := fun h => by
    simp only [Block.inside, Bool.and_eq_true] at h
    exact h.1.1
  step := fun ft s s' rs cols k h => (inside_step enter K leave ft s s' rs cols k).1 h

/-- Another name, place, type of claims, or a further test on the plan. -/
theorem Sits.same {S T Cl Cl' Cl'' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (B' : Block S Cl'') (hr : B'.rounds = B.rounds) (hd : B'.decide = B.decide)
    (hp : B'.planOk = true → B.planOk = true) : Sits B' K enter leave where
  rounds := hr.trans h.rounds
  plan := fun a => h.plan (hp a)
  step := fun ft s s' rs cols k a =>
    h.step ft s s' rs cols k (step_same2 B' B hr hd ft s rs cols ▸ a)

/-- The step of a block whose decision is another's with a test bound behind it. -/
theorem step_behind {S Cl Cl' : Type} (B : Block S Cl) (B' : Block S Cl')
    (g : S → S → Except String S) (hr : B'.rounds = B.rounds)
    (hd : ∀ s rs gs, B'.decide s rs gs = (B.decide s rs gs).bind (g s)) (ft : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ) (h : B'.step ft s rs cols = .ok (s', k)) :
    ∃ m, B.step ft s rs cols = .ok (m, k) ∧ g s m = .ok s' := by
  obtain ⟨hf, hdec, hk⟩ := (step_iff ft B' s s' rs cols k).1 h
  rw [hd] at hdec
  obtain ⟨m, h1, h2⟩ := (Except.bind_eq_ok _ _ _).1 hdec
  refine ⟨m, (step_iff ft B s m rs cols k).2 ⟨?_, ?_, ?_⟩, h2⟩
  · simpa only [Block.Fits, Block.want, hr] using hf
  · simpa only [Block.shown, Block.want, hr] using h1
  · simpa only [Block.want, hr] using hk

/-- A test bound behind the decision goes into the way out. -/
theorem Sits.behind {S T Cl Cl' Cl'' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (B' : Block S Cl'') (g : S → S → Except String S) (hr : B'.rounds = B.rounds)
    (hd : ∀ s rs gs, B'.decide s rs gs = (B.decide s rs gs).bind (g s))
    (hp : B'.planOk = true → B.planOk = true) :
    Sits B' K enter (fun s t => (leave s t).bind (g s)) where
  rounds := hr.trans h.rounds
  plan := fun a => h.plan (hp a)
  step := fun ft s s' rs cols k a => by
    obtain ⟨m, h1, h2⟩ := step_behind B B' g hr hd ft s s' rs cols k a
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft s m rs cols k h1
    exact ⟨t, t', e1, e2, (Except.bind_eq_ok _ _ _).2 ⟨m, e3, h2⟩⟩

theorem Sits.retype {S T Cl Cl' Cl'' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave) :
    Sits (B.retype (Cl' := Cl'')) K enter leave :=
  h.same _ rfl rfl fun a => by
    simp only [Block.retype, Bool.and_eq_true] at a
    exact a.1

theorem Sits.asBare {S T Cl Cl' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave) :
    Sits B.asBare K enter leave :=
  h.same _ rfl rfl fun a => by
    simp only [Block.asBare, Bool.and_eq_true] at a
    exact a.1

/-- Behind the guard on a seat of the record, at a place that the guard does not leave free. -/
theorem Sits.guarded {S T Cl Cl' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (same : S → S → Bool) (but : Place → Bool) (hb : but B.place = false) :
    Sits (B.guarded same but) K enter (fun s t => (leave s t).bind (seatSame same s)) :=
  h.behind _ (seatSame same) rfl (fun s rs gs => by simp only [Block.guarded, hb]; rfl) fun a => a

/-- A block without a round joined behind: its decision, on no round, goes into the way out. -/
theorem Sits.withRoundlessBlockBehind {S T Cl Cl' : Type} {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (name : String) (q : Block S Cl) (hq : q.rounds = []) :
    Sits (B.andThen name q) K enter (fun s t => (leave s t).bind fun m => q.decide m [] []) where
  rounds := by
    show B.rounds ++ q.rounds = K.rounds
    rw [hq, List.append_nil]
    exact h.rounds
  plan := fun a => by
    simp only [Block.andThen, Bool.and_eq_true] at a
    exact h.plan a.1
  step := fun ft s s' rs cols k a => by
    obtain ⟨m, h1, h2⟩ := (andThen_step_noRound name B q hq ft s s' rs cols k).1 a
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft s m rs cols k h1
    exact ⟨t, t', e1, e2, (Except.bind_eq_ok _ _ _).2 ⟨m, e3, h2⟩⟩

theorem isSeat_sits {S Cl : Type} (B : Block S Cl) (p : P12) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (h : IsSeat B p enter leave) :
    Sits B (proximityTestKind guardedProximityTestParts p : Blk') enter leave where
  rounds := h.1
  plan := h.2.2
  step := fun ft s s' rs cols k a => seat_step2 B enter _ leave h.1 h.2.1 ft s s' rs cols k a

/-- What AtSeatAll and the given form say at one cut with a seat, under a name. -/
def AtCut (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (pre : List (Block S Cl)) (B : Block S Cl)
    (l : List (Block S Cl)) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (s s' : S) (v : Fmt.View) : Prop :=
  ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
    (t : S),
    foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
    (∃ j, cols = v.opened.drop j) ∧
    enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
    (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
    foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
      .ok (s', [], []) ∧
    YesAll X p ft t0 r0 rs' cols ∧ GivenAt p ft t0 r0 rs' cols

theorem atCut_of_sits (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl))
    (s s' : S) (v : Fmt.View) (hpl : ∀ b ∈ bs, b.planOk = true)
    (h : H2K.First.StepsAt ft bs s s' v) (pre : List (Block S Cl)) (B : Block S Cl)
    (l : List (Block S Cl)) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hb : bs = pre ++ B :: l) (hB : Sits B (proximityTestKind guardedProximityTestParts p : Blk') enter leave) :
    AtCut X p ft pre B l enter leave s s' v := by
  obtain ⟨m, cols, t, k, h0, h1, h2, h3⟩ := h pre B l hb
  have hp := hB.plan (hpl B (by rw [hb]; simp))
  obtain ⟨t0, tE, e1, e2, e4⟩ := hB.step ft m t _ cols k h1
  obtain ⟨r0, rs', e3, hy⟩ := yesAll_of_step3 X p hp t0 ft _ cols h3 tE k e2
  exact ⟨m, t0, r0, rs', cols, tE, k, t, h0, fold_cols_drop ft pre s _ _ _ h0, e1, e3, e3 ▸ e2, e4,
    h2, hy, givenAt_of_step p ft t0 r0 rs' cols tE k (e3 ▸ e2)⟩

/-- The three chains' steps and tests on the plan, of a yes of a written description's decision. -/
theorem run_steps {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e) :
    ((∀ b ∈ F.first.blocksInOrder, b.planOk = true) ∧
      H2K.First.StepsAt 0 F.first.blocksInOrder (F.start₁ (F.pub x)) e.1 (withEmptySealRound v₁)) ∧
    ((∀ b ∈ F.shared.blocksInOrder, b.planOk = true) ∧
      H2K.First.StepsAt 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) e.2.1 v₂) ∧
    ∃ s₃, F.start₃ (F.pub x) e.1 e.2.1 = .ok s₃ ∧ (∀ b ∈ F.second.blocksInOrder, b.planOk = true) ∧
      H2K.First.StepsAt F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ e.2.2 v₃ := by
  obtain ⟨h1, h2, h3⟩ := Keeps.runEnd_blocks F x v₁ v₂ v₃ e h
  obtain ⟨a1, a2, s₃, hs, a3⟩ := H2K.First.runCore_steps_canon _ _ _ _ _ _ _ _ _ _ _ _ _ e h
  exact ⟨⟨h1, a1⟩, ⟨h2, a2⟩, s₃, hs, h3, a3⟩

/-- A yes of a written description's decision, at a cut of its FIRST chain's flat list. -/
theorem run_atCut1 (X : Letters) (p : P12) {Xi : Type} (F : FileDescription Xi)
    (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e)
    (pre : List (Block F.S₁ F.Cl)) (B : Block F.S₁ F.Cl) (l : List (Block F.S₁ F.Cl))
    (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (hb : F.first.blocksInOrder = pre ++ B :: l) (hB : Sits B (proximityTestKind guardedProximityTestParts p : Blk') enter leave) :
    AtCut X p 0 pre B l enter leave (F.start₁ (F.pub x)) e.1 (withEmptySealRound v₁) :=
  let a := (run_steps F x v₁ v₂ v₃ e h).1
  atCut_of_sits X p 0 _ _ _ _ a.1 a.2 pre B l enter leave hb hB

/-- The like at its SHARED chain. -/
theorem run_atCut2 (X : Letters) (p : P12) {Xi : Type} (F : FileDescription Xi)
    (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e)
    (pre : List (Block F.S₂ F.Cl)) (B : Block F.S₂ F.Cl) (l : List (Block F.S₂ F.Cl))
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (hb : F.shared.blocksInOrder = pre ++ B :: l) (hB : Sits B (proximityTestKind guardedProximityTestParts p : Blk') enter leave) :
    AtCut X p 0 pre B l enter leave (F.start₂ (F.pub x)) e.2.1 v₂ :=
  let a := (run_steps F x v₁ v₂ v₃ e h).2.1
  atCut_of_sits X p 0 _ _ _ _ a.1 a.2 pre B l enter leave hb hB

/-- The like at its SECOND (the last) chain: from the record that start₃ makes of the two other
chains' ends. -/
theorem run_atCut3 (X : Letters) (p : P12) {Xi : Type} (F : FileDescription Xi)
    (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e)
    (pre : List (Block F.S₃ F.Cl)) (B : Block F.S₃ F.Cl) (l : List (Block F.S₃ F.Cl))
    (enter : F.S₃ → Except String T12) (leave : F.S₃ → T12 → Except String F.S₃)
    (hb : F.second.blocksInOrder = pre ++ B :: l) (hB : Sits B (proximityTestKind guardedProximityTestParts p : Blk') enter leave) :
    ∃ s₃, F.start₃ (F.pub x) e.1 e.2.1 = .ok s₃ ∧
      AtCut X p F.lastChainFirstTreeNumber pre B l enter leave s₃ e.2.2 v₃ := by
  obtain ⟨s₃, hs, a1, a2⟩ := (run_steps F x v₁ v₂ v₃ e h).2.2
  exact ⟨s₃, hs, atCut_of_sits X p _ _ _ _ _ a1 a2 pre B l enter leave hb hB⟩

end H2K.JointK

#print axioms H2K.JointK.sits_inside
#print axioms H2K.JointK.Sits.same
#print axioms H2K.JointK.Sits.behind
#print axioms H2K.JointK.Sits.guarded
#print axioms H2K.JointK.Sits.withRoundlessBlockBehind
#print axioms H2K.JointK.isSeat_sits
#print axioms H2K.JointK.atCut_of_sits
#print axioms H2K.JointK.run_atCut1
#print axioms H2K.JointK.run_atCut2
#print axioms H2K.JointK.run_atCut3
