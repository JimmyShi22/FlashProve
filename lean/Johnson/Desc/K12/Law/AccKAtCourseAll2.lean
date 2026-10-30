-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKGivenAtCourse
import Johnson.Desc.K12.Law.AnswersStep
/-
Johnson/Desc/K12/Law/AccKAtCourseAll2.lean: A SMALL FILE ON TOP OF Johnson/Desc/K12/Law/AccKAtCourseAll.lean | AccKGivenAtCourse.lean: THE PREMISE p.answers = 1 FALLS: answers_of_step (Johnson/Desc/K12/Law/AnswersStep.lean: planOk and the kind's block's step's yes give p.answers = 1; no premise on early). So beside the yes of a written description's decision ONE PREMISE ON THE PLACE IS LEFT: p.early = true. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. AN ASSEMBLY.
  yesAll_of_step2 · atSeatAll_of_steps2 · course_atSeat_all2 · run_atSeat_all2 · run_given2     the five of the same names without «2», the binder (ha : p.answers = 1) struck; the definitions (YesAll · AtSeatAll · GivenAt · IsSeat) are the elder files' own.
No sorry and no axiom of our own stands in this file.
LIMITS. All of the two elder files'.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)
open H2K.First (canonOk)

theorem yesAll_of_step2 (X : Letters) (p : P12) (he : p.early = true)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 : T12) (F : ℕ) (mine : List Fmt.RoundView)
    (cols : List OpenedColumn) (hcan : canonOk mine = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 mine cols = .ok (tE, n)) :
    ∃ r0 rs', mine = r0 :: rs' ∧ YesAll X p F t0 r0 rs' cols :=
  yesAll_of_step X p he (answers_of_step p t0 tE F n mine cols hp hstep) hp t0 F mine cols hcan tE n
    hstep

theorem atSeatAll_of_steps2 (X : Letters) (p : P12) (he : p.early = true)
    (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (hpl : ∀ b ∈ bs, b.planOk = true) (h : H2K.First.StepsAt ft bs s s' v) :
    AtSeatAll X p ft bs s s' v := by
  intro pre B l enter leave hb hr hd hpB
  obtain ⟨m, cols, t, k, h0, h1, h2, h3⟩ := h pre B l hb
  have hp := hpB (hpl B (by rw [hb]; simp))
  obtain ⟨t0, tE, e1, e2, e4⟩ := seat_step2 B enter _ leave hr hd ft m t _ cols k h1
  obtain ⟨r0, rs', e3, hy⟩ := yesAll_of_step2 X p he hp t0 ft _ cols h3 tE k e2
  exact ⟨m, t0, r0, rs', cols, tE, k, t, h0, fold_cols_drop ft pre s _ _ _ h0, e1, e3, e3 ▸ e2, e4,
    h2, hy⟩

theorem course_atSeat_all2 (X : Letters) (p : P12) (he : p.early = true)
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
  exact ⟨atSeatAll_of_steps2 X p he 0 _ _ _ _ h1 a1, atSeatAll_of_steps2 X p he 0 _ _ _ _ h2 a2,
    s₃, hs, atSeatAll_of_steps2 X p he ft _ _ _ _ h3 a3⟩

/-- F.runEnd's yes and p.early = true: NO OTHER PREMISE. -/
theorem run_atSeat_all2 (X : Letters) (p : P12) (he : p.early = true)
    {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok e) :
    AtSeatAll X p 0 F.first.blocksInOrder (F.start₁ (F.pub x)) e.1 (withEmptySealRound v₁) ∧
      AtSeatAll X p 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) e.2.1 v₂ ∧
      ∃ s₃, F.start₃ (F.pub x) e.1 e.2.1 = .ok s₃ ∧
        AtSeatAll X p F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ e.2.2 v₃ := by
  obtain ⟨h1, h2, h3⟩ := Keeps.runEnd_blocks F x v₁ v₂ v₃ e h
  exact course_atSeat_all2 X p he _ _ _ _ _ _ _ _ _ _ v₁ v₂ v₃ e h1 h2 h3 h

theorem run_given2 (X : Letters) (p : P12) (he : p.early = true)
    {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok e) (pre : List (Block F.S₁ F.Cl)) (B : Block F.S₁ F.Cl)
    (l : List (Block F.S₁ F.Cl)) (enter : F.S₁ → Except String T12)
    (leave : F.S₁ → T12 → Except String F.S₁) (hb : F.first.blocksInOrder = pre ++ B :: l)
    (hB : IsSeat B p enter leave) :
    ∃ (m : F.S₁) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks 0 pre (F.start₁ (F.pub x)) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
        .ok (m, behindOf pre (withEmptySealRound v₁).rounds, cols) ∧
      (∃ j, cols = (withEmptySealRound v₁).opened.drop j) ∧ enter m = .ok t0 ∧
      (behindOf pre (withEmptySealRound v₁).rounds).take B.rounds.length = r0 :: rs' ∧
      GivenAt p 0 t0 r0 rs' cols := by
  obtain ⟨m, t0, r0, rs', cols, _, _, _, a1, a2, a3, a4, _, _, _, _, a9⟩ :=
    atSeatAll_given X p 0 _ _ _ _ (run_atSeat_all2 X p he F x v₁ v₂ v₃ e h).1 pre B l enter leave
      hb hB
  exact ⟨m, t0, r0, rs', cols, a1, a2, a3, a4, a9⟩

end H2K.JointK

#print axioms H2K.JointK.yesAll_of_step2
#print axioms H2K.JointK.run_atSeat_all2
#print axioms H2K.JointK.run_given2
