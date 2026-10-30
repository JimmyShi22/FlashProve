-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtCourseAll2
import Johnson.Desc.K12.Law.EarlyStep
/-
Johnson/Desc/K12/Law/AccKAtCourseAll3.lean: A SMALL FILE ON TOP OF
Johnson/Desc/K12/Law/AccKAtCourseAll2.lean: THE LAST PREMISE ON THE PLACE FALLS: p.early = true:
early_of_step (Johnson/Desc/K12/Law/EarlyStep.lean: a yes of the kind's block's
step gives p.early = true; no test on the plan, no other premise: where the masks do not come early
the base case finds no masking message and refuses). So from a yes of a written description's
decision ALONE: AtSeatAll at its three flat lists. NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING. AN ASSEMBLY.
  yesAll_of_step3 · atSeatAll_of_steps3 · course_atSeat_all3 · run_atSeat_all3 · run_given3     the
      five of the same names with «2», the binder (he : p.early = true) struck; the definitions
      (YesAll · AtSeatAll · GivenAt · IsSeat) are the elder files' own. THE ORDER: the kind's
      block's step's yes at the seat comes of seat_step2, which spends no he; early_of_step then
      gives he for what follows.
No sorry and no axiom of our own stands in this file.
WHAT IS LEFT AS PREMISES: F.runEnd x v₁ v₂ v₃ = .ok e; and INSIDE AtSeatAll: the cut bs = pre ++ B
:: l and the three things asked of B (IsSeat). X and p are free letters: at a p at which no block of
F is seated all three conjuncts are idle.
LIMITS. All of the elder files'. IT CARRIES A YES, NOT A PRICE.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)
open H2K.First (canonOk)

theorem yesAll_of_step3 (X : Letters) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 : T12) (F : ℕ) (mine : List Fmt.RoundView)
    (cols : List OpenedColumn) (hcan : canonOk mine = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 mine cols = .ok (tE, n)) :
    ∃ r0 rs', mine = r0 :: rs' ∧ YesAll X p F t0 r0 rs' cols :=
  yesAll_of_step2 X p (early_of_step p t0 tE F n mine cols hstep) hp t0 F mine cols hcan tE n hstep

theorem atSeatAll_of_steps3 (X : Letters) (p : P12)
    (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (hpl : ∀ b ∈ bs, b.planOk = true) (h : H2K.First.StepsAt ft bs s s' v) :
    AtSeatAll X p ft bs s s' v := by
  intro pre B l enter leave hb hr hd hpB
  obtain ⟨m, cols, t, k, h0, h1, h2, h3⟩ := h pre B l hb
  have hp := hpB (hpl B (by rw [hb]; simp))
  obtain ⟨t0, tE, e1, e2, e4⟩ := seat_step2 B enter _ leave hr hd ft m t _ cols k h1
  obtain ⟨r0, rs', e3, hy⟩ := yesAll_of_step3 X p hp t0 ft _ cols h3 tE k e2
  exact ⟨m, t0, r0, rs', cols, tE, k, t, h0, fold_cols_drop ft pre s _ _ _ h0, e1, e3, e3 ▸ e2, e4,
    h2, hy⟩

theorem course_atSeat_all3 (X : Letters) (p : P12)
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
  exact ⟨atSeatAll_of_steps3 X p 0 _ _ _ _ h1 a1, atSeatAll_of_steps3 X p 0 _ _ _ _ h2 a2,
    s₃, hs, atSeatAll_of_steps3 X p ft _ _ _ _ h3 a3⟩

/-- F.runEnd's yes: NO PREMISE ON THE PLACE AT ALL. -/
theorem run_atSeat_all3 (X : Letters) (p : P12)
    {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok e) :
    AtSeatAll X p 0 F.first.blocksInOrder (F.start₁ (F.pub x)) e.1 (withEmptySealRound v₁) ∧
      AtSeatAll X p 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) e.2.1 v₂ ∧
      ∃ s₃, F.start₃ (F.pub x) e.1 e.2.1 = .ok s₃ ∧
        AtSeatAll X p F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ e.2.2 v₃ := by
  obtain ⟨h1, h2, h3⟩ := Keeps.runEnd_blocks F x v₁ v₂ v₃ e h
  exact course_atSeat_all3 X p _ _ _ _ _ _ _ _ _ _ v₁ v₂ v₃ e h1 h2 h3 h

theorem run_given3 (X : Letters) (p : P12)
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
    atSeatAll_given X p 0 _ _ _ _ (run_atSeat_all3 X p F x v₁ v₂ v₃ e h).1 pre B l enter leave
      hb hB
  exact ⟨m, t0, r0, rs', cols, a1, a2, a3, a4, a9⟩

end H2K.JointK

#print axioms H2K.JointK.yesAll_of_step3
#print axioms H2K.JointK.run_atSeat_all3
#print axioms H2K.JointK.run_given3
