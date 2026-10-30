-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.TieOkMade
/-
Johnson/Desc/K12/Law/AnswersStep.lean: p.answers = 1 FROM THE BLOCK's OWN YES: a yes of the proximity test's block (the kind K12) holds that the place's number of answers to an out-of-domain sample is 1. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
Why it holds. The switch's part (switchJ, Johnson/Desc/K12/Join.lean) calls switchE (Parts.lean) at a target whose shape has p.answers answers. switchE's test (c2) asks that the entry "SEND seed" draws as many elements other than 0 as the largest number of answers among the notices of the sending, of which the target's is the first. The entry is the plan's: the frame deals the switch the declared rounds that H2U.roundsOfNums makes of the place's numbers, and there "SEND seed" has drawNZ = 1 (MadeRounds.lean; Fmt/M1Plan.lean's rSeed). So p.answers ≤ 1. sizesOk, a clause of the frame's test on the plan, asks 1 ≤ p.answers.
Main names:
  le_foldl_max, mem_foldl_max: the largest of a list's numbers is at least each.
  switchE_c2: a yes of switchE: the stretch's first entry draws as many elements other than 0 as the notices ask.
  switchJ_answers: a yes of the switch's part at a cut whose first round's entry has drawNZ = 1: p.answers ≤ 1.
  answers_of_decide, answers_of_step: the block's test on the plan and a yes of its decision, or of Block.step, give p.answers = 1.
WHAT IT PAYS: the premise ha : p.answers = 1 wherever a yes of the step stands beside it (k12_step_accE … accH, accK_yes_…). In a law that wants the chain IN FRONT of the rounds (k12_lemma; the coin's AtPlace.answers) there is no yes to spend: there it stays a premise on the place.
(Where this and lean/THEOREM.md differ,
the page holds.)
Limits: stated of guardedProximityTestParts (Johnson/Desc/K12/JoinGuarded.lean). p.early is not asked.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)
open H2K.Made (rounds_head cuts rounds_of_planOk)
open Fmt.M1 (rSeed)

theorem le_foldl_max {α : Type} (f : α → Nat) : ∀ (l : List α) (a : Nat),
    a ≤ l.foldl (fun a n => max a (f n)) a
  | [], _ => Nat.le_refl _
  | x :: l, a => Nat.le_trans (Nat.le_max_left a (f x)) (le_foldl_max f l _)

theorem mem_foldl_max {α : Type} (f : α → Nat) : ∀ (l : List α) (a : Nat) (x : α), x ∈ l →
    f x ≤ l.foldl (fun a n => max a (f n)) a
  | y :: l, a, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a (f x)) (le_foldl_max f l _)
    · exact mem_foldl_max f l _ x h

/-- A yes of switchE holds its test (c2). -/
theorem switchE_c2 (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (s : H2K.PS) (r : (Switched × E) × H2K.PS) (h : H2K.switchE old T gp others true s = .ok r) :
    ∃ e₁ es, s.entries = e₁ :: es ∧
      e₁.drawNZ = (Tw.L9.switchNotices T others).foldl (fun a n => max a n.shape.answers) 0 := by
  unfold H2K.switchE at h
  split at h
  · rename_i e₁ e₂ es r₁ r₂ rs he hr
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, hc2, _⟩ := bind_ok h
    exact ⟨e₁, e₂ :: es, he, by simpa using needD_ok hc2⟩
  · cases h

/-- A yes of the switch's part, at a cut whose first round's entry draws one element other than 0. -/
theorem switchJ_answers (p : P12) (j : Nat) (cur next : Fmt.M1.Stage) (last : Bool)
    (c0 : Fmt.DeclaredRound) (cut : List Fmt.DeclaredRound) (h0 : c0.entry.drawNZ = 1) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (switchJ p j cur next last (c0 :: cut)).decide t rs gs = .ok t1) : p.answers ≤ 1 := by
  unfold switchJ at h
  dsimp only at h
  split at h
  · rename_i rows gp n _ _
    obtain ⟨x, hx, _⟩ := bind_ok h
    obtain ⟨e₁, es, he, hc⟩ := switchE_c2 _ _ _ _ _ _ hx
    have he' : c0.entry = e₁ := (List.cons.inj he).1
    rw [← he', h0, ← Array.foldl_toList] at hc
    rw [hc]
    refine mem_foldl_max (fun n : OracleNotice => n.shape.answers) _ 0
      ⟨(switchTargetStage n.code n.maskCode n.k n.h p.answers).shape,
        (switchTargetStage n.code n.maskCode n.k n.h p.answers).leafClass⟩ ?_
    simp [Tw.L9.switchNotices]
  · cases h

/-- **p.answers = 1, from the block's test on the plan and a yes of its decision.** -/
theorem answers_of_decide (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : p.answers = 1 := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, _, _, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨ds', e2', hlen⟩ := rounds_of_planOk guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  obtain ⟨s, next, rest', R', hs, _, hrds⟩ := rounds_head p.nums ds' e2
  rw [hs] at e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  obtain ⟨_, t2, _, _, hsw, _⟩ := (stagesFrom_ok guardedProximityTestParts p 0 s next rest' _ _ _ _ _).1 hst
  have hl : (((ds'.zip p.oracles).drop 1).map (·.1)) = ds'.drop 1 := by
    rw [List.map_drop, List.map_fst_zip (by omega)]
  generalize ds'.zip p.oracles = Z at hl hsw
  rw [hrds, List.drop_succ_cons, List.drop_zero] at hl
  obtain ⟨_, c2, _⟩ := cuts _ _ _ _ R' s.k (by simp [Nat.add_comm]) hl
  have hsj := (ranged_ok _ _ _ _ _ _ hsw).1
  have hsj' : (switchJ p 0 s next rest'.isEmpty
      ((((Z.drop 1).drop (1 + s.k)).take 2).map (·.1))).decide _ _ _ = .ok t2 := hsj
  rw [c2] at hsj'
  have hle := switchJ_answers p 0 s next _ _ _ (by simp [rSeed]) _ _ _ _ hsj'
  have hge : 1 ≤ p.answers := by
    unfold proximityTestKind at hp
    split at hp
    · simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have h4 := hp.1.1.1.1
      unfold sizesOk at h4
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
      exact h4.1.2
    · cases hp
  omega

/-- **The same of Block.step.** -/
theorem answers_of_step (p : P12) (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 rs cols = .ok (tE, n)) : p.answers = 1 := by
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F _ t0 tE rs cols n h
  exact answers_of_decide p t0 tE _ _ hp hdec

end H2K.JointK

#print axioms H2K.JointK.answers_of_decide
#print axioms H2K.JointK.answers_of_step
