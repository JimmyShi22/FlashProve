-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/FrameP.lean: THE PLANNER's ROUTINES READ NO ROUND: a
routine of OnBytes/Params/Planner.lean that returns from a plan p returns the like from p with any
rounds R laid in front of its own, and leaves the setting as it was. Theorems. A law file; no
running text imports it.
  `under R p`   p with the rounds R in front of its own.
  `FrP y`       wherever y returns (a, q) from p: q.set = p.set, and from `under R p` it returns (a,
                under R q).
  `frP_pure`, `frP_bind`, `frP_ite`, `frP_needs`, `frP_must`, `frP_refuse`, `frP_modify`,
  `frP_close`,
  `frP_closeNone`; the tactic `frp`; then each routine by its name.
Limits. A CONDITIONAL ON RETURNS: of a routine that refuses nothing is said. Nothing on what a round
means.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.RowsNoArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- p, with the rounds R in front of its own. -/
def under (R : Array PlanRound) (p : PlanState) : PlanState := { p with rounds := R ++ p.rounds }

theorem app_push {β : Type} (R rs : Array β) (r : β) : (R ++ rs).push r = R ++ rs.push r := by
  apply Array.ext'
  simp

/-- A routine of the planner that reads no round and leaves the setting. -/
def FrP {α : Type} (y : Planning α) : Prop :=
  ∀ p a q, y.run p = .ok (a, q) → q.set = p.set ∧ ∀ R, y.run (under R p) = .ok (a, under R q)

section
variable {α β : Type}

theorem frP_pure (a : α) : FrP (pure a : Planning α) := by
  intro p b q h
  cases h
  exact ⟨rfl, fun _ => rfl⟩

theorem frP_bind {y : Planning α} {f : α → Planning β} (hy : FrP y) (hf : ∀ a, FrP (f a)) :
    FrP (y >>= f) := by
  intro p b q h
  rw [StateT.run_bind] at h
  obtain ⟨⟨a, p1⟩, h1, h2⟩ := exc_bind h
  obtain ⟨s1, g1⟩ := hy p a p1 h1
  obtain ⟨s2, g2⟩ := hf a p1 b q h2
  refine ⟨s2.trans s1, fun R => ?_⟩
  rw [StateT.run_bind, g1 R]
  exact g2 R

theorem frP_ite {c : Prop} [Decidable c] {x y : Planning α} (hx : FrP x) (hy : FrP y) :
    FrP (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem frP_refuse (why : String) : FrP (refusePlan why : Planning α) := by
  intro p a q h
  cases h

theorem frP_needs (b : Bool) (why : String) : FrP (needs b why) := by
  unfold needs
  exact frP_ite (frP_pure _) (frP_refuse _)

theorem frP_must (x : Option α) (why : String) : FrP (must x why) := by
  cases x with
  | none => exact frP_refuse _
  | some a => exact frP_pure a

theorem frP_theSetting : FrP theSetting := by
  intro p a q h
  cases h
  exact ⟨rfl, fun _ => rfl⟩

theorem frP_theScope : FrP theScope := by
  intro p a q h
  cases h
  exact ⟨rfl, fun _ => rfl⟩

theorem frP_modify (f : PlanState → PlanState) (h1 : ∀ p, (f p).set = p.set)
    (h2 : ∀ R p, f (under R p) = under R (f p)) : FrP (modify f : Planning PUnit) := by
  intro p a q h
  cases h
  refine ⟨h1 p, fun R => ?_⟩
  have e : (modify f : Planning PUnit).run (under R p) = .ok (PUnit.unit, f (under R p)) := rfl
  rw [e, h2]

end

theorem frP_planScalars (n : Nat) : FrP (planScalars n) :=
  frP_modify _ (fun _ => rfl) (fun _ _ => rfl)

theorem frP_planAnswers (n : Nat) : FrP (planAnswers n) :=
  frP_modify _ (fun _ => rfl) (fun _ _ => rfl)

theorem frP_planRoots (n : Nat) : FrP (planRoots n) :=
  frP_modify _ (fun _ => rfl) (fun _ _ => rfl)

theorem frP_closeNone (name : String) : FrP (closeNone name) := by
  intro p a q h
  unfold closeNone at h
  simp only [StateT.run] at h
  split at h
  · cases h
  · rename_i c
    cases h
    refine ⟨rfl, fun R => ?_⟩
    unfold closeNone
    simp only [StateT.run]
    have c' : ¬ ((under R p).openRoots != 0) = true := c
    rw [if_neg c']
    simp only [under, app_push]

/-- From two equations on the routine as a function. -/
theorem frP_of_eqs {α : Type} {y : Planning α}
    (h1 : ∀ p, Except.map (fun r => r.2.set) (y.run p) = Except.map (fun _ => p.set) (y.run p))
    (h2 : ∀ R p, y.run (under R p) = Except.map (fun r => (r.1, under R r.2)) (y.run p)) :
        FrP y := by
  intro p a q h
  refine ⟨?_, fun R => ?_⟩
  · have e := h1 p
    rw [h] at e
    exact Except.ok.inj e
  · rw [h2, h]
    rfl

theorem frP_close (name : String) (why : ErrorKind) (error : Bound) (d : Draws) :
    FrP (close name why error d) := by
  apply frP_of_eqs
  · intro p
    unfold close
    simp only [StateT.run]
    rw [apply_ite (Except.map _), apply_ite (Except.map _)]
    rfl
  · intro R p
    unfold close
    simp only [StateT.run]
    rw [apply_ite (Except.map _)]
    simp only [under, Except.map, app_push]
    try rfl

/-! ## The tactic -/

/-- One step through a routine of the planner. Each routine's own lemma is added below it. -/
syntax "frp_step" : tactic
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible intro _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible assumption)
macro_rules
  | `(tactic| frp_step) =>
    `(tactic| with_reducible refine frP_modify _ (fun _ => rfl) (fun _ _ => ?_) <;>
                              first | rfl | simp only [under, app_push])
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_close _ _ _ _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_closeNone _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planRoots _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planAnswers _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planScalars _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_theScope)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_theSetting)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_refuse _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_must _ _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_needs _ _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_pure _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_ite)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_bind)

/-- Steps through a routine of the planner. -/
macro "frp" : tactic => `(tactic| (try dsimp only) <;> repeat' frp_step)

/-! ## The routines of OnBytes/Params/Planner.lean and three of SubRounds.lean -/

theorem frP_planAnalysis (g : GroupSize) : FrP (planAnalysis g) := by
  unfold planAnalysis
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planAnalysis _)

theorem frP_planPositions (agree extra : Bound) : FrP (planPositions agree extra) := by
  unfold planPositions
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planPositions _ _)

theorem frP_planListed (logN t : Nat) : FrP (planListed logN t) := by
  unfold planListed
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planListed _ _)

theorem frP_listOfGroups : ∀ gs : List GroupSize, FrP (listOfGroups gs)
  | [] => by
    unfold listOfGroups
    frp
  | g :: gs => by
    have := frP_listOfGroups gs
    unfold listOfGroups
    frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_listOfGroups _)

theorem frP_sampleErrors (s : Setting) :
    ∀ (xs : List SampleSize) (e : Bound), FrP (sampleErrors s xs e)
  | [], e => by
    unfold sampleErrors
    frp
  | x :: xs, e => by
    have := fun e => frP_sampleErrors s xs e
    unfold sampleErrors
    frp
    exact this _
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_sampleErrors _ _ _)

theorem frP_planSend (o : List SampleSize) (roots : Nat) (answerRound : Bool) :
    FrP (planSend o roots answerRound) := by
  unfold planSend
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planSend _ _ _)

theorem frP_planBat (groups : List GroupSize) (rows : Nat) : FrP (planBat groups rows) := by
  unfold planBat
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planBat _ _)

theorem frP_planBatSigma (rows : Nat) : FrP (planBatSigma rows) := by
  unfold planBatSigma
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planBatSigma _)

theorem frP_planSplit : FrP planSplit := by
  unfold planSplit
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planSplit)

theorem frP_planPscRounds (s : Setting) : ∀ gs : List Nat, FrP (planPscRounds s gs)
  | [] => by
    unfold planPscRounds
    frp
  | g :: gs => by
    have := frP_planPscRounds s gs
    unfold planPscRounds
    frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planPscRounds _ _)

theorem frP_planPsc (x : PscSize) : FrP (planPsc x) := by
  unfold planPsc
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planPsc _)

theorem frP_planZero (n : Nat) : FrP (planZero n) := by
  unfold planZero
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planZero _)

theorem frP_planLine : FrP planLine := by
  unfold planLine
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLine)

theorem frP_planShift (n : Nat) : FrP (planShift n) := by
  unfold planShift
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planShift _)

theorem frP_planJoin (n : Nat) : FrP (planJoin n) := by
  unfold planJoin
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planJoin _)

theorem frP_planTreeLevels (more : Nat) : ∀ fuel l : Nat, FrP (planTreeLevels more fuel l)
  | 0, _ => by
    unfold planTreeLevels
    frp
  | fuel + 1, l => by
    have := frP_planTreeLevels more fuel (l + 1)
    unfold planTreeLevels
    frp

theorem frP_planProductTree (levels more : Nat) : FrP (planProductTree levels more) :=
  frP_planTreeLevels more levels 0
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planProductTree _ _)

theorem frP_planBatt (rows kCol : Nat) : FrP (planBatt rows kCol) := by
  unfold planBatt
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planBatt _ _)

theorem frP_forEach {γ : Type} {f : γ → Planning Unit} (h : ∀ a, FrP (f a)) :
    ∀ l : List γ, FrP (forEach l f)
  | [] => by
    unfold forEach
    frp
  | a :: t => by
    have := frP_forEach h t
    have := h a
    unfold forEach
    frp

theorem frP_planRng (columns : Nat) : FrP (planRng columns) := by
  unfold planRng
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planRng _)

theorem frP_planFoldFrom (s : Setting) (g : GroupSize) (a : Analysis) :
    ∀ fuel j : Nat, FrP (planFoldFrom s g a fuel j)
  | 0, _ => by
    unfold planFoldFrom
    frp
  | fuel + 1, j => by
    have := frP_planFoldFrom s g a fuel (j + 1)
    unfold planFoldFrom
    frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planFoldFrom _ _ _ _ _)

theorem frP_planFoldRounds (g : GroupSize) : FrP (planFoldRounds g) := by
  unfold planFoldRounds
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planFoldRounds _)

theorem frP_planFold (g : GroupSize) (roots : Nat) : FrP (planFold g roots) := by
  unfold planFold
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planFold _ _)

theorem frP_planLoc (g : GroupSize) : FrP (planLoc g) := by
  unfold planLoc
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLoc _)

theorem frP_planCs (source target : GroupSize) (cubeBits oldRows symbols roots : Nat) :
    FrP (planCs source target cubeBits oldRows symbols roots) := by
  unfold planCs
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planCs _ _ _ _ _ _)

theorem frP_planBase (g : GroupSize) (roots : Nat) : FrP (planBase g roots) := by
  unfold planBase
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planBase _ _)

theorem frP_planTable (T : TableSize) : FrP (planTable T) := by
  unfold planTable
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planTable _)

theorem frP_planRecord (T : TableSize) : FrP (planRecord T) := by
  unfold planRecord
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planRecord _)

theorem frP_planSeal : FrP planSeal := frP_close _ _ _ _
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planSeal)

theorem frP_planLinFirst (x : LinSize) : FrP (planLinFirst x) := frP_planSend _ _ _
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLinFirst _)

theorem frP_planLinShared (T : TableSize) (x : LinSize) : FrP (planLinShared T x) := by
  unfold planLinShared
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLinShared _ _)

theorem frP_planLink (T : TableSize) (u : SampleSize) : FrP (planLink T u) := by
  unfold planLink
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLink _ _)

theorem frP_planProductLayer (n : Nat) : FrP (planProductLayer n) := by
  unfold planProductLayer
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planProductLayer _)

theorem frP_planTokenSumcheck (lt degreeY shown : Nat) :
    FrP (planTokenSumcheck lt degreeY shown) := by
  unfold planTokenSumcheck
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planTokenSumcheck _ _ _)

theorem frP_planTokenSum (lt shown degreeInY more : Nat) :
    FrP (planTokenSum lt shown degreeInY more) := by
  unfold planTokenSum
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planTokenSum _ _ _ _)

/-- **Every call's own routine reads no round.** -/
theorem frP_plan (c : Call) : FrP c.plan := by
  cases c <;> unfold Call.plan <;> frp

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frP_bind
#print axioms VerifiableInference.Desc.LinkJoin.frP_close
#print axioms VerifiableInference.Desc.LinkJoin.frP_closeNone
#print axioms VerifiableInference.Desc.LinkJoin.frP_forEach
#print axioms VerifiableInference.Desc.LinkJoin.frP_plan
