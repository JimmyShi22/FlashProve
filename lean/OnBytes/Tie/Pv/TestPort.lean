-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/TestPort.lean: the rounds of a whole proximity test as the planner adds them, against
one list of counts; and so the errors of a key's second chain, work counted, against the target.

OnBytes/Tie/Pv/BatPort.lean and TowerPort.lean compare one planned round with one pair (bad values,
values). This file lays these pairs in a row, in the order of the planner's list `ioppList`
(OnBytes/Params/PlanListsProx.lean), general in the stages. Definitions and statements with their
proofs. No block of the proof library occurs in a statement.
Main names:
  `StageOK s g e`: what is asked of a stage's group g at the radius e: `JohnsonGroup`
    (OnBytes/Params/GroupPrices.lean), and e is at least the upper radius.
  `foldPairs`, `csPairs`, `basePairs`, `stagesPairs`, `testPairs`: the largest counts that the
    prices cover, round by round: of a fold, a code switch, a last step, the stages, a whole test.
  `bad_of_good`: what `close` has tested of a round says that its price is not marked bad.
  `test_covered`: `testPairs` is covered, pair by pair, by `ioppList` under the scope `.once`, if
    every stage is in order and `close` has tested every round.
  `covered_mono`, `LePairs`, `covered_of_le`: smaller counts of as many values are covered too.
  `second_belowG`: for a finished plan of a key's second chain: a list of errors whose counts are
    at most `testPairs`, of as many values, with the plan's bits of work, has `Err.BelowG` at
    1 / 2 ^ target (`belowG_of_plan`, OnBytes/Tie/Pv/Below.lean).
Limits: only groups with a mask whose main code rules (`JohnsonGroup`). That a group of a key is
such a group, at which radius, is a premise. `StageOK` bounds the radius from both sides: it is at
most (1 - agreement) times the length, and at least the upper end of the planner's interval for
that number, rounded down; that some radius has both at a given group is not shown. That the
errors of a given chain of reductions are at most `testPairs` is a premise; `foldCount` and
`baseSum` in them are the library's assumed bound on counts, so for a block it asks what is proved
nowhere beyond half a distance. The scope is `.once`. A maximum over the rounds; no sum. That work
is worth its bits is not said here.

-/
import OnBytes.Tie.Pv.BatPort
import OnBytes.Tie.Pv.TowerPort
import OnBytes.Tie.Pv.Below
import OnBytes.Plan.PlanListsKeyMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open OnBytes OnBytes.Params OnBytes.Plan Iop

/-! ### lists -/

theorem forall₂_app {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ m₁ : List α} {l₂ m₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R m₁ m₂ →
      List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (forall₂_app t h)

/-- A relation that holds wherever the right member has P, at a list all of whose members have P. -/
theorem forall₂_of_mem {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => P b → R a b) l₁ l₂ →
      (∀ b ∈ l₂, P b) → List.Forall₂ R l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hp =>
    .cons (h (hp _ List.mem_cons_self))
      (forall₂_of_mem t fun b hb => hp b (List.mem_cons_of_mem _ hb))

/-! ### one round -/

/-- What `close` has tested of a round says that its price is not marked bad. -/
theorem bad_of_good {s : Setting} {n : String} {w : ErrorKind} {e : Bound} {d : Draws}
    {b r a : ℕ} (h : (RoundSpec.said n w e d b r a).Good s .once) : e.bad = false := by
  have h1 := h.1
  simpa [RoundSpec.bound] using h1

/-- Covered, if `close` has tested the round. -/
def CoveredIf (s : Setting) (cn : ℕ × ℕ) (y : RoundSpec) : Prop :=
  y.Good s .once → Covered s .once cn y

/-- What is asked of a stage's group at a radius. -/
structure StageOK (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  group : JohnsonGroup s g e
  whole : ((analysisOfM s g).mainAt.delta * Bound.ofNat (lenOf g)).bad = false
  upper : upperRadius (analysisOfM s g).mainAt.delta (lenOf g) ≤ e

/-! ### the pairs -/

/-- The counts of a fold: its first round, and rounds 1 to k. -/
noncomputable def foldPairs (s : Setting) (g : GroupSize) (e : ℕ) : List (ℕ × ℕ) :=
  (listMain g e, s.cardE) :: (List.range g.k).map fun i => (foldCount g e (1 + i), s.cardE)

/-- The counts of a code switch. -/
noncomputable def csPairs (s : Setting) (g g' : GroupSize) (e e' cubeBits oldRows symbols : ℕ) :
    List (ℕ × ℕ) :=
  [((largestList s [g']).choose 2 * clashSeeds s.cardE cubeBits ^ s.samples,
      allSeeds s.cardE cubeBits ^ s.samples),
    ((lenOf g - e - 1) ^ csCount s .once g g' oldRows symbols * s.cardE +
        lenOf g ^ csCount s .once g g' oldRows symbols *
          (listMain g' e' *
            (oldRows + s.samples + symbols * csCount s .once g g' oldRows symbols - 1)),
      lenOf g ^ csCount s .once g g' oldRows symbols * s.cardE)]

/-- The counts of a last step. -/
noncomputable def basePairs (s : Setting) (g : GroupSize) (e : ℕ) : List (ℕ × ℕ) :=
  [(baseSum g e, s.cardE),
    ((lenOf g - e - 1) ^ baseCount s .once g, lenOf g ^ baseCount s .once g)]

/-- The counts of the stages, at the radius eOf of each stage's group. -/
noncomputable def stagesPairs (s : Setting) (eOf : GroupSize → ℕ) : List StageSize → List (ℕ × ℕ)
  | x :: y :: rest =>
    foldPairs s x.g (eOf x.g) ++
      (csPairs s x.g y.g (eOf x.g) (eOf y.g) (stageCubeBits y.g) 1
          (x.g.slots + (if x.g.hasMask then 2 else 0)) ++
        stagesPairs s eOf (y :: rest))
  | [x] => basePairs s x.g (eOf x.g)
  | [] => []

/-- The counts of a proximity test. -/
noncomputable def testPairs (s : Setting) (eOf : GroupSize → ℕ) (st : List StageSize) (rows : ℕ) :
    List (ℕ × ℕ) :=
  (largestList s (st.take 1 |>.map (·.g)) * (rows - 1), s.cardE) :: stagesPairs s eOf st

/-! ### covered -/

section
variable {s : Setting} {g g' : GroupSize} {e e' : ℕ}

theorem fold_coveredIf (h : StageOK s g e) (roots : ℕ) :
    List.Forall₂ (CoveredIf s) (foldPairs s g e) (foldList s g roots) := by
  unfold foldPairs foldList
  refine .cons (fun hg => fold_first_covered h.group roots _ le_rfl ?_) ?_
  · have hb : (Bound.ofNat (analysis s g).list * fieldError s 1).bad = false := bad_of_good hg
    rwa [h.group.analysis_eq] at hb
  · refine forall₂_foldFrom (fun j => (foldCount g e j, s.cardE)) g.k 1 fun i _ hg =>
      fold_round_covered h.group (1 + i) _ le_rfl ?_
    have hb : (foldRoundError s g (analysis s g) (1 + i)).bad = false := bad_of_good hg
    rwa [h.group.analysis_eq] at hb

theorem cs_coveredIf (hq : 2 ≤ s.cardE) (h : StageOK s g e) (h' : StageOK s g' e')
    (cubeBits oldRows symbols roots : ℕ) :
    List.Forall₂ (CoveredIf s) (csPairs s g g' e e' cubeBits oldRows symbols)
      (csList s .once g g' cubeBits oldRows symbols roots) := by
  rw [csList_eq]
  unfold csPairs
  refine .cons (fun hg => seed_covered ⟨cubeBits, [g']⟩ roots (largestList s [g']) _ _ hq le_rfl
    rfl le_rfl (bad_of_good hg)) (.cons (fun hg => cs_covered h.group h'.group h.whole h.upper
      oldRows symbols _ (by omega) le_rfl ?_) .nil)
  have hb : (Bound.pow (analysis s g).mainAt.agree (csCount s .once g g' oldRows symbols) +
      Bound.ofNat (analysis s g').list *
        powersError s
          (oldRows + s.samples + symbols * csCount s .once g g' oldRows symbols)).bad = false :=
    bad_of_good hg
  rwa [h.group.analysis_eq, h'.group.analysis_eq] at hb

theorem base_coveredIf (h : StageOK s g e) (roots : ℕ) :
    List.Forall₂ (CoveredIf s) (basePairs s g e) (baseList s .once g roots) := by
  rw [baseList_eq]
  unfold basePairs
  refine .cons (fun hg => base_first_covered h.group roots _ le_rfl ?_)
    (.cons (fun hg => base_last_covered h.group h.whole h.upper ?_) .nil)
  · have hb : (baseError s g (analysis s g)).bad = false := bad_of_good hg
    rwa [h.group.analysis_eq] at hb
  · have hb : (Bound.pow (analysis s g).mainAt.agree (baseCount s .once g)).bad = false :=
      bad_of_good hg
    rwa [h.group.analysis_eq] at hb

end

theorem stages_coveredIf {s : Setting} (hq : 2 ≤ s.cardE) (eOf : GroupSize → ℕ) (fm : ℕ)
    (mr : Bool) :
    ∀ (first : Bool) (st : List StageSize), (∀ x ∈ st, StageOK s x.g (eOf x.g)) →
      List.Forall₂ (CoveredIf s) (stagesPairs s eOf st) (stagesList s .once fm mr first st)
  | _, [], _ => by
      rw [stagesPairs, stagesList]
      exact .nil
  | _, [x], h => by
      rw [stagesPairs, stagesList]
      exact base_coveredIf (h x List.mem_cons_self) _
  | first, x :: y :: rest, h => by
      rw [stagesPairs, stagesList]
      exact forall₂_app (fold_coveredIf (h x List.mem_cons_self) _)
        (forall₂_app
          (cs_coveredIf hq (h x List.mem_cons_self)
            (h y (List.mem_cons_of_mem _ List.mem_cons_self)) _ _ _ _)
          (stages_coveredIf hq eOf fm mr false (y :: rest)
            fun z hz => h z (List.mem_cons_of_mem _ hz)))

/-- The counts of a proximity test are covered by the planner's list, pair by pair. -/
theorem test_covered {s : Setting} (hq : 2 ≤ s.cardE) (eOf : GroupSize → ℕ) (st : List StageSize)
    (rows fm : ℕ) (mr : Bool) (h : ∀ x ∈ st, StageOK s x.g (eOf x.g))
    (hg : ∀ y ∈ ioppList s .once st rows fm mr, y.Good s .once) :
    List.Forall₂ (Covered s .once) (testPairs s eOf st rows) (ioppList s .once st rows fm mr) := by
  refine forall₂_of_mem (P := fun y => y.Good s .once) ?_ hg
  unfold testPairs ioppList
  exact .cons (fun hb => Bat.covered_num s _ rows _ le_rfl (bad_of_good hb))
    (stages_coveredIf hq eOf fm mr true st h)

/-! ### smaller counts -/

theorem covered_mono {s : Setting} {c : Scope} {a b n : ℕ} {y : RoundSpec} (h : a ≤ b)
    (hb : Covered s c (b, n) y) : Covered s c (a, n) y := by
  unfold Covered at hb ⊢
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)) hb

/-- Pair by pair: at most as many bad values, of as many values. -/
def LePairs (l l' : List (ℕ × ℕ)) : Prop :=
  List.Forall₂ (fun p p' : ℕ × ℕ => p.1 ≤ p'.1 ∧ p.2 = p'.2) l l'

theorem covered_of_le {s : Setting} {c : Scope} :
    ∀ {l l' : List (ℕ × ℕ)} {ys : List RoundSpec}, LePairs l l' →
      List.Forall₂ (Covered s c) l' ys → List.Forall₂ (Covered s c) l ys
  | _, _, _, .nil, .nil => .nil
  | (_, _) :: _, (_, _) :: _, _, .cons h t, .cons h' t' => by
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h2
      exact .cons (covered_mono h1 h') (covered_of_le t t')

/-! ### a key's second chain -/

/-- The errors of a key's second chain, work counted, against the target. -/
theorem second_belowG {l : Lines} {shape : Plan.Shape} {z : KeySized} {σ : Setting} {P : Planned}
    (hz : keySized l shape = some z) (hP : secondPlan σ z.once = .ok P) (hq : 2 ≤ σ.cardE)
    (eOf : GroupSize → ℕ) (hS : ∀ x ∈ z.once.own.stages, StageOK σ x.g (eOf x.g))
    (sh : Iop.Shape) (g : GBits sh) (ε : Err sh)
    (hle : LePairs (ε.toList.zip sh.chalList)
      (testPairs σ eOf z.once.own.stages (2 + 3 * σ.samples)))
    (hg : bitsList g = (secondChainList σ .once z.once).map (heldWork σ .once)) :
    Err.BelowG g ε (ENNReal.ofReal ((2 : ℝ) ^ σ.target)⁻¹) :=
  belowG_of_plan (keySecond_is hz hP).1 sh g ε
    (covered_of_le hle (test_covered hq eOf _ _ _ _ hS (keySecond_is hz hP).1.good)) hg

end Cb.Pv.Tower

#print axioms Cb.Pv.Tower.test_covered
#print axioms Cb.Pv.Tower.covered_of_le
#print axioms Cb.Pv.Tower.second_belowG
