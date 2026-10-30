-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OneRadOfPlan.lean: two stages of a proximity test (the kind K12) that have the
same numbers have the same radius, from a test that every plan of the planner has passed.

Why. The law of a proximity test reads a radius for each stage. Where the radii are looked up in the
planner's list of stages by the stage's nine numbers (the two codes, the numbers of row variables,
the positions), the look-up is well defined only if two stages with the same nine numbers have one
radius.
How. `radiusOf` (Johnson/Top/H/StageJ.lean) reads of a group the two codes and the integer m,
nothing else. Every stage's price stands beside a round of its test in the plan.
`Planned.oneDistance` (OnBytes/Params/Planner.lean) asks that two prices with the same codes have
one rule and one said m. The theorem asks
besides of every stage that its rule is johnson or named, or that its m is 0.
Main names:
  `radiusOf_congr`: the radius hangs on the two codes and m alone.
  `mem_stages_group`: each stage's price stands beside a round of the list `stagesList`.
  `oneChoice_mem`: what `oneDistance` says of two members.
  `OneRad σ st`: two stages of st with the same nine numbers have the same radius at the setting σ.
  `oneRad_of_oneDistance`: the theorem.
Limits: it says that the look-up is well defined on the planner's record. It does not say that the
radius which a price spends is the radius of the test. By evaluation, `oneDistance` alone does not
give `OneRad`: a list of stages laid by hand under the rules unique or third, with one set of nine
numbers and two values of m, passes the planner's own routine and has two radii. Nothing on
soundness. Nothing on hiding.

-/
import OnBytes.Params.PlanListsProx
import Johnson.Top.H.StageJ

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open Johnson.Top.H (stageOf radiusOf)

/-! ## What the planner's radius reads of a group -/

theorem k_congr {c c' : CodeSize} (h2 : c.ell = c'.ell) (h3 : c.r = c'.r) : c.k = c'.k := by
  unfold CodeSize.k CodeSize.dim
  rw [h2, h3]

theorem wordOf_congr {c c' : CodeSize} (h1 : c.logN = c'.logN) (h2 : c.ell = c'.ell)
    (h3 : c.r = c'.r) : wordOf c = wordOf c' := by
  unfold wordOf
  rw [h1, k_congr h2 h3]

theorem repeated_congr {c c' : CodeSize} (h1 : c.logN = c'.logN) (h2 : c.ell = c'.ell)
    (h3 : c.r = c'.r) (n : Nat) : repeated c n = repeated c' n := by
  unfold repeated
  rw [wordOf_congr h1 h2 h3, h1, k_congr h2 h3]

theorem analysisAt_delta (s : Setting) (g : GroupSize) (x : Proximity) :
    (analysisAt s g x).mainAt.delta = x.delta := by
  unfold analysisAt
  dsimp only
  split <;> split <;> rfl

/-- The distance of the analysis under the Johnson rule, written out. -/
theorem delta_ofM (s : Setting) (g : GroupSize) :
    (analysisOfM s g).mainAt.delta =
      if !maskRules g then (johnson (wordOf g.main) g.m s.printed).delta
      else (atDistance s (wordOf g.main)
        (johnson (repeated g.mask g.main.logN) g.m s.printed).agree).delta := by
  unfold analysisOfM
  split
  · exact analysisAt_delta _ _ _
  · exact analysisAt_delta _ _ _

/-- **The planner's radius reads the two codes' three numbers each, and m.** -/
theorem radiusOf_congr (σ : Setting) {g g' : GroupSize} (a1 : g.main.logN = g'.main.logN)
    (a2 : g.main.ell = g'.main.ell) (a3 : g.main.r = g'.main.r)
    (b1 : g.mask.logN = g'.mask.logN) (b2 : g.mask.ell = g'.mask.ell) (b3 : g.mask.r = g'.mask.r)
    (hm : g.m = g'.m) : radiusOf σ g = radiusOf σ g' := by
  have hr : maskRules g = maskRules g' := by
    unfold maskRules GroupSize.hasMask CodeSize.n
    rw [b2, k_congr a2 a3, k_congr b2 b3, a1, b1]
  unfold radiusOf
  rw [delta_ofM, delta_ofM, hr, wordOf_congr a1 a2 a3, repeated_congr b1 b2 b3, a1, hm]

/-! ## Every stage's choice stands beside a round of its test -/

theorem group_said (s : Setting) (c : Scope) (name : String) (why : ErrorKind) (e : Bound)
    (d : Draws) (b r a : Nat) : ((RoundSpec.said name why e d b r a).round s c).group = d.group :=
  rfl

theorem mem_stages_group (s : Setting) (c : Scope) (fm : Nat) (mr : Bool) :
    ∀ (st : List StageSize) (first : Bool), ∀ y ∈ st,
      ∃ x ∈ stagesList s c fm mr first st, (x.round s c).group = some (pricedOf y.g)
  | [], _, y, hy => by cases hy
  | [x], first, y, hy => by
    obtain rfl : y = x := List.mem_singleton.1 hy
    refine ⟨(baseList s c y.g (if mr then 0 else 1)).head (by simp [baseList]), ?_, rfl⟩
    unfold stagesList
    exact List.head_mem _
  | x :: z :: rest, first, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy'
    · refine ⟨foldFirst s y.g (if first then fm else if mr then 0 else 1), ?_, rfl⟩
      unfold stagesList foldList
      exact List.mem_append_left _ List.mem_cons_self
    · obtain ⟨w, hw, e⟩ := mem_stages_group s c fm mr (z :: rest) false y hy'
      refine ⟨w, ?_, e⟩
      unfold stagesList
      exact List.mem_append_right _ (List.mem_append_right _ hw)

/-! ## What oneChoice says of two members -/

theorem oneChoice_mem : ∀ (L : List PricedChoice), oneChoice L = true →
    ∀ g ∈ L, ∀ h ∈ L, g.main = h.main → g.mask = h.mask → g.rule = h.rule ∧ g.m = h.m
  | [], _, g, hg, _, _, _, _ => by cases hg
  | a :: L, hL, g, hg, h, hh, e1, e2 => by
    unfold oneChoice at hL
    rw [Bool.and_eq_true] at hL
    have key : ∀ x ∈ L, x.main = a.main → x.mask = a.mask → x.rule = a.rule ∧ x.m = a.m := by
      intro x hx f1 f2
      have := List.all_eq_true.1 hL.1 x hx
      simpa [f1, f2] using this
    rcases List.mem_cons.1 hg with rfl | hg' <;> rcases List.mem_cons.1 hh with rfl | hh'
    · exact ⟨rfl, rfl⟩
    · obtain ⟨q1, q2⟩ := key h hh' e1.symm e2.symm
      exact ⟨q1.symm, q2.symm⟩
    · exact key g hg' e1 e2
    · exact oneChoice_mem L hL.2 g hg' h hh' e1 e2

/-! ## The lemma -/

/-- Two stages of the list with the same nine numbers have one radius. -/
def OneRad (σ : Setting) (st : List StageSize) : Prop :=
  ∀ y ∈ st, ∀ y' ∈ st, stageOf y.g y.t = stageOf y'.g y'.t → radiusOf σ y.g = radiusOf σ y'.g

/-- **From the plan's own test that rounds which say the same two codes say the same choice.** P: a
plan whose rounds are those of a list of descriptions which holds the rounds of the stages st of a
proximity test. Asked besides, of every stage: its rule is `johnson` or `named`, or its m is 0.
`radiusOf` reads a group's m. -/
theorem oneRad_of_oneDistance {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (hP : P.rounds = l.map (·.round s c)) (h1 : P.oneDistance = true) (st : List StageSize)
    (fm : Nat) (mr : Bool) (hsub : ∀ x ∈ stagesList s c fm mr true st, x ∈ l)
    (hj : ∀ y ∈ st, y.g.rule = .johnson ∨ y.g.rule = .named ∨ y.g.m = 0) (σ : Setting) :
    OneRad σ st := by
  have hmem : ∀ y ∈ st, pricedOf y.g ∈ P.rounds.filterMap (·.group) := by
    intro y hy
    obtain ⟨x, hx, e⟩ := mem_stages_group s c fm mr st true y hy
    refine List.mem_filterMap.2 ⟨x.round s c, ?_, e⟩
    rw [hP]
    exact List.mem_map.2 ⟨x, hsub x hx, rfl⟩
  intro y hy y' hy' e
  unfold stageOf at e
  injection e with eC eZ _ _ _
  injection eC with a1 a2 a3
  injection eZ with b1 b2 b3
  obtain ⟨hr, hm⟩ := oneChoice_mem _ h1 _ (hmem y hy) _ (hmem y' hy')
    (by simp [pricedOf, a1, a2, a3])
    (by simp [pricedOf, GroupSize.hasMask, b1, b2, b3])
  have hm' : y.g.m = y'.g.m := hm
  refine radiusOf_congr σ a1 a2 a3 b1 b2 b3 ?_
  exact hm'

end H2K.Pub

#print axioms H2K.Pub.radiusOf_congr
#print axioms H2K.Pub.oneRad_of_oneDistance
