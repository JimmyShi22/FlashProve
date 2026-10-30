-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5BeforeBentDefs.lean: kind K5's row: **NEGATIVE TESTS OF before_closed
(Johnson/Desc/First/Att/Row/K5BeforeClosed.lean) THAT BEND THE INPUT, NOT THE WRITTEN SIDE: THE
DEFINITIONS, AND TWO GENERAL LAWS.** NOTHING IS EVALUATED HERE: NO DECISION.
WHY. A test "the computed column = a bent written column" says no by logic alone once the unbent
equation holds: it shows that the comparison can say no, nothing of the data. Here the DATA are bent
(the table of stretches; the list of roots), and the tests are stated
positively over a negation (moved: "it returns, and what it returns is not the written entry"): so
that a refusal FAILS the test instead of passing for it (moved_false_of_none).
A CONTROL OF THE CONTROL, NO TEST: beforeBy_struck is a general fact on beforeBy (behind the filter
no row bears the name, whatever the table); before_struck tells it at one point; moved_struck: there
"moved" says no: a refusal does not pass for a bite. NONE OF THE THREE CAN FAIL.
Main names (namespace H2K5.Row): cutPairsBent (the first stretch one round longer) · seedRootsBent
(the first pair declares one root more) · cutPairsStruck (the last segment's step ".2.scores"
struck) · beforeMovedB · beforeIsB · moved_false_of_none · beforeBy_struck ·
before_struck · moved_struck.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5BeforeClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

/-- The written table's pairs with the first stretch one round longer. -/
def cutPairsBent : List (String × ℕ) :=
  match cutPairsW with
  | [] => []
  | x :: l => (x.1, x.2 + 1) :: l

/-- The written roots with the first pair declaring one root more. -/
def seedRootsBent : List (ℕ × ℕ) :=
  match P5T.seedRoots with
  | [] => []
  | x :: l => (x.1, x.2 + 1) :: l

/-- The written table's pairs without the last segment's step ".2.scores". -/
def cutPairsStruck : List (String × ℕ) :=
  cutPairsW.filter fun c => c.1 != ("A" ++ toString 11) ++ ".2.scores"

/-- "before" RETURNS at each of the twelve, AND what it returns is NOT the written entry. A refusal
gives false. -/
def beforeMovedB (cuts : List (String × ℕ)) (roots : List (ℕ × ℕ)) : Bool :=
  (List.range 12).all fun g =>
    (beforeBy cuts (P5T.sumBelow roots) ("A" ++ toString g)).any fun c => c != [(1, 4 + 6 * g)]

/-- "before" at the twelve is the column want. -/
def beforeIsB (cuts : List (String × ℕ)) (roots : List (ℕ × ℕ)) (want : ℕ → List (ℕ × ℕ)) : Bool :=
  (List.range 12).all fun g =>
    decide (beforeBy cuts (P5T.sumBelow roots) ("A" ++ toString g) = some (want g))

/-- **A refusal fails the test "moved".** -/
theorem moved_false_of_none {cuts : List (String × ℕ)} {roots : List (ℕ × ℕ)} {g : ℕ} (hg : g < 12)
    (h : beforeBy cuts (P5T.sumBelow roots) ("A" ++ toString g) = none) :
    beforeMovedB cuts roots = false := by
  unfold beforeMovedB
  rw [List.all_eq_false]
  exact ⟨g, List.mem_range.2 hg, by rw [h]; exact Bool.false_ne_true⟩

/-- **Where the step nm ++ ".2.scores" is struck from the table, "before" answers nothing at nm: AT
EVERY TABLE.** -/
theorem beforeBy_struck (cuts : List (String × ℕ)) (rb : ℕ → ℕ) (nm : String) :
    beforeBy (cuts.filter fun c => c.1 != nm ++ ".2.scores") rb nm = none := by
  have h0 :
      ((cuts.filter fun c => c.1 != nm ++ ".2.scores").any fun c =>
        c.1 == nm ++ ".2.scores") = false := by
    rw [List.any_eq_false]
    intro c hc
    have h := (List.mem_filter.1 hc).2
    intro h'
    rw [bne, h'] at h
    exact Bool.false_ne_true h
  have h1 :
      rootsBy (cuts.filter fun c => c.1 != nm ++ ".2.scores") rb (nm ++ ".2.scores") = none := by
    unfold rootsBy roundsBy
    rw [h0]
    rfl
  unfold beforeBy
  rw [h1]
  cases rootsBy (cuts.filter fun c => c.1 != nm ++ ".2.scores") rb (nm ++ ".0.call") <;> rfl

/-- The general fact, told at one point: at the struck table "before" answers nothing at the last
segment. -/
theorem before_struck :
    beforeBy cutPairsStruck (P5T.sumBelow P5T.seedRoots) ("A" ++ toString 11) = none :=
  beforeBy_struck cutPairsW (P5T.sumBelow P5T.seedRoots) ("A" ++ toString 11)

/-- So the test "moved" says no there: a refusal does not pass for a bite. -/
theorem moved_struck : beforeMovedB cutPairsStruck P5T.seedRoots = false :=
  moved_false_of_none (g := 11) (by omega) before_struck

end H2K5.Row

#print axioms H2K5.Row.moved_false_of_none
#print axioms H2K5.Row.beforeBy_struck
#print axioms H2K5.Row.before_struck
#print axioms H2K5.Row.moved_struck
