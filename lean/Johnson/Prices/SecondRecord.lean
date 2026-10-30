-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/SecondRecord.lean: a proof's second chain at the typed full-size sizes of the setting
"record with work": its plan's 30 rounds are those of a typed list; each is covered by numbers made
of the proof library's counts and of its bound on the MAIN code's list; 19 of them have a price,
work counted, above 2 ^ -129; and such a plan exists.

A second chain is the request's own proximity test (`secondChainList`,
OnBytes/Params/PlanListsChains.lean). `secondList`: its list at `recordSet`, under a request's own
scope, at the typed stages `sharedOwn` (Johnson/Prices/SharedExists.lean). `AtRecordOwn x`: the
sizes x have these stages; no one-time test; masks are sent ahead and ride. For every such x and
every plan P that `secondPlan recordSet x` returns: the rounds of P are those of `secondList`
(`second_rounds_at`); the numbers `ioppCounts` (Johnson/Prices/Prox.lean) are at most their errors,
one by one (`second_covered`; at the last of the five stages the mask code gives the distance, and
there these numbers are too small to serve: said here without a theorem); which rounds pass `dear`
and `dearBare` (Johnson/Prices/Dear.lean, DearBare.lean) is `secondMarks` (`second_marks`).
`second_exists`: the typed sizes of Johnson/Prices/SharedExists.lean meet the conditions and have a
plan, which meets `Passes 20` (Johnson/Prices/SharedExists.lean). Beside: `listMax_le_largest`: the
library's bound on the list of a group's main code is at most the planner's list size for a message
that is tested in that group among others.

By `decide +kernel`, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `own_stages_test`, `secondList_good`, `secondList_both`, `secondSized_test`.

Main definitions: `secondList`, `secondMarks`, `AtRecordOwn`.
Main theorems: `listMax_le_largest`, `own_stages_test`, `secondList_covered`, `second_rounds_at`,
`second_covered`, `second_marks`, `second_exists`.
What is not claimed: what the heads of Johnson/Prices/Prox.lean, Dear.lean and SharedExists.lean do
not claim.

-/
import Johnson.Prices.ProxRecord
import Johnson.Prices.DearBare
import Johnson.Prices.SharedExists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- A group's list size is at most the largest among groups of which it is one. -/
theorem list_le_largest (s : Setting) {g : GroupSize} :
    ∀ {gs : List GroupSize}, g ∈ gs → (analysis s g).list ≤ largestList s gs
  | _ :: gs, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact (list_le_largest s h').trans (le_max_right _ _)

/-- **The library's bound on the list of a group's main code is at most the planner's list size for
a message that is tested in that group.** -/
theorem listMax_le_largest {s : Setting} {g : GroupSize} {e : ℕ} {gs : List GroupSize}
    (hg : g ∈ gs) (J : JohnsonPair s g e) :
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e ≤
      largestList s gs := by
  refine (listMax_le_pair J).trans ?_
  rw [← J.analysis_eq]
  exact list_le_largest s hg

/-- The rounds of a second chain at the typed stages. -/
def secondList : List RoundSpec :=
  ioppList recordSet .request sharedOwn (2 + 3 * recordSet.samples) 0 true

/-- Which of the 30 rounds hold with an error, whole and own, above half of what it may be. -/
def secondMarks : List Bool :=
  [false, false, true, true, true, true, true, false, true, false, true, true, true, true, false,
    false, false, true, true, true, false, true, false, true, true, true, false, false, true,
    true]

/-- The five typed stages pass the test. By evaluation in Lean's kernel. -/
theorem own_stages_test : (sharedOwn.all fun x => stageTest recordSet x.g) = true := by
  decide +kernel

/-- No bound of the 30 typed rounds is marked bad. By evaluation in Lean's kernel. -/
theorem secondList_good :
    (secondList.all fun y => !(y.bound recordSet .request).bad) = true := by
  decide +kernel

/-- The 30 typed rounds, one by one. By evaluation in Lean's kernel. -/
theorem secondList_both :
    (secondList.map fun y => both recordSet (y.round recordSet .request)) = secondMarks := by
  decide +kernel

/-- **Each of the 30 typed rounds is covered.** -/
theorem secondList_covered :
    List.Forall₂ (CoveredBy recordSet .request)
      (ioppCounts recordSet .request sharedOwn (2 + 3 * recordSet.samples)) secondList :=
  iopp_covered (plainScope_settingOf recordLines .request) rr_set.2 _ _ _ _
    (List.all_eq_true.mp own_stages_test)
    fun y hy => by simpa using List.all_eq_true.mp secondList_good y hy

/-- The sizes of a test on the table at which the typed list is the second plan's. -/
structure AtRecordOwn (x : LinSized) : Prop where
  oneTime : x.lines.oneTime = false
  own : x.own.stages = sharedOwn
  ahead : x.shape.masksAhead = true
  ride : x.shape.choice.masksRide = true

/-- **The rounds of every second plan at such sizes.** -/
theorem second_rounds_at {x : LinSized} {P : Planned} (hx : AtRecordOwn x)
    (h : secondPlan recordSet x = .ok P) :
    P.rounds = secondList.map (·.round recordSet .request) := by
  have hP := secondPlan_rounds h
  simp only [hx.oneTime, Bool.false_eq_true, ↓reduceIte] at hP
  have hr := hP.rounds
  unfold secondChainList at hr
  rw [hx.own, hx.ahead, hx.ride] at hr
  simpa [secondList] using hr

/-- **They are covered, one by one.** -/
theorem second_covered {x : LinSized} {P : Planned} (hx : AtRecordOwn x)
    (h : secondPlan recordSet x = .ok P) :
    List.Forall₂ (fun (cnt : ℝ) (r : PlanRound) => cnt ≤ ((r.error.val : ℚ) : ℝ))
      (ioppCounts recordSet .request sharedOwn (2 + 3 * recordSet.samples)) P.rounds := by
  rw [second_rounds_at hx h, List.forall₂_map_right_iff]
  exact secondList_covered

/-- **Which of them are dear.** -/
theorem second_marks {x : LinSized} {P : Planned} (hx : AtRecordOwn x)
    (h : secondPlan recordSet x = .ok P) : P.rounds.map (both recordSet) = secondMarks := by
  rw [second_rounds_at hx h, List.map_map]
  exact secondList_both

/-- The typed sizes meet the conditions and have a second plan that passes the public test on a
chain with at most 20 bits of work. By evaluation in Lean's kernel. -/
theorem secondSized_test :
    (sharedSized.any fun p => !p.1.lines.oneTime && decide (p.1.own.stages = sharedOwn) &&
      p.1.shape.masksAhead && p.1.shape.choice.masksRide &&
      (secondPlan recordSet p.1).toOption.any (passes 20)) = true := by
  decide +kernel

/-- **The laws on a second plan at the typed sizes are not empty.** -/
theorem second_exists : ∃ (x : LinSized) (P : Planned),
    AtRecordOwn x ∧ secondPlan recordSet x = .ok P ∧ Passes 20 P := by
  have h := secondSized_test
  cases hs : sharedSized with
  | none =>
    rw [hs] at h
    cases h
  | some p =>
    rw [hs] at h
    simp only [Option.any_some, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, h2⟩ := h
    cases hP : secondPlan recordSet p.1 with
    | error e =>
      rw [hP] at h2
      cases h2
    | ok P =>
      rw [hP] at h2
      exact ⟨p.1, P, ⟨a1, a2, a3, a4⟩, hP, passes_sound (by simpa [Except.toOption] using h2)⟩

end OnBytes.Params.Prices
