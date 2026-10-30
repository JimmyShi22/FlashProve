-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/GroupJohnson.lean: what a group's analysis under the rule `johnson` encloses, for the
main code and for the mask code.

Under the rule `johnson` a group's analysis is `analysisOfM s g` (`analysis_johnson`;
OnBytes/Params/Group.lean). One distance serves main and mask rows. It is made from one of the two
codes at the group's integer m (`johnson`), and the other code is read at it (`atDistance`); the
mask code is read as its repetition to the main code's length, and where its source is not `.third`
its count has its list size added. `rulingWord g` is the code that gives the distance, and
`groupAgree s g` the agreement that belongs to its m, as a real number. With
OnBytes/Params/JohnsonLaws.lean and OnBytes/Params/AtDistanceJohnson.lean: where the main code's
source is `.johnson` and its count is not marked bad, its agreement, distance and count enclose the
group's agreement, 1 less that, and `countAt` at the main code's rate, that distance and the main
code's own m; 3 ≤ m; and, with m as printed, the group's agreement is at least the agreement that
belongs to that m (`analysisOfM_main`). The like for the mask code of a group with mask rows, at the
repeated code's rate, with the list size added to `countAt` (`analysisOfM_mask`). So under the same
conditions, with m as printed, a radius that is at most 1 less the group's agreement, times the
length, has the slack that belongs to the code's own m: (m + 1) ^ 2 k n ≤ m ^ 2 (n - e) ^ 2
(`analysisOfM_main_slack`, `analysisOfM_mask_slack`). The length in the second law is the repeated
code's; where the main code's count is not marked bad the group has no shape fault, and the two
lengths are one (`analysisAt_noFault`, `analysisOfM_oneLength`, with `repeated_n`).
Beside: what `analysisAt` hands on (`analysisAt_mainAt`,
`analysisAt_mainJohnson`, `analysisAt_maskAt`), that `atDistance` hands the agreement on
(`atDistance_agree`), and what a sum that is not marked bad says of its arguments
(`add_good`).


Main definitions: `rulingWord`, `groupAgree`.
Main theorems: `add_good`, `atDistance_agree`, `analysis_johnson`, `analysisAt_noFault`,
`analysisAt_mainAt`, `analysisAt_mainJohnson`, `analysisOfM_main`, `analysisAt_maskAt`,
`analysisOfM_mask`, `analysisOfM_oneLength`, `analysisOfM_main_slack`, `analysisOfM_mask_slack`.
What is not claimed: what the head of OnBytes/Params/JohnsonLaws.lean does not claim of `countAt`.
That the count at the repeated code's rate, with the list size added, bounds anything of mask rows
whose symbols are copies in the main rows' leaves: the docstring of `analysisAt` gives the footing;
nothing of it is proved here. A mask code that is longer than the main code is read as itself, at
its own length; that is a shape fault, which marks the main code's count bad, not the mask code's:
`analysisOfM_mask` then speaks of that code. Nothing on the list sizes. Nothing where a code's
source is `.third`. Nothing on the other rules, on a table's analysis
(OnBytes/Params/TableJohnson.lean), on which m the planner chooses, or on the rounds' prices that
are made of these counts. That k > 0, which `inJohnson_of_slack` and `countAt_mono` ask. That the
agreement's and the distance's own marks are good: each part speaks where its bound is not marked
bad. For proofs only; the program, that is the Lean port built from OnBytes/, does not import this
file.

-/
import OnBytes.Params.AtDistanceJohnson
import OnBytes.Params.KindLaws

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- In a group with a mask whose shape has no fault, the repeated mask code has the main code's
length. -/
theorem repeated_n {g : GroupSize} (hf : shapeFault g = false) (hm : g.hasMask = true) :
    (repeated g.mask g.main.logN).n = (wordOf g.main).n := by
  unfold shapeFault at hf
  simp only [hm, Bool.not_true, Bool.false_eq_true, if_false, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_lt] at hf
  have hle : g.mask.logN ≤ g.main.logN := hf.1.1
  unfold repeated
  split
  · rename_i h
    show 2 ^ g.mask.logN = 2 ^ g.main.logN
    rw [le_antisymm hle h]
  · rfl

/-- What a sum that is not marked bad says of its arguments. -/
theorem add_good {a b : Bound} (h : (a + b).bad = false) : a.bad = false ∧ b.bad = false :=
  inherit_good (r := ends (a.lo.add b.lo .down) (a.hi.add b.hi .up)) h

/-- Where `atDistance` gives a count that is not marked bad, it hands the agreement on. -/
theorem atDistance_agree {s : Setting} {c : Word} {agree : Bound}
    (hg : (atDistance s c agree).count.bad = false) : (atDistance s c agree).agree = agree := by
  unfold atDistance at hg ⊢
  dsimp only at hg ⊢
  split
  · rename_i h1
    rw [if_pos h1] at hg
    cases hg
  · repeat' split
    all_goals rfl

/-- Under the rule `johnson` the analysis is `analysisOfM`. -/
theorem analysis_johnson {s : Setting} {g : GroupSize} (h : g.rule = .johnson) :
    analysis s g = analysisOfM s g := by
  unfold analysis
  rw [h]

/-- Where the main code's count in `analysisAt` is not marked bad, the group has no shape fault. -/
theorem analysisAt_noFault {s : Setting} {g : GroupSize} {x : Proximity}
    (hg : (analysisAt s g x).mainAt.count.bad = false) : shapeFault g = false := by
  unfold analysisAt at hg
  dsimp only at hg
  by_cases hf : shapeFault g = true
  · rw [if_pos hf] at hg
    split at hg <;> cases hg
  · simpa using hf

/-- Where the main code's count in `analysisAt` is not marked bad, the main code's `Proximity` is
the one that was handed in. -/
theorem analysisAt_mainAt {s : Setting} {g : GroupSize} {x : Proximity}
    (hg : (analysisAt s g x).mainAt.count.bad = false) :
    (analysisAt s g x).mainAt = x ∧ x.count.bad = false := by
  unfold analysisAt at hg ⊢
  dsimp only at hg ⊢
  by_cases hf : shapeFault g = true
  · rw [if_pos hf] at hg
    split at hg <;> cases hg
  · rw [if_neg hf] at hg ⊢
    split at hg
    · rename_i hh
      rw [if_pos hh]
      exact ⟨rfl, hg⟩
    · rename_i hh
      rw [if_neg hh]
      exact ⟨rfl, hg⟩

/-- The main code in `analysisAt` where it was read by `atDistance` at an agreement that encloses
a. -/
theorem analysisAt_mainJohnson {s : Setting} {g : GroupSize} {agree : Bound} {a : ℝ}
    (ha : EnclR agree a)
    (hs : (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.source = .johnson)
    (hg : (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.count.bad = false) :
    EnclR (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.agree a ∧
      EnclR (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.delta (1 - a) ∧
      EnclR (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.count
        (countAt (wordOf g.main).n (wordOf g.main).rho (1 - a)
          (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.m) ∧
      3 ≤ (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.m ∧
      (s.printed = true → (wordOf g.main).agreeAt
        (analysisAt s g (atDistance s (wordOf g.main) agree)).mainAt.m true ≤ a) := by
  obtain ⟨e, hg'⟩ := analysisAt_mainAt hg
  rw [e] at hs ⊢
  obtain ⟨h1, h2, h3, h4⟩ := atDistance_johnson ha hs hg'
  refine ⟨?_, h1, h2, h3, h4⟩
  rw [atDistance_agree hg']
  exact ha

/-- The word that gives a group's distance under the rule `johnson`, by `maskRules`: the mask code,
as its repetition to the main code's length, if its rate before the repetition is the larger one;
else the main code. -/
def rulingWord (g : GroupSize) : Word :=
  if maskRules g then repeated g.mask g.main.logN else wordOf g.main

/-- The agreement at which a group is read under the rule `johnson`, as a real number. -/
noncomputable def groupAgree (s : Setting) (g : GroupSize) : ℝ :=
  (rulingWord g).agreeAt g.m s.printed

/-- **The main code in a group's analysis under the rule `johnson`**, where its source is
`.johnson` and its count is not marked bad: agreement, distance and count enclose the group's
agreement, 1 less that, and `countAt` at the main code's rate, that distance and the main code's own
m; 3 ≤ m; and, with m as printed, the group's agreement is at least the agreement that belongs to
that m. -/
theorem analysisOfM_main {s : Setting} {g : GroupSize}
    (hs : (analysisOfM s g).mainAt.source = .johnson)
    (hg : (analysisOfM s g).mainAt.count.bad = false) :
    EnclR (analysisOfM s g).mainAt.agree (groupAgree s g) ∧
      EnclR (analysisOfM s g).mainAt.delta (1 - groupAgree s g) ∧
      EnclR (analysisOfM s g).mainAt.count (countAt (wordOf g.main).n (wordOf g.main).rho
        (1 - groupAgree s g) (analysisOfM s g).mainAt.m) ∧
      3 ≤ (analysisOfM s g).mainAt.m ∧
      (s.printed = true →
        (wordOf g.main).agreeAt (analysisOfM s g).mainAt.m true ≤ groupAgree s g) := by
  unfold groupAgree rulingWord
  by_cases hm : maskRules g = true
  · -- the mask code rules: the main code is read at the mask code's agreement
    rw [if_pos hm]
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).mainAt := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hs hg ⊢
    have ha := enclR_johnson_agree (repeated g.mask g.main.logN) g.m s.printed
    exact analysisAt_mainJohnson ha hs hg
  · -- the main code rules
    rw [if_neg hm]
    have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).mainAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hs hg ⊢
    obtain ⟨e, hg'⟩ := analysisAt_mainAt hg
    rw [e] at hs ⊢
    obtain ⟨h3, _⟩ := johnson_count_good hg'
    refine ⟨enclR_johnson_agree _ _ _, enclR_johnson_delta _ _ _, enclR_johnson_count _ _ _, h3, ?_⟩
    intro hp
    rw [hp]
    exact le_rfl

/-- The mask code in `analysisAt`, of a group with mask rows, where its source is `.johnson`: it is
what `atDistance` says of the repeated mask code at the main code's agreement, with the list size
added to the count. -/
theorem analysisAt_maskAt {s : Setting} {g : GroupSize} {x : Proximity} (hh : g.hasMask = true)
    (hs : (analysisAt s g x).maskAt.source = .johnson) :
    (analysisAt s g x).maskAt =
      { atDistance s (repeated g.mask g.main.logN) x.agree with
        count := (atDistance s (repeated g.mask g.main.logN) x.agree).count +
          Bound.ofNat (atDistance s (repeated g.mask g.main.logN) x.agree).list } := by
  unfold analysisAt at hs ⊢
  dsimp only at hs ⊢
  rw [if_pos hh] at hs ⊢
  dsimp only at hs ⊢
  split at hs
  · rename_i h3
    rw [if_pos h3]
  · rename_i h3
    simp only [bne_iff_ne, ne_eq, not_not] at h3
    rw [h3] at hs
    cases hs

/-- **The mask code in a group's analysis under the rule `johnson`**, of a group with mask rows,
where its source is `.johnson` and its count is not marked bad. The code is
`repeated g.mask g.main.logN`: the mask code's repetition to the main code's length, or the mask
code itself if it is not shorter. Agreement and distance enclose the group's agreement and 1 less
that; the count encloses `countAt` at the repeated code's rate, that distance and the mask code's
own m, and the list size more; 3 ≤ m; and, with m as printed, the group's agreement is at least the
agreement that belongs to that m. -/
theorem analysisOfM_mask {s : Setting} {g : GroupSize} (hh : g.hasMask = true)
    (hs : (analysisOfM s g).maskAt.source = .johnson)
    (hg : (analysisOfM s g).maskAt.count.bad = false) :
    EnclR (analysisOfM s g).maskAt.agree (groupAgree s g) ∧
      EnclR (analysisOfM s g).maskAt.delta (1 - groupAgree s g) ∧
      EnclR (analysisOfM s g).maskAt.count
        (countAt (repeated g.mask g.main.logN).n (repeated g.mask g.main.logN).rho
          (1 - groupAgree s g) (analysisOfM s g).maskAt.m + ((analysisOfM s g).maskAt.list : ℝ)) ∧
      3 ≤ (analysisOfM s g).maskAt.m ∧
      (s.printed = true → (repeated g.mask g.main.logN).agreeAt (analysisOfM s g).maskAt.m true ≤
        groupAgree s g) := by
  unfold groupAgree rulingWord
  by_cases hm : maskRules g = true
  · rw [if_pos hm]
    have hA : (analysisOfM s g).maskAt =
        { johnson (repeated g.mask g.main.logN) g.m s.printed with
          count := (johnson (repeated g.mask g.main.logN) g.m s.printed).count +
            Bound.ofNat (johnson (repeated g.mask g.main.logN) g.m s.printed).list } := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hs hg ⊢
    dsimp only at hs hg ⊢
    obtain ⟨g1, _⟩ := add_good hg
    obtain ⟨h3, _⟩ := johnson_count_good g1
    refine ⟨enclR_johnson_agree _ _ _, enclR_johnson_delta _ _ _,
      enclR_add (enclR_johnson_count _ _ _) (enclR_ofNat _), h3, ?_⟩
    intro hp
    rw [hp]
    exact le_rfl
  · rw [if_neg hm]
    have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).maskAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).maskAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hs hg ⊢
    have e := analysisAt_maskAt (s := s) (g := g) (x := johnson (wordOf g.main) g.m s.printed) hh hs
    generalize (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).maskAt = Z at e hs hg ⊢
    subst e
    dsimp only at hs hg ⊢
    obtain ⟨g1, _⟩ := add_good hg
    have ha := enclR_johnson_agree (wordOf g.main) g.m s.printed
    obtain ⟨h1, h2, h3, h4⟩ := atDistance_johnson ha hs g1
    refine ⟨?_, h1, enclR_add h2 (enclR_ofNat _), h3, h4⟩
    rw [atDistance_agree g1]
    exact ha

/-- **Where the main code's count in a group's analysis under the rule `johnson` is not marked bad,
the two codes of a group with mask rows are read at one length.** -/
theorem analysisOfM_oneLength {s : Setting} {g : GroupSize} (hh : g.hasMask = true)
    (hg : (analysisOfM s g).mainAt.count.bad = false) :
    (repeated g.mask g.main.logN).n = (wordOf g.main).n := by
  refine repeated_n ?_ hh
  by_cases hm : maskRules g = true
  · have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).mainAt := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hg
    exact analysisAt_noFault hg
  · have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).mainAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hg
    exact analysisAt_noFault hg

/-- **So, with m as printed, a radius that is at most 1 less the group's agreement, times the
length, has the slack that belongs to the main code's own m.** -/
theorem analysisOfM_main_slack {s : Setting} {g : GroupSize} {e : ℕ}
    (hs : (analysisOfM s g).mainAt.source = .johnson)
    (hg : (analysisOfM s g).mainAt.count.bad = false) (hp : s.printed = true)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)) :
    e ≤ (wordOf g.main).n ∧
      ((analysisOfM s g).mainAt.m + 1) * ((analysisOfM s g).mainAt.m + 1) * (wordOf g.main).k *
        (wordOf g.main).n ≤ (analysisOfM s g).mainAt.m * (analysisOfM s g).mainAt.m *
          (((wordOf g.main).n - e) * ((wordOf g.main).n - e)) := by
  obtain ⟨_, _, _, h3, h4⟩ := analysisOfM_main hs hg
  refine radius_slack (by omega) (he.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith [h4 hp]) (Nat.cast_nonneg _)

/-- **The like for the mask code**, as its repetition to the main code's length. -/
theorem analysisOfM_mask_slack {s : Setting} {g : GroupSize} {e : ℕ} (hh : g.hasMask = true)
    (hs : (analysisOfM s g).maskAt.source = .johnson)
    (hg : (analysisOfM s g).maskAt.count.bad = false) (hp : s.printed = true)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ)) :
    e ≤ (repeated g.mask g.main.logN).n ∧
      ((analysisOfM s g).maskAt.m + 1) * ((analysisOfM s g).maskAt.m + 1) *
        (repeated g.mask g.main.logN).k * (repeated g.mask g.main.logN).n ≤
          (analysisOfM s g).maskAt.m * (analysisOfM s g).maskAt.m *
            (((repeated g.mask g.main.logN).n - e) * ((repeated g.mask g.main.logN).n - e)) := by
  obtain ⟨_, _, _, h3, h4⟩ := analysisOfM_mask hh hs hg
  refine radius_slack (by omega) (he.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith [h4 hp]) (Nat.cast_nonneg _)

end OnBytes.Params

#print axioms OnBytes.Params.add_good
#print axioms OnBytes.Params.analysis_johnson
#print axioms OnBytes.Params.analysisAt_noFault
#print axioms OnBytes.Params.analysisOfM_oneLength
#print axioms OnBytes.Params.analysisOfM_main_slack
#print axioms OnBytes.Params.analysisOfM_mask_slack
#print axioms OnBytes.Params.atDistance_agree
#print axioms OnBytes.Params.analysisAt_mainAt
#print axioms OnBytes.Params.analysisAt_mainJohnson
#print axioms OnBytes.Params.analysisOfM_main
#print axioms OnBytes.Params.analysisAt_maskAt
#print axioms OnBytes.Params.analysisOfM_mask
