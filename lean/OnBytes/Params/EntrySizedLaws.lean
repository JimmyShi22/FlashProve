-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntrySizedLaws.lean: what a yes of `entrySized` says of its parts, for all lines.

`entrySized` (OnBytes/Params/Derive.lean) derives a table, sizes a link, numbers the chain's codes
and plans the chain's rounds. Two statements take a yes apart: `deriveTable` returned a table, and
the link, the codes and the plan are what `linkSized` on that table and `finishHeld` return; and the
numbers of the codes in a link's shape, with the list of codes, are what `ioppStages` returns on the
link's solved stages. With them a file that evaluates the planner at fixed lines can evaluate the
stages first and then number the codes of the stages as written out.





Main statements: `entrySized_parts`, `linkSized_stages`.
What is not claimed: that `entrySized` says yes at any lines. Nothing on what the sizes or the
plan's errors are worth. The program, that is the Lean port built from OnBytes/ and not the C++
verifier, does not call `entrySized`; it calls `linkSized` in `sized`
(OnBytes/Params/Configure.lean).

-/
import OnBytes.Params.Derive

namespace OnBytes.Params

/-- If `entrySized` answers, then `deriveTable` gave a table, `linkSized` on that table and an empty
list of codes gave the answer's link and codes, and `finishHeld` gave its plan. -/
theorem entrySized_parts {l : Lines} {y : LinkSized × Codes × Planned} (h : entrySized l = .ok y) :
    ∃ T, deriveTable (settingOf l) l = some T ∧
      linkSized (settingOf l) l T {} = some (y.1, y.2.1) ∧
      finishHeld (settingOf l) .once (linkPlan y.1) = .ok y.2.2 := by
  unfold entrySized at h
  cases hT : deriveTable (settingOf l) l with
  | none => simp [hT, orRefuse, bind, Except.bind] at h
  | some T =>
    cases hL : linkSized (settingOf l) l T {} with
    | none => simp [hT, hL, orRefuse, bind, Except.bind] at h
    | some xc =>
      obtain ⟨x, codes⟩ := xc
      cases hP : finishHeld (settingOf l) .once (linkPlan x) with
      | error e => simp [hT, hL, hP, orRefuse, bind, Except.bind] at h
      | ok p =>
        simp [hT, hL, hP, orRefuse, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨T, rfl, hL, hP⟩

/-- If `linkSized` answers, then `ioppStages` on the answer's solved stages and the given list of
codes returned a first stage, the later stages and the answer's list of codes; the shape's two
numbers of codes are the first stage's, and its later stages are these. -/
theorem linkSized_stages {s : Setting} {l : Lines} {T : TableSize} {codes codes' : Codes}
    {x : LinkSized} (h : linkSized s l T codes = some (x, codes')) :
    ∃ g later, ioppStages x.linked.stages codes = (g :: later, codes') ∧
      x.shape.code = g.code ∧ x.shape.maskCode = g.maskCode ∧ x.shape.later = later := by
  unfold linkSized at h
  dsimp only at h
  generalize scopePositions s Scope.once
    (tableAnalysis s T).later.agree = first at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨t, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i g later c' hio
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hc⟩ := h
    subst hx
    subst hc
    exact ⟨g, later, hio, rfl, rfl, rfl⟩
  · cases h

end OnBytes.Params
