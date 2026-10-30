-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Admit.lean: the admitting of a sample's answers goes onward and leaves the
small record: what a run of the linear claim's shared rounds asks of what lies between a receiving
of oracle messages and the kind's note behind it.

Main names: onward_admitP, onward_sampleLoop.

What is not claimed. That a given block of a sending is made of a receiving and this loop is shown
where that block is written.

-/
import Johnson.Desc.K14.Law.RunSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground

/-- A message's sample is admitted: onward; no group's list turns; the small record stays. -/
theorem onward_admitP (d d' : St) (o : Nat) (rows : Array Row) (h : admitP d o rows = some d') :
    Onward d d' ∧ d'.loc = d.loc := by
  have g := admitP_grows d d' o rows h
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact ⟨⟨g, fun _ => ⟨[], by simp [rowsOn, admitted]⟩⟩, rfl⟩
  · cases h

/-- Message by message. -/
theorem onward_sampleLoop (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys ys' : List E) (d d' : St),
      sampleLoop groundG p codes seeds l ys d = some (d', ys') →
      Onward d d' ∧ d'.loc = d.loc := by
  intro l
  induction l with
  | nil =>
    intro ys ys' d d' h
    simp only [sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact ⟨Onward.refl _, rfl⟩
  | cons x l ih =>
    intro ys ys' d d' h
    obtain ⟨o, s⟩ := x
    simp only [sampleLoop] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i d1 h1
        obtain ⟨a, b⟩ := onward_admitP d d1 o _ h1
        obtain ⟨a', b'⟩ := ih _ _ _ _ h
        exact ⟨a.trans a', b'.trans b⟩

end Desc.K14.Law
