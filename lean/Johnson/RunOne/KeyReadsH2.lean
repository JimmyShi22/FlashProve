-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyReadsH2.lean: THE TWO CONDITIONS ON THE READING THAT THE
ROWS 2.1 | 2.2 | 2.4 | 2.5 OF THE KEY FILE's TABLE ASK (hpins:
Johnson/RunOne/KeyRow24.lean | KeyRow21.lean · SmpGrows: Johnson/RunOne/KeyRows2225.lean) ARE MET BY
THE TABLES' OWN READING BaseSt.h₂ (Johnson/RunOne/KeyOneReading.lean), AT EVERY BaseSt AND EVERY
PAIR OF RECORDS: by Lean: so the two bare «∀» have an instance that is not degenerate: the meant
one.
OBJECT: BaseSt.h₂ · USER: loc_back₂ | point_back₂ (hpins) · keeps₂_send2 | keeps₂_send5 (hG) at G₂
:= B.h₂ · LETTERS: T : BaseSt Cells M Smp Rec, free.
  samePins_h₂   records with one first component, the same messages and the same codes give the same
    samples and the same record of the stored table
  smpGrows_h₂   a sample that is read is read, the same, where every older message is as it was
Nothing on soundness.
-/
import Johnson.RunOne.KeyOneReading
import Johnson.RunOne.KeyRows2225

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound

variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec)

theorem samePins_h₂ : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles →
    z'.2.st.codes = z.2.st.codes → SamePins T.h₂ z z' := by
  intro z z' e1 ho hc
  refine ⟨fun j t => ?_, ?_⟩
  · simp only [BaseSt.h₂, BaseSt.smAt, e1, ho, hc]
  · show T.recOf z.1.1 = T.recOf z'.1.1
    rw [e1]

theorem smpGrows_h₂ : SmpGrows T.h₂ := by
  intro z z' e1 hc ho
  refine ⟨fun j t s hs => ?_, ?_⟩
  · simp only [BaseSt.h₂] at hs ⊢
    split_ifs at hs ⊢ with h
    · rw [e1]
      exact hs
    · obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.1 hs
      refine Option.bind_eq_some_iff.2 ⟨o, h1, ?_⟩
      unfold BaseSt.smAt at h2 ⊢
      obtain ⟨x, hx, h3⟩ := Option.bind_eq_some_iff.1 h2
      refine Option.bind_eq_some_iff.2 ⟨x, (ho o (Array.getElem?_eq_some_iff.1 hx).1).trans hx, ?_⟩
      rw [hc]
      exact h3
  · show T.recOf z'.1.1 = T.recOf z.1.1
    rw [e1]

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.samePins_h₂
#print axioms Johnson.RunOne.KeyRows23.smpGrows_h₂
