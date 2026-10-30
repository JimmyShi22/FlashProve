-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/AloneMeans.lean: of aloneIn (Johnson/Desc/Own/Alone.lean): what it checks, and how
it stands to the hand-written program's linAloneInItsTree (OnBytes/Iop/Lin.lean). Theorems. No block
imports this file.
  aloneIn_iff        aloneIn book o = true just where the book has a place p for o, a tree t at p's
                     number, and t's parts are o alone.
  aloneIn_older      a yes of aloneIn gives a yes of the program's test.
  older_parts        JUST WHERE THE TWO PART: the program's test says yes and aloneIn says no just
                     where the tree at that number has one part and that part is another number.
  they_part          a book at which they part: message 0's place names tree 0, whose one part is 1.
THE TWO ARE NOT EQUAL, ON PURPOSE. Nothing on soundness.

-/
import Johnson.Desc.Own.Alone
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem aloneIn_iff (book : TreeBook) (o : Nat) :
    aloneIn book o = true ↔
      ∃ p t, book.place[o]? = some p ∧ book.trees[p.1]? = some t ∧ t.parts = #[o] := by
  unfold aloneIn
  constructor
  · intro h
    split at h
    · rename_i t ht
      obtain ⟨p, hp, hq⟩ := Option.bind_eq_some_iff.1 ht
      exact ⟨p, t, hp, hq, by simpa using h⟩
    · cases h
  · rintro ⟨p, t, hp, ht, h1⟩
    simp [hp, ht, h1]

/-- A yes gives the program's yes. -/
theorem aloneIn_older (book : TreeBook) (o : Nat) (h : aloneIn book o = true) :
    linAloneInItsTree book o = true := by
  obtain ⟨p, t, hp, ht, h1⟩ := (aloneIn_iff book o).1 h
  simp [linAloneInItsTree, hp, ht, h1]

/-- Just where the two part. -/
theorem older_parts (book : TreeBook) (o : Nat) :
    (linAloneInItsTree book o = true ∧ aloneIn book o = false) ↔
      ∃ p t x, book.place[o]? = some p ∧ book.trees[p.1]? = some t ∧ t.parts = #[x] ∧ x ≠ o := by
  unfold linAloneInItsTree aloneIn
  cases hp : book.place[o]? with
  | none => simp
  | some p =>
    cases ht : book.trees[p.1]? with
    | none => simp [ht]
    | some t =>
      simp only [Option.bind_some, ht]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : t.parts.size = 1 := by simpa using h1
        obtain ⟨x, hx⟩ : ∃ x, t.parts = #[x] := by
          refine ⟨t.parts[0]'(by omega), ?_⟩
          apply Array.ext
          · simpa using h1'
          · intro i hi _
            have : i = 0 := by omega
            subst this
            rfl
        refine ⟨p, t, x, rfl, ht, hx, fun e => ?_⟩
        subst e
        simp [hx] at h2
      · rintro ⟨p', t', x, hp', ht', hx, hne⟩
        obtain rfl := Option.some.inj hp'
        rw [ht] at ht'
        obtain rfl := Option.some.inj ht'
        refine ⟨by simp [hx], ?_⟩
        simp [hx, hne]

/-- A book at which they part. -/
theorem they_part :
    linAloneInItsTree
        { trees := #[{ shape := default, parts := #[1] }], place := #[(0, 0)] } 0 = true ∧
      aloneIn
        { trees := #[{ shape := default, parts := #[1] }], place := #[(0, 0)] } 0 = false := by
  constructor <;> rfl

end VerifiableInference.Desc.Own
