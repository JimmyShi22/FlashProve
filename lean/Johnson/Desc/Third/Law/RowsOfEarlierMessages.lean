-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/RowsOfEarlierMessages.lean: a row that names older messages alone says of words, behind a block
of the last chain, what it says in front. Theorems; no definition.

Main names.
  `extends_of_later`: our `Later` gives the library's `Means.Extends`.
  `old_says`: `Carries s.st s'.st` and a row that names messages of s.st alone: of all words it says
    the same at s'.st and at s.st. An iff.
  `old_rows_back`: from `Says p s s'`: if all the own group's open rows behind the block hold of m,
    all its open rows in front hold of m, read in the statement in front.

The premise of `old_rows_back`, by name. names: every open row of the own group in front names
messages of the statement in front alone. It is weaker than `Means.RowIn` of these rows, which
`rows_back` (Johnson/Desc/Third/Law/Back.lean) asks. No law of these files states it.

The proof of `old_says` goes by `Means.value_extends` (Johnson/Desc/Means/Keeps.lean) and our
`coefficient_off_names`. Kin in this library: `Desc.K14.Law.says_grows`
(Johnson/Desc/K14/Law/Carry.lean) states the like along `Grows`, over a field; `Means.says_grows`
(Johnson/Desc/Means/GrowsTie.lean) asks `Means.RowIn` of the row. `old_says` goes along our
`Carries`, over a commutative ring.

Limits. One m on both sides. Sample rows lie in a message's record, not on a group: the like holds
by `old_says`, row by row. Every statement on the block is of the form "if `Says p s s'`". Nothing
on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.Renamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open VerifiableInference.Desc.Later (Later Carries)

namespace VerifiableInference.Desc.Third.Law

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- A statement that is later in our sense is later in the library's sense. -/
theorem extends_of_later {T T' : Statement} (h : Later T T') : Means.Extends T T' :=
  ⟨h.codes, fun o x hx => by
    obtain ⟨x', hx', l⟩ := h.oracles o x hx
    exact ⟨x', hx', l.shape⟩⟩

/-- **A row that names older messages alone says the same behind the block as in front.** -/
theorem old_says (s s' : S₃) (hk : Carries s.st s'.st) (r : OnBytes.Row)
    (hr : ∀ o ∈ r.oracles, o < s.st.oracles.size) (m : Means.Words K) :
    Means.Says ρ s'.st r m ↔ Means.Says ρ s.st r m := by
  unfold Means.Says
  rw [Means.value_extends ρ (extends_of_later hk.1.1) r m fun o ho pt i =>
    coefficient_off_names ρ r o (fun hm => absurd (hr o hm) (Nat.not_lt.2 ho)) pt i]

/-- **The own group's open rows in front hold, if those behind do.** -/
theorem old_rows_back (p : P₁₄) (s s' : S₃) (h : Says p s s') (hk : Carries s.st s'.st)
    (m : Means.Words K)
    (names : ∀ G, s.st.groups[s.loc.own]? = some G → ∀ r ∈ G.rows.toList, ∀ o ∈ r.oracles,
      o < s.st.oracles.size)
    (hs : ∀ G', s'.st.groups[s.loc.own]? = some G' → Means.AllSay ρ s'.st G'.rows.toList m) :
    ∀ G, s.st.groups[s.loc.own]? = some G → Means.AllSay ρ s.st G.rows.toList m := by
  obtain ⟨_, _, G₀, dot, _, _, _, _, _, _, hG₀, _, _, _, hG', _, _, _, _⟩ := h
  intro G hG r hr
  obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
  refine (old_says ρ s s' hk r (names G₀ hG r hr) m).1 (hs _ hG' r ?_)
  show r ∈ (G₀.rows.push dot).toList
  rw [Array.toList_push]
  exact List.mem_append_left _ hr

end VerifiableInference.Desc.Third.Law
