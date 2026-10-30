-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Back.lean: what rows say of words behind K14's second part of the last chain,
carried back in front of it. Theorems; no definition.

Why. The block lays one message (Omega's copy) and one open row (Dot). A table of this chain's
joints goes backwards: from "these rows hold of the witness's words behind the block" to "they hold
in front". For the rows that were there in front this is the library's law `Means.says_extends`
(Johnson/Desc/Means/Keeps.lean) at `Says`' frame. Omega's sample rows lie, in front, in the border's
copy of the shared chain's statement, on Omega's number there; behind, in this chain's statement,
renamed to Omega's number here.

Main names.
  `extends_of_says`: behind the block the statement is a later statement in the library's sense.
  `rows_back`: a row that has passed the tests in front says behind the block what it says in front.
  `open_row_back`: the own group's open row number i in front is its open row number i behind.
  `old_message_back`: a message that was there in front is there behind, the same record.
  `omega_rows_back`: if all sample rows of Omega's copy hold behind the block, all of Omega's sample
    rows hold in the border's copy of the shared statement.

The premises of `omega_rows_back`, by name. codes: the border's copy has this statement's codes (the
start's yes gives it: `start₃_inv`). alone: each of Omega's sample rows there names Omega's number
there alone (no law of these files states it). words: m' reads at Omega's number here what m reads
at its number there.

What reads no block (`oracles_renamed` · `coefficient_renamed` ·
`coefficient_off_names` · `tableSize_same` · `value_one` · `says_renamed`) stands in
Johnson/Desc/Third/Law/Renamed.lean, so that a file which reads no block can import it alone.



Limits. `rows_back` asks `Means.RowIn` of the row in front: no law of these files states it of the
own group's open rows or of a message's sample rows. Nothing on (Dot) itself. Every statement is of
the form "if `Says p s s'`": it is empty where the block never says yes. Nothing on soundness or on
hiding.
-/
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.Renamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-! ## The rows that were there in front -/

/-- Behind the block the codes are the same and every message that was there is there. -/
theorem extends_of_says (p : P₁₄) (s s' : S₃) (h : Says p s s') : Means.Extends s.st s'.st := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, fo, _, _⟩ := h
  refine ⟨hc, fun o x hx => ⟨x, ?_, rfl⟩⟩
  rw [fo o (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- **A row that has passed the tests in front says behind the block what it says in front.** -/
theorem rows_back (p : P₁₄) (s s' : S₃) (h : Says p s s') (G : OnBytes.Group) (row : OnBytes.Row)
    (hr : Means.RowIn s.st G row) (m : Means.Words K) :
    Means.Says ρ s'.st row m ↔ Means.Says ρ s.st row m :=
  Means.says_extends ρ (extends_of_says p s s' h) hr m

/-- The own group's open rows in front are its first open rows behind, in their order. -/
theorem open_row_back (p : P₁₄) (s s' : S₃) (h : Says p s s') :
    ∃ G G' : OnBytes.Group, s.st.groups[s.loc.own]? = some G ∧
      s'.st.groups[s.loc.own]? = some G' ∧ G'.rows.size = G.rows.size + 1 ∧
      ∀ i : Nat, i < G.rows.size → G'.rows[i]? = G.rows[i]? := by
  obtain ⟨_, _, G, dot, _, _, _, _, _, _, hG, _, _, _, hg, _⟩ := h
  refine ⟨G, _, hG, hg, Array.size_push _, fun i hi => ?_⟩
  have hne : i ≠ G.rows.size := Nat.ne_of_lt hi
  show (G.rows.push dot)[i]? = _
  rw [Array.getElem?_push, if_neg hne]

/-- A message that was there in front is there behind, the same record. -/
theorem old_message_back (p : P₁₄) (s s' : S₃) (h : Says p s s') (o : Nat)
    (ho : o < s.st.oracles.size) : s'.st.oracles[o]? = s.st.oracles[o]? := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, fo, _, _⟩ := h
  exact fo o ho

/-! ## Omega's sample rows -/

/-- **Omega's sample rows: if they hold behind the block, they hold in the border's copy of the
shared statement.** -/
theorem omega_rows_back (p : P₁₄) (s s' : S₃) (h : Says p s s') (m m' : Means.Words K)
    (codes : ∀ b, s.loc.border = some b → b.shared.st.codes = s.st.codes)
    (alone : ∀ b y, s.loc.border = some b → b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, ∀ x ∈ r.oracles, x = b.shared.omega)
    (words : ∀ b, s.loc.border = some b →
      ∀ pt i, m' s.st.oracles.size pt i = m b.shared.omega pt i)
    (hs : ∀ x', s'.st.oracles[s.st.oracles.size]? = some x' →
      Means.AllSay ρ s'.st x'.sampleRows.toList m') :
    ∃ b y, s.loc.border = some b ∧ b.shared.st.oracles[b.shared.omega]? = some y ∧
      Means.AllSay ρ b.shared.st y.sampleRows.toList m := by
  obtain ⟨b, y, _, _, hb, _, hy, _, _, hO, _, _, _, _, _, hc, _, _, _⟩ := h
  refine ⟨b, y, hb, hy, fun r hr => ?_⟩
  have ho : b.shared.omega < b.shared.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy).1
  have hn : s.st.oracles.size < s'.st.oracles.size := (Array.getElem?_eq_some_iff.1 hO).1
  refine (says_renamed ρ b.shared.st s'.st r b.shared.omega s.st.oracles.size ho hn
    (alone b y hb hy r hr)
    (tableSize_same b.shared.st s'.st _ _ y _ hy hO rfl (hc.trans (codes b hb).symm)) m m'
    (words b hb)).1 (hs _ hO (r.renamed s.st.oracles.size) ?_)
  show r.renamed s.st.oracles.size ∈ (y.sampleRows.map (·.renamed s.st.oracles.size)).toList
  rw [Array.toList_map]
  exact List.mem_map_of_mem hr

end VerifiableInference.Desc.Third.Law
