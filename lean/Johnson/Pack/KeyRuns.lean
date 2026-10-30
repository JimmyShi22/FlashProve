-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/KeyRuns.lean: keys in parts that cover the rows of a forest in any order: the parts lie
in the table if and only if the forest does.

Definitions, statements and proofs. Johnson/Pack/KeyHalf.lean cuts a forest in consecutive blocks.
The programs may lay the rows of keys of a forest on the places of its parts in another order, with
padding between. Keys that are affine in one column of the index matrix are given row by row, by an
offset and row factors. "All keys lie in the table" is then a statement on rows of keys, and it does
not see their order.
Main names:
  `keyOf k o co M`: the keys with the offsets o, the row factors co, over the matrix M: the form of
    `LinKeys` (Cb/Ld/LdWfKeys.lean).
  `rowOK`: all 2^k keys of a row of keys, given by its offset and its row factors, lie in the table.
  `inTable_rowOK`: the keys of a forest of R row variables lie in the table if and only if each of
    its 2^R rows of keys is `rowOK`.
  `rowOK_pad`: a row of keys without a row factor, whose offset is an entry of the table, is
    `rowOK`.
  `Covers`, `inT_cover`: if every place of every part is padding or has the offset and the row
    factors of some row of the forest, and every row of the forest is idle or is had at some place
    of some part, then all parts lie in the table if and only if the forest does. No order, no
    injectivity and no count is asked.
Limits: the two conditions of `Covers` are hypotheses; no runs of rows of any program are given
here. Nothing on multiplicities: padding that a lookup does not count is not spoken of.
-/
import Johnson.Pack.KeyHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Blocks Cb.Lkp

section
variable {E : Type} [Field E] {Rw : Type} [Fintype Rw] (k d : ℕ) (tab : ℕ → E)
  (M : Rw × (Fin k → Bool) → E)

/-- The keys with the offsets o and the row factors co, over the matrix M. -/
def keyOf (o : ℕ → E) (co : ℕ → Rw → E) (b : ℕ) : E :=
  o (b / 2 ^ k) + ∑ r, co (b / 2 ^ k) r * M (r, Alg.bits k (b % 2 ^ k))

/-- All keys of one row of keys lie in the table. -/
def rowOK (o : E) (co : Rw → E) : Prop :=
  ∀ c < 2 ^ k, ∃ t < 2 ^ d, o + ∑ r, co r * M (r, Alg.bits k c) = tab t

theorem keyOf_row (o : ℕ → E) (co : ℕ → Rw → E) (v c : ℕ) (hc : c < 2 ^ k) :
    keyOf k M o co (v * 2 ^ k + c) = o v + ∑ r, co v r * M (r, Alg.bits k c) := by
  have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  have e1 : (v * 2 ^ k + c) / 2 ^ k = v := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (v * 2 ^ k + c) % 2 ^ k = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  unfold keyOf
  rw [e1, e2]

/-- A forest lies in the table if and only if each of its rows of keys does. -/
theorem inTable_rowOK (R : ℕ) (o : ℕ → E) (co : ℕ → Rw → E) :
    InTable (R + k) d (keyOf k M o co) tab ↔ ∀ v < 2 ^ R, rowOK k d tab M (o v) (co v) := by
  rw [inTable_split]
  refine forall_congr' fun v => forall_congr' fun _ => forall_congr' fun c =>
    forall_congr' fun hc => ?_
  show (∃ u < 2 ^ d, keyOf k M o co (v * 2 ^ k + c) = tab u) ↔ _
  rw [keyOf_row k M o co v c hc]

/-- Padding: no row factor, and the offset is an entry of the table. -/
theorem rowOK_pad (o : E) (h : ∃ t < 2 ^ d, o = tab t) : rowOK k d tab M o (fun _ => 0) := by
  intro c _
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [Finset.sum_eq_zero fun r _ => zero_mul _, add_zero, e]

/-- The parts cover the forest. oA, coA: the forest's 2^R rows of keys. oB f, coB f: those of part
f < n, which has 2^(r f) places. -/
structure Covers (R n : ℕ) (r : ℕ → ℕ) (oA : ℕ → E) (coA : ℕ → Rw → E) (oB : ℕ → ℕ → E)
    (coB : ℕ → ℕ → Rw → E) : Prop where
  /-- a place is padding, or has the offset and the row factors of a row of the forest -/
  place : ∀ f < n, ∀ u < 2 ^ r f,
    (coB f u = (fun _ => 0) ∧ ∃ t < 2 ^ d, oB f u = tab t) ∨
      ∃ v < 2 ^ R, oB f u = oA v ∧ coB f u = coA v
  /-- a row of the forest is idle, or is had at a place of a part -/
  row : ∀ v < 2 ^ R,
    (coA v = (fun _ => 0) ∧ ∃ t < 2 ^ d, oA v = tab t) ∨
      ∃ f < n, ∃ u < 2 ^ r f, oB f u = oA v ∧ coB f u = coA v

/-- All parts lie in the table if and only if the forest does. -/
theorem inT_cover (R n : ℕ) (r : ℕ → ℕ) (oA : ℕ → E) (coA : ℕ → Rw → E) (oB : ℕ → ℕ → E)
    (coB : ℕ → ℕ → Rw → E) (h : Covers d tab R n r oA coA oB coB) :
    InTable (R + k) d (keyOf k M oA coA) tab ↔
      ∀ f < n, InTable (r f + k) d (keyOf k M (oB f) (coB f)) tab := by
  rw [inTable_rowOK]
  constructor
  · intro hA f hf
    rw [inTable_rowOK]
    intro u hu
    rcases h.place f hf u hu with ⟨e0, ht⟩ | ⟨v, hv, e1, e2⟩
    · rw [e0]
      exact rowOK_pad k d tab M _ ht
    · rw [e1, e2]
      exact hA v hv
  · intro hB v hv
    rcases h.row v hv with ⟨e0, ht⟩ | ⟨f, hf, u, hu, e1, e2⟩
    · rw [e0]
      exact rowOK_pad k d tab M _ ht
    · rw [← e1, ← e2]
      exact (inTable_rowOK k d tab M (r f) (oB f) (coB f)).1 (hB f hf) u hu

end
end Johnson.Pack

#print axioms Johnson.Pack.inTable_rowOK
#print axioms Johnson.Pack.inT_cover
