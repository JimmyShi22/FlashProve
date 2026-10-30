-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyLaws.lean: the table of joints of the key file: what a block without a round owes at its row, as a statement; and the first such law proved from named facts on the readers: rng.0.rows.
A block without a round draws nothing: its law has no error term: it is a tie: where its decide returns, «its outs and its ctx hold behind» gives «its ins and its ctx hold in front», at one witness, at the same oracles.
  QuietLaw          the tie, general in the row and in the block's decide
  SameTables        two statements have the same oracle messages' number and tables' sizes: then a row holds at the one just if it holds at the other (rowHolds_congr: proved)
  RowsLaidFacts     what rng.0.rows does, as facts on the readers at the state in front (s) and behind (s'): the statement's tables are not turned · B's oracle message is the same record · in front every lookup's rows are there, none
                    empty · every row of every lookup is among the group's open rows behind · B is sampled and has a sample row
  rngRows_tie       **proved**: under these facts: grows behind ⟹ rows l in front, for every lookup l below n, and srow 1 in front. (pin 1, the row's ctx, is carried by the reading's own law: it reads the sample off the record: not here.)
What is not here: that rng.0.rows has these facts (its files' to show, once the readers are filled: each is an equation on its state) · the promise's half (the book-keeping behind) · the layer's tie · V's sending's identity.
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)

/-- **What a block without a round owes at its row.** -/
def QuietLaw (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (r : KRow) (dec : S → Except String S) : Prop :=
  ∀ (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M), dec s = .ok s' →
    (∀ i ∈ r.outs ++ r.ctx, i.holds F G at_ Mg (p, s') y w) → ∀ i ∈ r.ins ++ r.ctx, i.holds F G at_ Mg (p, s) y w

end

/-- Two statements have the same number of oracle messages and the same tables' sizes. -/
def SameTables (A B : Statement) : Prop :=
  A.oracles.size = B.oracles.size ∧ ∀ o part, A.tableBits o part = B.tableBits o part

/-- A row holds at the one just if it holds at the other. -/
theorem rowHolds_congr (same : E → E → Prop) {A B : Statement} (h : SameTables A B) (val : Nat → Part → Nat → E) (r : OnBytes.Row) :
    RowHolds same A val r ↔ RowHolds same B val r := by
  unfold RowHolds
  rw [h.1]
  simp only [h.2]

section
variable {S Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders S)

/-- **What rng.0.rows does, as facts on the readers.** n: the number of lookups. -/
structure RowsLaidFacts (n : Nat) (s s' : S) : Prop where
  tables : SameTables (X.st s') (X.st s)
  /-- B's oracle message is not turned -/
  sameB : ∀ o, K.orc 1 = some o → (X.st s').oracles[o]? = (X.st s).oracles[o]?
  /-- in front: every lookup's rows are there, none empty -/
  there : ∀ l, l < n → ∃ rs, X.rowsAt s l = some rs ∧ rs ≠ []
  /-- every row of every lookup is among the group's open rows behind -/
  laid : ∀ l rs g Gr, l < n → X.rowsAt s l = some rs → X.grpB s' = some g → (X.st s').groups[g]? = some Gr → ∀ r ∈ rs, r ∈ Gr.rows.toList
  /-- B is sampled and has a sample row -/
  sampled : ∀ o x, K.orc 1 = some o → (X.st s).oracles[o]? = some x → x.sampled = true ∧ x.sampleRows.size ≠ 0

variable {P : Type} (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- **rng.0.rows' tie.** -/
theorem rngRows_tie (n : Nat) (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (H : RowsLaidFacts K X n s s')
    (h : (meaning₁ K R X near forms worth other).grows (p, s') y w) :
    (∀ l, l < n → (meaning₁ K R X near forms worth other).rows l (p, s) y w) ∧ (meaning₁ K R X near forms worth other).srow 1 (p, s) y w := by
  obtain ⟨g, Gr, o, x, hg, hG, ho, hx, _, hrows, hsmp⟩ := h
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨rs, hrs, hne⟩ := H.there l hl
    exact ⟨rs, hrs, hne, fun r hr => (rowHolds_congr _ H.tables _ r).1 (hrows r (H.laid l rs g Gr hl hrs hg hG r hr))⟩
  · have hx' : (X.st s).oracles[o]? = some x := (H.sameB o ho).symm.trans hx
    obtain ⟨h1, h2⟩ := H.sampled o x ho hx'
    exact ⟨o, x, ho, hx', h1, h2, fun r hr => (rowHolds_congr _ H.tables _ r).1 (hsmp r hr)⟩

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.rowHolds_congr
#print axioms VerifiableInference.Desc.Key.rngRows_tie
