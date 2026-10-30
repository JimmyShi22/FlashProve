-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LastJoint.lean: the last tree of the written proximity test, read off the oracle that
was sent.

A column of the last tree holds four symbols over the extension field: the main row's, the masking
word's beside it, the mask row's, the masking word's beside it. The format's decision reads them
from an opened column (Fmt/M1Dec.lean: `lastCol`). The block that takes the base case off
(OnBytes/Slice/Base.lean) speaks of a word and a masking word that are fixed before the last two
rounds. This file reads both off the written oracle, and shows that whatever the decision reads of
an opened column of that oracle is what the two hold.

Main definitions.
 `lastQ`      the four symbols in the column at a position of a written oracle.
 `lastColW`   the columns arranged in rows: one main row, one mask row, no fresh mask row.
 `lastMk`     the masking word's two symbols at each position.
Main theorem.
 `lastCol_tie`   if every column that a view shows under a tree's number is the oracle's, then the
                 four symbols that the decision reads at a position are those of `lastColW` and
                 `lastMk`.
Not claimed. Nothing on which columns a view shows.
-/
import OnBytes.Slice.Stage
import Fmt.M1Dec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

section
variable (d : PQ.RD) (o : (wRound d).Orc)

/-- The four symbols in the column at x of a written oracle; nothing if the column has not the
width of four symbols. -/
def lastQ (x : ℕ) : Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) :=
  match Fmt.M1.cutCol 0 2 2 (colW d o x) with
  | some ([a, b], [c, e]) => some (a, b, c, e)
  | _ => none

/-- The columns of the last tree, arranged in rows: one main row, one mask row, no fresh mask row.
Empty where the column has not the width of four symbols. -/
def lastColW (x : ℕ) : Fmt.M1.Col :=
  match lastQ d o x with
  | some q => ⟨#[q.1], #[q.2.2.1], #[]⟩
  | none => ⟨#[], #[], #[]⟩

/-- The masking word's two symbols in the column at x: the one beside the main row's symbol and the
one beside the mask row's. Both 0 where the column has not the width of four symbols. -/
def lastMk (x : ℕ) : Fmt.M1.E × Fmt.M1.E :=
  match lastQ d o x with
  | some q => (q.2.1, q.2.2.2)
  | none => (Fmt.Fld.zeroE, Fmt.Fld.zeroE)

/-- What `lastQ` gives is what `lastColW` and `lastMk` hold. -/
theorem lastQ_tie (x : ℕ) (q : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)
    (h : lastQ d o x = some q) :
    Fmt.M1.ent (lastColW d o x).main 0 = q.1 ∧ (lastMk d o x).1 = q.2.1 ∧
      Fmt.M1.ent (lastColW d o x).mask 0 = q.2.2.1 ∧ (lastMk d o x).2 = q.2.2.2 := by
  unfold lastColW lastMk
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩

end

/-- What the decision reads of the last tree is what the word and the masking word hold. -/
theorem lastCol_tie (V : Fmt.M1.View) (tree : ℕ) (d : PQ.RD) (o : (wRound d).Orc)
    (hV : ∀ x w, Fmt.M1.colAt V tree x = some w → w = colW d o x) (x : ℕ)
    (q : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) (h : Fmt.M1.lastCol V tree x = some q) :
    Fmt.M1.ent (lastColW d o x).main 0 = q.1 ∧ (lastMk d o x).1 = q.2.1 ∧
      Fmt.M1.ent (lastColW d o x).mask 0 = q.2.2.1 ∧ (lastMk d o x).2 = q.2.2.2 := by
  unfold Fmt.M1.lastCol at h
  cases hc : Fmt.M1.colAt V tree x with
  | none =>
    rw [hc] at h
    cases h
  | some w =>
    obtain rfl := hV x w hc
    rw [hc] at h
    exact lastQ_tie d o x q h

end OnBytes.Slice

#print axioms OnBytes.Slice.lastQ_tie
#print axioms OnBytes.Slice.lastCol_tie
