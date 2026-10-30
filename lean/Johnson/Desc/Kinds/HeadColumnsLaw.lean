-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/HeadColumnsLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE LAW OF A CALL'S COLUMNS
(HeadIn.lean's column): STATED HERE, proved in Law/Columns.lean. Definitions and nothing else.

WHY. The lookup takes from its caller, for each call, ONE form: the call's key vector at the call's
key point. Its law speaks of a table with 2^lJ columns of T keys. The caller's form is a sum over
KEYS AND ENTRIES under the entries' weights, and a padding term: the padding key times (1 less the
sum of all entries' weights). That this is a sum over COLUMNS needs: no two entries of a call take one
column, and every entry's column lies below 2^lJ.

  ColumnsStatement   the two facts, for any list of keys whose lengths are below 2^41.
  tableOf            a call's table at one position, column by column: the value of the entry that
                     takes the column; the padding's where no entry takes it.
  OverColumnsStatement  in any commutative ring: for weights w on the columns that add up to 1:
                     the sum over keys and entries of w (column) * value, and pad * (1 - the sum of
                     the entries' weights), is the sum over the columns of w * tableOf.

WHAT IT DOES NOT SAY. Which values stand in the table; that the weights are equality weights (they
are: LettersOk.column, HeadInLaw.lean); anything on a verifier, on probabilities, on hiding.

-/
import Mathlib
import Johnson.Desc.Kinds.HeadIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **No two entries take one column; every column lies below the sum of the lengths.** lens: the
lengths of a call's keys. An entry: key number s, entry x below that key's length. -/
def ColumnsStatement : Prop :=
  ∀ lens : List Nat, (∀ n ∈ lens, n < 2 ^ 41) →
    (∀ s x, x < lens.getD s 0 → column lens s x < lens.sum) ∧
    ∀ s x s' x', x < lens.getD s 0 → x' < lens.getD s' 0 →
      column lens s x = column lens s' x' → s = s' ∧ x = x'

/-- All entries of a call, each with its column and its value. g s x: the value of entry x of key
number s. -/
def entriesOf {α : Type} (lens : List Nat) (g : Nat → Nat → α) : List (Nat × α) :=
  (List.range lens.length).flatMap fun s =>
    (List.range (lens.getD s 0)).map fun x => (column lens s x, g s x)

/-- A call's table at a column. -/
def tableOf {α : Type} (lens : List Nat) (g : Nat → Nat → α) (pad : α) (col : Nat) : α :=
  ((entriesOf lens g).lookup col).getD pad

/-- **The caller's sum over keys and entries, with its padding term, is the sum over columns.** N: the
number of columns. -/
def OverColumnsStatement : Prop :=
  ∀ (R : Type) [CommRing R] (lens : List Nat) (N : Nat) (w : Nat → R) (g : Nat → Nat → R) (pad : R),
    (∀ n ∈ lens, n < 2 ^ 41) → lens.sum ≤ N → (Finset.range N).sum w = 1 →
    ((Finset.range lens.length).sum fun s => (Finset.range (lens.getD s 0)).sum fun x =>
        w (column lens s x) * g s x)
      + pad * (1 - (Finset.range lens.length).sum fun s =>
          (Finset.range (lens.getD s 0)).sum fun x => w (column lens s x))
      = (Finset.range N).sum fun col => w col * tableOf lens g pad col

end VerifiableInference.Desc.Kinds.Head.Law
