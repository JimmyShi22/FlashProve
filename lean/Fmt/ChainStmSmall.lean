-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStmSmall.lean: a statement under which a chain's description is in order is within the
format page's bound on what is hashed, and so has fewer than 2 ^ 64 bytes, under the hypotheses
counted below. (A chain is the non-interactive form of one protocol. Its description, a `SpecX`, is
what the library's reader of a chain, `readChainX`, follows; `Declared.spec` makes one from a
`Declared`, the library's description of what is public, and a statement that it is handed.)
The format page (docs/format/FORMAT.md) bounds every hashed string: at most 2 ^ 32 - 144 bytes
(R2.3), and a verifier rejects a statement that would make a longer one (R2.7). The library has that
test: `Spec.small`, the first clause of `Spec.ok`, which is the first of `SpecX.ok` ("in order");
`readChainX` begins with `SpecX.ok`. The test counts 88 bytes around the statement in `firstBytes`,
the string that is hashed for a chain's first value: the parameters' digest (32), the statement's
length (8), the record field's length (8), no byte of a record field (R4.6: no chain of the format
fills it), the word 1 (8) and the run's value (32). In a chain without random bytes the last two are
the word 0 alone, so there the test asks 32 bytes more than the hashed string has.
States (seven theorems; three name single clauses or fields):
(1) `Declared.spec_ok_small`, `Declared.spec_ok_lt` (2 hypotheses each): if `Declared.spec` gives
    the description S at a statement, and `S.ok = true`, the statement with 88 bytes more has at
    most 2 ^ 32 - 144 bytes; and it has fewer than 2 ^ 64 bytes.
(2) `Declared.entryFormOk_count`, `Declared.entryFormOk_fitsWord` (2 hypotheses each): if the tests
    on a link (the chain of an entry file), `Declared.entryFormOk`, pass at a statement that has the
    form (`EntryStm.ok`), the shape's `TableShape.count` n (how many stored answers a table has:
    2 ^ logRows times the shape's number `answers`) has 248 + 48 n ≤ 2 ^ 32 - 144; and
    `TableShape.fitsWord` is true, a hypothesis of eight theorems of Fmt/ChainStmLaws.lean. (That
    alone follows from less: `TableShape.fitsWord_of_ok` there.)
Under: the two hypotheses named at each; none on a hash: no theorem here has a hash among its
arguments.
Does not show:
(1) No theorem here says when `Declared.spec` gives a description or when that is in order.
(2) Nothing on a chain that was not run under such a description: the hypothesis is `SpecX.ok` at
    the very statement, which whoever calls `readChainX` runs, and which `Declared.keyFormOk` and
    `Declared.proofFormOk` (Fmt/Parsed.lean) do not run; `Declared.entryFormOk` runs it for a link.
(3) The tests (OnBytes/Entry/TestRecordToyDeclared.lean has these three among its five: that the
    hypotheses of (1) are met together, that under another setting the second is not, that those of
    (2) are met together) are at a toy link's chain. No description of a key's or a proof's chain is
    tried. The toy link is the programs' own honest toy: made-up data, no model and no weights.
(4) `Declared.entryFormOk_count` serves the theorems on a key's or a proof's statements only by way
    of an entry's statement that has the form and passes `Declared.entryFormOk` under the same
    declared structure.
(5) No Mathlib, neither directly nor through the imports.
Notes in full, with every limit at length, stand at the end of this file.

-/
import Fmt.ChainStmLaws
import Fmt.Rules8Ok

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-- The clause of `Spec.small` on the statement (R2.3, R2.7). -/
theorem Spec.small_statement (S : Spec) (h : S.small = true) :
    S.statement.size + 88 ≤ 2 ^ 32 - 144 := by
  unfold Spec.small at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- The first clause of `SpecX.ok`. -/
theorem SpecX.ok_base (S : SpecX) (h : S.ok = true) : S.base.ok = true := by
  unfold SpecX.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- The description that `Declared.spec` gives holds the statement that it was handed. -/
theorem Declared.spec_statement (D : Declared) (c : ChainDecl) (cfg statement : ByteArray)
    (earlier : List (List ByteArray × ByteArray)) (S : SpecX)
    (h : D.spec c cfg statement earlier = some S) : S.base.statement = statement := by
  unfold Declared.spec at h
  obtain ⟨rand, -, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨rs, -, h2⟩ := Option.map_eq_some_iff.1 h1
  rw [← h2]

/-- If the description of a chain at a statement is in order, the statement and the 88 bytes around
it in the first query are within the page's bound (R2.3, R2.7). -/
theorem Declared.spec_ok_small (D : Declared) (c : ChainDecl) (cfg statement : ByteArray)
    (earlier : List (List ByteArray × ByteArray)) (S : SpecX)
    (h : D.spec c cfg statement earlier = some S) (hok : S.ok = true) :
    statement.size + 88 ≤ 2 ^ 32 - 144 := by
  have a := Spec.small_statement S.base (ok_small (SpecX.ok_base S hok))
  rw [Declared.spec_statement D c cfg statement earlier S h] at a
  exact a

/-- The same premises: the statement has fewer than 2 ^ 64 bytes. -/
theorem Declared.spec_ok_lt (D : Declared) (c : ChainDecl) (cfg statement : ByteArray)
    (earlier : List (List ByteArray × ByteArray)) (S : SpecX)
    (h : D.spec c cfg statement earlier = some S) (hok : S.ok = true) :
    statement.size < 2 ^ 64 := by
  have a := Declared.spec_ok_small D c cfg statement earlier S h hok
  omega

/-- Where the tests on an entry's link (`Declared.entryFormOk`) pass at a statement with the form
(`EntryStm.ok`), the link's statement, 160 bytes and 48 for each of the `TableShape.count` answers
(2 ^ logRows times the shape's number `answers`), is with its 88 bytes within the page's bound.
`Declared.entryFormOk` runs `SpecX.ok` at that statement. -/
theorem Declared.entryFormOk_count (D : Declared) (cfg : ByteArray) (x : EntryStm)
    (h : D.entryFormOk cfg x = true) (hx : x.ok D = true) :
    248 + 48 * D.table.count ≤ 2 ^ 32 - 144 := by
  unfold Declared.entryFormOk at h
  simp only [Bool.and_eq_true] at h
  have a : ((D.spec D.link cfg x.bytes).any fun S => S.ok) = true := h.1.1.2
  unfold EntryStm.ok at hx
  simp only [Bool.and_eq_true] at hx
  have n := EntryStm.bytes_size_ok D.setting.field D.table x hx.1 hx.2
  cases e : D.spec D.link cfg x.bytes with
  | none => rw [e] at a; exact absurd a (by simp)
  | some S =>
    rw [e] at a
    have b := Declared.spec_ok_small D D.link cfg x.bytes [] S e a
    omega

/-- The same premises give the premise hs of eight theorems of Fmt/ChainStmLaws.lean. -/
theorem Declared.entryFormOk_fitsWord (D : Declared) (cfg : ByteArray) (x : EntryStm)
    (h : D.entryFormOk cfg x = true) (hx : x.ok D = true) : D.table.fitsWord = true := by
  have a := Declared.entryFormOk_count D cfg x h hx
  exact (TableShape.fitsWord_iff D.table).2 (by omega)

end Fmt

#print axioms Fmt.Spec.small_statement
#print axioms Fmt.SpecX.ok_base
#print axioms Fmt.Declared.spec_statement
#print axioms Fmt.Declared.spec_ok_small
#print axioms Fmt.Declared.spec_ok_lt
#print axioms Fmt.Declared.entryFormOk_count
#print axioms Fmt.Declared.entryFormOk_fitsWord

/-
Notes in full.

Fmt/ChainStmSmall.lean: a statement under which a chain's description is in order is within the
format page's bound on what is hashed, and so has fewer than 2 ^ 64 bytes.
It stands on Fmt/Parsed.lean (`Declared.spec`), on Fmt/Rules8.lean, Rules8X.lean, Rules8Ok.lean, and
for the last two theorems on Fmt/ChainStm.lean (`TableShape.fitsWord`) and Fmt/ChainStmLaws.lean
(`EntryStm.bytes_size_ok`, `TableShape.fitsWord_iff`).

In plain words. The format page bounds every hashed string: at most 2 ^ 32 - 144 bytes (R2.3), and a
verifier rejects a statement that would make a longer one (R2.7). The library has that test
(`Spec.small`, the first clause of `Spec.ok`, which is the first of `SpecX.ok`), and its reader of a
chain (`readChainX`, Fmt/Rules8X.lean) begins with `SpecX.ok`. The description that
`Declared.spec` makes holds the statement that it was handed. So: if that description is in order,
the statement with the 88 bytes around it (see below) is within the page's bound. The laws of
Fmt/ChainStmLaws.lean and the library's `firstBytes_inj` (Fmt/Rules4Laws.lean) ask "fewer than
2 ^ 64 bytes", which follows.

The 88 is `Spec.small`'s number. In `firstBytes` (Fmt/Rules4.lean) there stand around the statement:
the parameters' digest (32 bytes), the statement's length (8), the record field's length (8), no
byte of a record field (R4.6: no chain of the format fills it; `startChainW` hands the empty
string), the word 1 (8) and the run's value (32). In a chain without random bytes (case (c) of R4.5)
the last two are the word 0 alone, so there the test asks 32 bytes more than the hashed string has.

1. What the file contains. Seven theorems.
    `Spec.small_statement`: the clause of `Spec.small` on the statement, under a name.
    `SpecX.ok_base`: the first clause of `SpecX.ok`, under a name.
    `Declared.spec_statement`: the description holds the statement that `Declared.spec` was handed.
    `Declared.spec_ok_small`: the page's bound, from "the description is in order".
    `Declared.spec_ok_lt`: fewer than 2 ^ 64 bytes, from the same.
    `Declared.entryFormOk_count`: where the tests on a link pass at a statement with the form, the
      shape's `TableShape.count` n (2 ^ logRows times its number `answers`) has
      248 + 48 n ≤ 2 ^ 32 - 144.
    `Declared.entryFormOk_fitsWord`: and so `TableShape.fitsWord` (Fmt/ChainStm.lean). (That alone
      follows from less: `Declared.entryFormOk` asks `TableShape.ok`, by way of
      `Declared.settingOk`, and the inequality of `TableShape.fitsWord` is the last clause of
      `TableShape.ok`: `TableShape.fitsWord_of_ok`, Fmt/ChainStmLaws.lean. The bound of the theorem
      before it is the page's, far below, and does not follow from `TableShape.ok`.)

2. What is checked when the file compiles. The proofs. Tests:
OnBytes/Entry/TestRecordToyDeclared.lean has these three among its five: the two premises of
`Declared.spec_ok_small` and `Declared.spec_ok_lt` are met together at a toy link; under another
setting the second is not; the two premises of the last two theorems are met together at that toy
link.

3. What is not claimed.
   No theorem here says when `Declared.spec` gives a description or when that is in order.
   Nothing on a chain that was not run under such a description: the premise is `SpecX.ok` at the
   very statement, which whoever calls `readChainX` runs, and which `Declared.keyFormOk` and
   `Declared.proofFormOk` (Fmt/Parsed.lean) do not run; `Declared.entryFormOk` runs it for a link.
   Those tests are at a link's chain. No description of a key's or a proof's chain is tried. The toy
   link is the programs' own honest toy: made-up data, no model and no weights.
   `Declared.entryFormOk_count` serves the laws on a key's or a proof's statements only by way of an
   entry's statement that has the form and passes `Declared.entryFormOk` under the same declared
   structure.
   No Mathlib, neither directly nor through the imports.
-/
