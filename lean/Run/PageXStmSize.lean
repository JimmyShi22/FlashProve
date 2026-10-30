-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageXStmSize.lean: the length of the statement of two tables (`twoItems`, Run/PageXStm.lean), as
a formula in the lengths of the two roots and the numbers of the two tables' answers.

Theorems; one definition (`stmInvTwoN`: data). Run/PageXStm.lean's `stmInvTwo` asks two bounds on
the bytes of the answers, and Run/PageXLax.lean [not in this library]'s `stmFits_all` a bound on the
statement of any two strings of 32 bytes. For answers that are not written out in a file of this
library, both are had from the numbers of the answers by the formulas here.

Main names:
  `size_listExt`: a list of n answers is spelled in 8 + 24 n bytes.
  `twoItems_size`: the statement's length, with the spelled lists' lengths in it;
    `twoItems_size_n`: with the numbers of the answers.
  `stmInvTwoN`: `stmInvTwo` from bounds on the numbers of the answers (each below 2^32).
  `twoItems_short`: under these bounds the statement of any two strings of 32 bytes has fewer than
    2^64 bytes.

Limits: lengths alone. Nothing on what a statement says, on any verifier, or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.PageXStm

set_option autoImplicit false

namespace Run.PQ

/-- An answer is spelled in 24 bytes. -/
theorem size_ext3 (e : W3) : (_root_.Fmt.ext e).size = 24 := by
  unfold _root_.Fmt.ext
  rw [ByteArray.size_append, ByteArray.size_append, _root_.Fmt.size_u64, _root_.Fmt.size_u64,
    _root_.Fmt.size_u64]

/-- The spellings of n answers, one after the other, have 24 n bytes. -/
theorem size_catExt : ∀ a : List W3, (_root_.Fmt.cat (a.map _root_.Fmt.ext)).size = 24 * a.length
  | [] => rfl
  | e :: a => by
    rw [List.map_cons, _root_.Fmt.cat_cons, ByteArray.size_append, size_ext3, size_catExt a,
      List.length_cons]
    omega

/-- A list of n answers is spelled in 8 + 24 n bytes. -/
theorem size_listExt (a : List W3) :
    (_root_.Fmt.list _root_.Fmt.ext a).size = 8 + 24 * a.length := by
  unfold _root_.Fmt.list
  rw [ByteArray.size_append, _root_.Fmt.size_u64n, size_catExt]

/-- The length of the statement of two tables. -/
theorem twoItems_size (a₀ a₁ : List W3) (r0 r1 : ByteArray) :
    (twoItems a₀ a₁ r0 r1).size =
      (_root_.Fmt.ascii "the first table").size + (_root_.Fmt.ascii "the further table").size +
        48 + r0.size + r1.size + (_root_.Fmt.list _root_.Fmt.ext a₀).size +
        (_root_.Fmt.list _root_.Fmt.ext a₁).size := by
  simp only [twoItems, tableItem_val, _root_.Fmt.item, _root_.Fmt.textS, _root_.Fmt.text,
    ByteArray.size_append, _root_.Fmt.size_u64n, tabVal_size]
  omega

/-- The same with the numbers of the answers. -/
theorem twoItems_size_n (a₀ a₁ : List W3) (r0 r1 : ByteArray) :
    (twoItems a₀ a₁ r0 r1).size = 96 + r0.size + r1.size + 24 * a₀.length + 24 * a₁.length := by
  have h1 : (_root_.Fmt.ascii "the first table").size = 15 := by decide
  have h2 : (_root_.Fmt.ascii "the further table").size = 17 := by decide
  rw [twoItems_size, size_listExt, size_listExt, h1, h2]
  omega

/-- The reader for the statement of two tables, from bounds on the numbers of their answers. -/
def stmInvTwoN (D : XD) (a₀ a₁ : List W3) (hs : D.stm = twoItems a₀ a₁) (h0 : a₀.length < 2 ^ 32)
    (h1 : a₁.length < 2 ^ 32) : StmInv D :=
  stmInvTwo D a₀ a₁ hs (by rw [size_listExt]; omega) (by rw [size_listExt]; omega)

/-- Under these bounds the statement of any two strings of 32 bytes has fewer than 2^64 bytes. -/
theorem twoItems_short (a₀ a₁ : List W3) (h0 : a₀.length < 2 ^ 32) (h1 : a₁.length < 2 ^ 32)
    (r0 r1 : ByteArray) (e0 : r0.size = 32) (e1 : r1.size = 32) :
    (twoItems a₀ a₁ r0 r1).size < 2 ^ 64 := by
  rw [twoItems_size_n, e0, e1]
  omega

end Run.PQ
