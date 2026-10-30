-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsPage.lean: the code of bodies that are strings, as the leaf code of the SIBLING's
page.

The sibling has its own code of leaf queries (`TypedOracleCompiler.Run.pLeaf n p`, from a partial code p of
BODIES) and its own data of a page (`TypedOracleCompiler.Run.PageC`), with the fields `leafP`, a partial
code of bodies, and `leafTag`, the law that what it writes begins with the 16 bits of the leaves'
number (of 164 or of 174). OnBytes/TypedOracleCompiler/Strings.lean has the identity on
the bodies that pass a test (`pBody`), one test (`ok164`), and a code of leaf queries of its own
(`pLeafS`). This file ties the two: `pBody ok164` meets the first alternative of `leafTag`
(`pBody_tag`); `pLeafS` writes and reads what the sibling's `pLeaf` over `pBody` writes and reads
(`pLeafS_put`, `pLeafS_parse`).

Main theorems: `pBody_tag`, `pLeafS_put`, `pLeafS_parse`.

Not claimed. No page is made: a page's other fields (the chain's data, the first query's code, the
total code behind the escape) are given by nobody here. `pBody ok164` can be no leaf code of the
LIBRARY's page, by type. MEETING `leafTag` IS NOT ENOUGH FOR A PAGE THAT FITS: with `pBody ok164` as
its leaf code the sibling's `PageFit` is false, whatever the salts' length and the spellings, at
every page whose test `leafOK` lets both through (the default does), since that code writes a body
of 16 bits AND one of 17, and the strings of both cannot be whole bytes (by hand; no Lean
statement). OnBytes/TypedOracleCompiler/StringsWhole.lean has a narrower test; OnBytes/TypedOracleCompiler/StringsRead.lean one that
meets the hypothesis on leaves of the sibling's `PageFit.of`; OnBytes/TypedOracleCompiler/StringsBoth.lean one for
both leaves' numbers. On stored leaves: OnBytes/TypedOracleCompiler/StringsStoredAt.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Strings
import OnBytes.TypedOracleCompiler.Run.CodingPage

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open _root_.Run (t164)

/-- What the identity on the bodies that pass `ok164` writes begins with the 16 bits of the leaves'
number: the law `leafTag` of the sibling's page. -/
theorem pBody_tag (y m : List Bool) (h : (pBody ok164).put y = some m) :
    16 ≤ m.length ∧ m.take 16 = t164 := by
  have h0 : (if ok164 y then some y else none) = some m := h
  by_cases hy : ok164 y = true
  · rw [if_pos hy] at h0
    cases h0
    unfold ok164 at hy
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hy
    exact hy
  · rw [if_neg hy] at h0
    cases h0

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X) (n : ℕ) (ok : List Bool → Bool)

/-- `pLeafS` writes what the sibling's code of leaf queries over `pBody` writes. -/
theorem pLeafS_put (q : Compile.Batch.LeafIn (strung L)) :
    (pLeafS L n ok).put q = (TypedOracleCompiler.Run.pLeaf (L := strung L) n (pBody ok)).put q :=
  rfl

/-- And reads what it reads. -/
theorem pLeafS_parse (s : List Bool) :
    (pLeafS L n ok).parse s = (TypedOracleCompiler.Run.pLeaf (L := strung L) n (pBody ok)).parse s :=
  rfl

end TypedOracleCompiler.Strings
