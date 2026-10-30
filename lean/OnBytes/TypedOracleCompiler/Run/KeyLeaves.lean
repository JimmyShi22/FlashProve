-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean: the code of leaf queries for the page of a key's judge: bodies that
are strings, under the leaves' number 164 or the stored leaves' number 174; and the page with it.

OnBytes/TypedOracleCompiler/Run/KeyPage.lean takes any partial code of leaf queries whose strings have the tag of
164 or 174 and begin with the byte 0 (`PageG.Leaves`). At an interface whose bodies are strings
OnBytes/TypedOracleCompiler/StringsBoth.lean has the code of bodies (`pBody ok2`: the identity on the bodies that
are a label under one of the two numbers and bytes), and OnBytes/TypedOracleCompiler/StringsStoredAt.lean a test on
body and salt together (`leafOK2 cfg`: with a body that looks like a stored symbol's, the typed
salt's first 256 bits are cfg's). This file puts them into the form that the page takes. The sibling
is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `leafCode L n cfg`: the sibling's code of leaf queries over `pBody ok2`, at a file's salt of n
   bits, under the test `leafOK2 cfg`;
 - `leafCode_facts`: its strings have the tag of 164 or of 174 and begin with the byte 0;
 - `leavesAt L n cfg : PageG.Leaves (strung L)`;
 - `leafCode_str`: for a salt of whole bytes: what it writes is the bits of the format's string of
   the call that `call2` gives.

Main definitions: `leafCode`, `leavesAt`.
Main theorems: `leafCode_facts`, `leafCode_str`.

Not claimed. That a prover's symbol's body, or a stored symbol's, passes the tests:
OnBytes/TypedOracleCompiler/StringsBoth.lean (`Stretches.ok2_rd2_embS`), StringsStoredAt.lean and StringsAt.lean say
it, under their conditions. `ok2` passes every label under the two numbers with any bytes behind it.
What the heads of these files do not claim. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is
the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.KeyPage
import OnBytes.TypedOracleCompiler.StringsStoredAt

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.KeyLeaves
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Strings
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X) (n : ℕ) (cfg : ByteArray)

/-- The code of leaf queries: the sibling's, over the identity on the bodies that pass `ok2`, at
a file's salt of n bits, under the test `leafOK2 cfg`. -/
def leafCode : PCode (LeafIn (strung L)) :=
  (pLeaf (L := strung L) n (pBody ok2)).sub (leafOK2 L cfg)

/-- Whatever it writes, the code without the test writes. -/
theorem leafCode_put (q : LeafIn (strung L)) (s : List Bool)
    (h : (leafCode L n cfg).put q = some s) :
    (pLeaf (L := strung L) n (pBody ok2)).put q = some s := by
  have h0 : (if leafOK2 L cfg q = true then (pLeaf (L := strung L) n (pBody ok2)).put q
    else none) = some s := h
  by_cases hk : leafOK2 L cfg q = true
  · rw [if_pos hk] at h0
    exact h0
  · rw [if_neg hk] at h0
    cases h0

/-- Its strings have the tag of 164 or of 174 and begin with the byte 0. -/
theorem leafCode_facts (q : LeafIn (strung L)) (s : List Bool)
    (h : (leafCode L n cfg).put q = some s) :
    (tag16 s = t164 ∨ tag16 s = t174) ∧ ∀ b : UInt8, b ≠ 0 → ¬ bitsOfByte b <+: s := by
  have h0 : (pSalted pre33 n (pBody ok2)).put (q.body, q.salt) = some s :=
    leafCode_put L n cfg q s h
  obtain ⟨st, m, r, hst, hm, rfl⟩ := pSalted_shape pre33 n (pBody ok2) (q.body, q.salt) s h0
  exact ⟨(pBody2_tag _ m hm).2.imp (tag16_pre33 st m r hst (pBody2_tag _ m hm).1).trans
      (tag16_pre33 st m r hst (pBody2_tag _ m hm).1).trans,
    fun b hb => pre33_not_prefix b hb _⟩

/-- The leaves' code in the form that the page takes. -/
def leavesAt : PageG.Leaves (strung L) := ⟨leafCode L n cfg, leafCode_facts L n cfg⟩

/-- What it writes is the format's string of the call that `call2` gives, for a salt of whole
bytes. -/
theorem leafCode_str (k : ℕ) (hn : n = 8 * k) (q : LeafIn (strung L)) (s : List Bool)
    (h : (leafCode L n cfg).put q = some s) :
    ∃ c, call2 L q = some c ∧ s = bytesToBits (strOf c) :=
  pLeaf2_put L n k hn q s (leafCode_put L n cfg q s h)

end TypedOracleCompiler.Run.KeyLeaves
