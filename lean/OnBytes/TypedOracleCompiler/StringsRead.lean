-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsRead.lean: a reader of a body that is a string, and a test on bodies under which
the page's condition on leaves holds by the test's own definition.

The sibling's `PageFit.of` (OnBytes/TypedOracleCompiler/Run/CodingAgree.lean) asks of a page's code of bodies and of
its spelling of a leaf (`D.leaf`): whatever the code writes for a body is the bits of the format's
label under the leaves' number 164, with the two numbers that `D.leaf` gives for that body, and of
the bytes that it gives.

`rd` reads a body: from its first 64 bits the number above the leaves' number in the label's first
word; from the next 64 the index; the rest as bytes. It computes. IT REFUSES NOTHING AND IS NOT ONE
TO ONE: it gives a value also on bodies that are too short, or no whole number of bytes, or under
another number. `okRd` is the test: `okWhole` (OnBytes/TypedOracleCompiler/StringsWhole.lean), and the body IS the
bits of the label and bytes that `rd` reads from it. `rdOk` is the reader behind the test: `rd` on
the bodies that pass, nothing on any other; it is the one to take as `D.leaf`. The identity on the
bodies that pass `okRd` meets that condition by the test itself, with `D.leaf := rdOk`
(`pBodyR_fit`), and still the first alternative of the law `leafTag` (`pBodyR_tag`); so, at salts of
whole bytes, the first clause of `PageFit` holds at every page with this leaf code (`pLeafR_put`, by
the sibling's `pLeaf_put`; `pageFit_leaf`).

What is left: that the reader reads a symbol's spelling from its body, and that the body passes.
`rd_spell`: from the bits of a label under 164 and of bytes `rd` reads these very numbers and bytes,
if both words are below 2 ^ 64. So, under three conditions (no tree deeper than 63; the test on the
trees' words; both words of every label below 2 ^ 64), a symbol's body passes `okRd` and `rdOk`
reads from it the spelling of its leaf in its own tree: in ONE list of rounds, with the sibling's
own spelling `leafSL` on the right (`embTail_okRd`, `rdOk_embTail`); and at the protocol in three
stretches, with `Stretches.leafS` on the right (`embS_okRd`, `rd_embS`, `rdOk_embS`).
OnBytes/TypedOracleCompiler/StringsBounds.lean has all of these from conditions on the trees and the salt alone:
those are the forms to use.

Main definitions: `rd`, `spell`, `okRd`, `rdOk`, `InWordsL`, `Stretches.InWords`.
Main theorems: `rd_spell`, `pBodyR_fit`, `pBodyR_tag`, `pLeafR_put`, `pageFit_leaf`, `okRd_of_fit`;
`leafT_eq`, `leafSL_eq` (OnBytes/TypedOracleCompiler/StringsList.lean's spellings of a leaf in a round and in a list
of rounds are the sibling's own); `embTail_okRd`, `rdOk_embTail`; `rd_embS`, `embS_okRd`,
`rdOk_embS`.

Not claimed.
 - No page is made. Of `PageFit` the first clause alone is shown; its other three and a page's other
   fields are given by nobody here.
 - That `rdOk_embTail` is the hypothesis on bodies of the sibling's `forests_ind` is by eye: this
   file does not import that file.
 - `Stretches.leafS` has no counterpart in the sibling: `leafSL_eq` ties its third stretch alone.
 - By hand, not proved: the second clause of `okRd` follows from the first.
 - `okRd` passes every label under 164 with any bytes behind it, also outside the domain of the
   format's hash.
 - ON STORED LEAVES: a body that passes `okRd` has the number 164 (OnBytes/TypedOracleCompiler/StringsAt.lean:
   `ok2_of_okRd`), so a body under 174 is refused by `okRd` and by `rdOk`. By hand, no Lean
   statement: `rd` itself reads from it the two numbers and the bytes that it reads from the body
   under 164. A test that is not in this library tries this at one made-up body.
 - This file's code of bodies writes under 164 alone. The sibling's verifier asks stored leaves
   (174) at the same oracle, and its page takes both numbers:
   OnBytes/TypedOracleCompiler/StringsBoth.lean has one code of bodies for both. With THIS file's code as a page's
   leaf code, where `embE` writes the format's string under 174, the sibling's test `fitsC` is false
   at the leaf query of an external opening, and its `run_agree` says nothing of a run that reads
   one (by hand).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsWhole
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import OnBytes.TypedOracleCompiler.Run.CodingPut

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open _root_.Run (t164 bytesToBits bitsToBytes length_bytesToBits bitsToBytes_bytesToBits
  bytesToBits_append length_u64n)

/-- The bits of the label under 164 with two numbers, and of bytes. -/
def spell (z : ℕ × ℕ × ByteArray) : List Bool :=
  bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2

/-- A body read: the number above the leaves' number in the first word; the second word; the rest as
bytes. -/
def rd (b : List Bool) : Option (ℕ × ℕ × ByteArray) :=
  some (((_root_.Fmt.wordAt (bitsToBytes (b.take 64)) 0).toNat - 164) / 65536,
    (_root_.Fmt.wordAt (bitsToBytes ((b.drop 64).take 64)) 0).toNat,
    bitsToBytes (b.drop 128))

/-- From the bits of a label under 164 and of bytes `rd` reads these numbers and bytes, if both
words are below 2 ^ 64. -/
theorem rd_spell (t i : ℕ) (z : ByteArray) (ht : 164 + 65536 * t < 2 ^ 64) (hi : i < 2 ^ 64) :
    rd (spell (t, i, z)) = some (t, i, z) := by
  have e : spell (t, i, z) =
      bytesToBits (_root_.Fmt.u64n (164 + 65536 * t)) ++
        (bytesToBits (_root_.Fmt.u64n i) ++ bytesToBits z) := by
    unfold spell _root_.Fmt.label
    rw [bytesToBits_append, List.append_assoc]
  have h1 : (spell (t, i, z)).take 64 = bytesToBits (_root_.Fmt.u64n (164 + 65536 * t)) := by
    rw [e]
    exact List.take_left' (length_u64n _)
  have h2 : (spell (t, i, z)).drop 64 = bytesToBits (_root_.Fmt.u64n i) ++ bytesToBits z := by
    rw [e]
    exact List.drop_left' (length_u64n _)
  have h3 : ((spell (t, i, z)).drop 64).take 64 = bytesToBits (_root_.Fmt.u64n i) := by
    rw [h2]
    exact List.take_left' (length_u64n _)
  have h4 : (spell (t, i, z)).drop 128 = bytesToBits z := by
    have : (spell (t, i, z)).drop 128 = ((spell (t, i, z)).drop 64).drop 64 := by
      rw [List.drop_drop]
    rw [this, h2]
    exact List.drop_left' (length_u64n _)
  unfold rd
  rw [h1, h3, h4, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits,
    _root_.Fmt.wordAt_u64n _ ht, _root_.Fmt.wordAt_u64n _ hi, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel_left _ (by decide : 0 < 65536)]

/-- The test: `okWhole`, and the body is the bits of what `rd` reads from it. -/
def okRd (b : List Bool) : Bool :=
  okWhole b && match rd b with
    | some z => decide (b = spell z)
    | none => false

/-- The reader behind the test: what `rd` reads from a body that passes `okRd`; nothing from any
other. This is the one to take as a page's spelling of a leaf: `rd` itself refuses nothing. -/
def rdOk (b : List Bool) : Option (ℕ × ℕ × ByteArray) := if okRd b then rd b else none

theorem rdOk_of {b : List Bool} (h : okRd b = true) : rdOk b = rd b := if_pos h

/-- The identity on the bodies that pass `okRd` has the page's fit by the test itself, with
`rdOk` as the page's spelling of a leaf. -/
theorem pBodyR_fit (y m : List Bool) (h : (pBody okRd).put y = some m) :
    ∃ z, rdOk y = some z ∧
      m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2 := by
  have h0 : (if okRd y then some y else none) = some m := h
  by_cases hy : okRd y = true
  · rw [if_pos hy] at h0
    cases h0
    rw [rdOk_of hy]
    unfold okRd at hy
    rw [Bool.and_eq_true] at hy
    cases hr : rd y with
    | none => rw [hr] at hy; exact absurd hy.2 Bool.false_ne_true
    | some z =>
        rw [hr] at hy
        exact ⟨z, rfl, of_decide_eq_true hy.2⟩
  · rw [if_neg hy] at h0
    cases h0

/-- And the law `leafTag` of the sibling's page. -/
theorem pBodyR_tag (y m : List Bool) (h : (pBody okRd).put y = some m) :
    16 ≤ m.length ∧ m.take 16 = t164 := by
  have h0 : (if okRd y then some y else none) = some m := h
  by_cases hy : okRd y = true
  · rw [if_pos hy] at h0
    cases h0
    unfold okRd at hy
    rw [Bool.and_eq_true] at hy
    exact pBodyW_tag y y (if_pos hy.1)
  · rw [if_neg hy] at h0
    cases h0

/-- The bits of a label under 164 and of bytes pass `okRd` if they pass `ok164` and both words are
below 2 ^ 64. -/
theorem okRd_of_fit {b : List Bool} (t i : ℕ) (z : ByteArray) (hb : b = spell (t, i, z))
    (h : ok164 b = true) (ht : 164 + 65536 * t < 2 ^ 64) (hi : i < 2 ^ 64) : okRd b = true := by
  unfold okRd
  rw [okWhole_of_fit 164 t i z hb h, Bool.true_and, hb, rd_spell t i z ht hi]
  exact decide_eq_true rfl

/-- What the first clause of the sibling's `PageFit` comes to behind the page's test, at any
interface with bodies that are strings, for the leaf code `pBody okRd`, salts of whole bytes, and
any spellings whose spelling of a leaf is `rdOk`: what the sibling's `pLeaf` writes is the bits of a
call's string. By the sibling's `pLeaf_put`, whose hypothesis `fit` is `pBodyR_fit`. -/
theorem pLeafR_put {I X : Type} (L : _root_.Iop.BatchProtocol I X) (tg : _root_.Compile.Tag)
    (D : TypedOracleCompiler.Run.PageD (strung L) tg) (hD : D.leaf = rdOk) (n k : ℕ) (hn : n = 8 * k)
    (q : Compile.Batch.LeafIn (strung L)) (s : List Bool)
    (h : (TypedOracleCompiler.Run.pLeaf (L := strung L) n (pBody okRd)).put q = some s) :
    ∃ c, TypedOracleCompiler.Run.leafCall D q = some c ∧ s = bytesToBits (_root_.Run.strOf c) :=
  TypedOracleCompiler.Run.pLeaf_put D n k hn (pBody okRd) (hD ▸ pBodyR_fit) q s h

/-- The first clause of the sibling's `PageFit`, at every page whose leaf code is `pBody okRd`
and whose salts are whole bytes, and any spellings whose spelling of a leaf is `rdOk`; whatever the
page's test. -/
theorem pageFit_leaf {I X : Type} (L : _root_.Iop.BatchProtocol I X) {K : ℕ} {tg : _root_.Compile.Tag}
    (C : TypedOracleCompiler.Run.PageC (strung L) K tg) (D : TypedOracleCompiler.Run.PageD (strung L) tg)
    (hC : C.leafP = pBody okRd) (hD : D.leaf = rdOk) (k : ℕ) (hk : C.saltBits = 8 * k)
    (q : Compile.Batch.LeafIn (strung L)) (s : List Bool)
    (h : (TypedOracleCompiler.Run.pLeafC C).put q = some s) :
    ∃ c, TypedOracleCompiler.Run.leafCall D q = some c ∧ s = bytesToBits (_root_.Run.strOf c) := by
  have h1 := (TypedOracleCompiler.Run.pLeafC_put C q s h).2
  rw [hC] at h1
  exact pLeafR_put L tg D hD C.saltBits k hk q s h1

end TypedOracleCompiler.Strings

namespace TypedOracleCompiler.Slice
open _root_.Iop (OPos OSym)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings

variable (salt : ℕ)

/-- OnBytes/TypedOracleCompiler/StringsList.lean's spelling of a leaf in a round is the sibling's own. -/
theorem leafT_eq : ∀ (ts : List _root_.Fmt.Shape) (p : PQ.PosT ts) (a : PQ.SymT ts p),
    StringsList.leafT salt ts p a = PQ.leafT salt ts p a
  | _ :: _, .inl _, _ => rfl
  | _ :: ts, .inr p, a => leafT_eq ts p a

/-- And in a list of rounds. -/
theorem leafSL_eq (C : PQ.CK) : ∀ (ds : List PQ.RD) (y : _root_.Compile.SymAny (PQ.uL C ds)),
    StringsList.leafSL salt C ds y = PQ.leafSL C salt ds y
  | [], y => y.1.elim
  | d :: _, ⟨.inl p, a⟩ => leafT_eq salt d.trees p a
  | _ :: ds, ⟨.inr q, a⟩ => leafSL_eq C ds ⟨q, a⟩

/-! ## One list of rounds -/

section OneList
variable (C : PQ.CK) (ds : List PQ.RD)

/-- Both words of every leaf's label are below 2 ^ 64, in one list of rounds; in the sibling's own
spelling of a leaf. -/
def InWordsL : Prop :=
  ∀ y : _root_.Compile.SymAny (PQ.uL C ds),
    164 + 65536 * (PQ.leafSL C salt ds y).1 < 2 ^ 64 ∧ (PQ.leafSL C salt ds y).2.1 < 2 ^ 64

/-- A symbol's body passes `okRd`, in one list of rounds, if no tree is deeper than 63, every tree's
word begins with the 16 bits of the leaves' number, and both words of every label are below 2 ^ 64.
-/
theorem embTail_okRd (h : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (hk : tagsL salt ds = true) (hw : InWordsL salt C ds) (p : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) p) : okRd (embTail salt C ds p a) = true := by
  have hw' := hw ⟨p, a⟩
  rw [← leafSL_eq salt C ds ⟨p, a⟩] at hw'
  exact okRd_of_fit _ _ _ (fits_tail salt C ds h p a) (passes_tail salt C ds h hk p a) hw'.1 hw'.2

/-- From a symbol's body the reader behind the test reads the sibling's own spelling of its
leaf, in one list of rounds, under the same three conditions. -/
theorem rdOk_embTail (h : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (hk : tagsL salt ds = true) (hw : InWordsL salt C ds) (p : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) p) :
    rdOk (embTail salt C ds p a) = some (PQ.leafSL C salt ds ⟨p, a⟩) := by
  have hw' := hw ⟨p, a⟩
  rw [← leafSL_eq salt C ds ⟨p, a⟩] at hw'
  rw [rdOk_of (embTail_okRd salt C ds h hk hw p a), ← leafSL_eq salt C ds ⟨p, a⟩,
    fits_tail salt C ds h p a]
  exact rd_spell _ _ _ hw'.1 hw'.2

end OneList

/-! ## Three stretches -/

namespace Stretches
variable (G : Stretches)

/-- Both words of every leaf's label are below 2 ^ 64. -/
def InWords : Prop :=
  ∀ (p : OPos G.sh) (a : OSym G.sh p),
    164 + 65536 * (G.leafS salt p a).1 < 2 ^ 64 ∧ (G.leafS salt p a).2.1 < 2 ^ 64

/-- From a symbol's body `rd` reads the spelling of its leaf in its own tree, if no tree is
deeper than 63 and both words of every label are below 2 ^ 64. -/
theorem rd_embS (h : G.Shallow) (hw : G.InWords salt) (p : OPos G.sh) (a : OSym G.sh p) :
    rd (G.embS salt p a) = some (G.leafS salt p a) := by
  rw [G.embS_fit salt h p a]
  exact rd_spell _ _ _ (hw p a).1 (hw p a).2

/-- A symbol's body passes `okRd`, under these two conditions and the test on the trees' words
(`Tags`). -/
theorem embS_okRd (h : G.Shallow) (hk : G.Tags salt) (hw : G.InWords salt) (p : OPos G.sh)
    (a : OSym G.sh p) : okRd (G.embS salt p a) = true :=
  okRd_of_fit _ _ _ (G.embS_fit salt h p a) (G.embS_ok164 salt h hk p a) (hw p a).1 (hw p a).2

/-- And so the reader behind the test reads that spelling, under the three conditions. -/
theorem rdOk_embS (h : G.Shallow) (hk : G.Tags salt) (hw : G.InWords salt) (p : OPos G.sh)
    (a : OSym G.sh p) : rdOk (G.embS salt p a) = some (G.leafS salt p a) := by
  rw [rdOk_of (G.embS_okRd salt h hk hw p a)]
  exact G.rd_embS salt h hw p a

end Stretches

end TypedOracleCompiler.Slice
