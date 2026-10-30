-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsStoredAt.lean: a stored symbol's own body as a string of bits.

A stored table's symbol is a position and a column. The sibling has a partial code of such symbols
(`pStored a salt`, OnBytes/TypedOracleCompiler/Run/Tag174.lean): the label under the stored leaves' number 174, the
column, the fill; written exactly where a test holds
(`storedOK`). `embX` makes a body of EVERY symbol, in the form of OnBytes/TypedOracleCompiler/StringsStored.lean:
that code's string where it writes one; else an escape of 16 zero bits and then the string of a
total code c, which is a parameter. `prjX` reads a body back.
 - `embX_stored`: where the sibling's test `storedOK` holds, the body is the sibling's `storedStr`:
   the bits of the format's label under 174 and of column and fill;
 - `ok2_rd2_embX`: there it passes `ok2`, and `rd2` reads from it the number 174 and the stored
   leaf's spelling;
 - `put_embX`: on a stored symbol's body the identity on the bodies that pass `ok2` writes what the
   stored symbols' code writes, AND NOTHING WHERE THAT CODE WRITES NOTHING: a body behind the escape
   fails `ok2` (`ok2_esc`);
 - `prjX_embX`: what is written is read back, for ALL symbols;
 - `leafOK2`: a test on body and salt together: with a stored symbol's body (one that begins with
   the 16 bits of 174 or with the escape) the typed salt's first 256 bits must be cfg; with any
   other body nothing is asked (`leafOK2_own`);
 - `storedIn`: the sibling's `StoredIn` at every page whose leaf code is `pBody ok2` and whose test
   is `leafOK2` at its own configuration digest;
 - `storedGet`: the sibling's `StoredGet`: `prjX` is a partial inverse of `embX`.

Main definitions: `esc16`, `embX`, `prjX`, `storedLike`, `leafOK2`.
Main theorems: `ok2_esc`, `prjX_embX`, `embX_stored`, `ok2_rd2_embX`, `put_embX`, `storedLike_embX`,
`storedLike_own`, `storedIn`, `storedGet`, `leafOK2_own`.

Not claimed. No page is made: `storedIn` is for a page that is given, with two of its fields as
said. The total code c is a parameter here; OnBytes/TypedOracleCompiler/StringsAt.lean gives one. `storedOK` IS
WIDER THAN THE FORMAT's OWN TEST (`Fmt.leafOK`, `Fmt.idxOK`): it takes an empty column, any length
of salt below 2 ^ 11 bytes, an index from 2 ^ 63 on; it asks neither that the position is below 2 ^
a nor any one width. `salt` is in bytes, and nothing ties it to a page's `saltBits`: `storedIn`
holds at every a, salt and c. One depth and one length: bodies at two depths can be one string. The
page writes more under 174 than `embX`'s range: any label under 174 with any bytes passes `ok2`:
OnBytes/TypedOracleCompiler/StringsAt.lean has the narrower test (`okA`). A leaf query on a body behind this file's
escape is written by the page behind its own escape, this file's 16 bits inside: harmless (by hand).
The fourth hypothesis of the sibling's `sameStored_impl` (the two pages' total codes write leaf
queries on stored symbols alike) is not touched. Nothing ties `embX` to the wire of
OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean, whose `embE` is a parameter of the same type; no reading is
given. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsBoth
import OnBytes.TypedOracleCompiler.StringsStored
import OnBytes.TypedOracleCompiler.Run.PageXJoin

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open Rom
open _root_.Run (t164 bytesToBits PCode)
open TypedOracleCompiler.Run (t174 pStored storedStr storedOK pStored_some pStored_put pStored_tag startIs
  StoredIn StoredGet PageC)

/-- The escape: 16 bits that are the first 16 of no label under 164 or 174. -/
def esc16 : List Bool := List.replicate 16 false

theorem esc16_ne : esc16 ≠ t164 ∧ esc16 ≠ t174 := by decide +kernel

/-- A string that begins with the escape has it as its first 16 bits. -/
theorem take_esc (r : List Bool) : (esc16 ++ r).take 16 = esc16 := List.take_left' rfl

/-- A body that passes `ok2` begins with the 16 bits of 164 or of 174. -/
theorem ok2_tag {b : List Bool} (h : ok2 b = true) : b.take 16 = t164 ∨ b.take 16 = t174 :=
  (pBody2_tag b b (if_pos h)).2

/-- So a body that begins with the escape fails `ok2`. -/
theorem ok2_esc (r : List Bool) : ok2 (esc16 ++ r) = false := by
  cases h : ok2 (esc16 ++ r) with
  | false => rfl
  | true =>
      rcases ok2_tag h with e | e
      · exact absurd ((take_esc r).symm.trans e) esc16_ne.1
      · exact absurd ((take_esc r).symm.trans e) esc16_ne.2

/- a: the stored table's depth; salt: the length of a file's salt, in bytes; c: a total code of all
symbols -/
variable (a salt : ℕ) (c : StrCode (ℕ × List UInt64))

/-- No string of the stored symbols' code begins with the escape. -/
theorem stored_no_esc (y : ℕ × List UInt64) (s : List Bool) (h : (pStored a salt).put y = some s) :
    ¬ esc16 <+: s := by
  rintro ⟨r, rfl⟩
  exact esc16_ne.2 ((take_esc r).symm.trans (pStored_tag a salt y _ h).2)

/-- A stored symbol (position, column) as a body: the stored symbols' code's string (a label
under 174, column, fill) where that code writes one; else the escape and then the total code's
string. -/
def embX : ℕ × List UInt64 → List Bool :=
  StringsStored.embE (pStored a salt) c esc16 (stored_no_esc a salt)

/-- A body read as a stored symbol. -/
def prjX : List Bool → Option (ℕ × List UInt64) :=
  StringsStored.prjE (pStored a salt) c esc16 (stored_no_esc a salt)

/-- What is written is read back, for all symbols. -/
theorem prjX_embX (y : ℕ × List UInt64) : prjX a salt c (embX a salt c y) = some y :=
  StringsStored.prjE_embE _ _ _ _ y

/-- Where `storedOK` holds, a symbol's body is `storedStr`. -/
theorem embX_stored (y : ℕ × List UInt64) (h : storedOK a salt y) :
    embX a salt c y = storedStr a salt y :=
  StringsStored.embE_fmt _ _ _ _ (pStored_some a salt y h)

/-- There the body passes `ok2`, and `rd2` reads from it the number 174 and the stored leaf's
spelling: the place with the tree's number 0, the column's width and the salt's words; 2 ^ a + the
position; the column's bytes and the fill. -/
theorem ok2_rd2_embX (y : ℕ × List UInt64) (h : storedOK a salt y) :
    ok2 (embX a salt c y) = true ∧
      rd2 (embX a salt c y) = (174, _root_.Fmt.leafPlace 0 y.2.length (salt / 8), 2 ^ a + y.1,
        _root_.Fmt.colBytes y.2 ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length salt)) := by
  have hp : _root_.Fmt.leafPlace 0 y.2.length (salt / 8) < 2 ^ 48 := by
    have := h.2.1
    omega
  rw [embX_stored a salt c y h]
  exact ⟨ok2_spell 174 _ _ _ (Or.inr rfl) hp h.2.2, rd2_spell 174 _ _ _ (by decide) hp h.2.2⟩

/-- On a stored symbol's body the identity on the bodies that pass `ok2` writes what the stored
symbols' code writes, and nothing where that code writes nothing. -/
theorem put_embX (y : ℕ × List UInt64) :
    (pBody ok2).put (embX a salt c y) = (pStored a salt).put y := by
  show (if ok2 (embX a salt c y) then some (embX a salt c y) else none) = _
  cases hp : (pStored a salt).put y with
  | some m =>
      have hk := (pStored_put a salt y m hp).1
      rw [if_pos (ok2_rd2_embX a salt c y hk).1, embX_stored a salt c y hk,
        (pStored_put a salt y m hp).2]
  | none =>
      have e : embX a salt c y = esc16 ++ c.put y := StringsStored.embE_esc _ _ _ _ hp
      rw [e, ok2_esc]
      rfl

/-- Whether a body looks like a stored symbol's: it begins with the 16 bits of 174, or with the
escape. Every `embX y` does; not only these. -/
def storedLike (b : List Bool) : Bool := decide (b.take 16 = t174) || decide (b.take 16 = esc16)

theorem storedLike_embX (y : ℕ × List UInt64) : storedLike (embX a salt c y) = true := by
  unfold storedLike
  rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  cases hp : (pStored a salt).put y with
  | some m =>
      have e : embX a salt c y = m := StringsStored.embE_fmt _ _ _ _ hp
      exact Or.inl (e ▸ (pStored_tag a salt y m hp).2)
  | none =>
      have e : embX a salt c y = esc16 ++ c.put y := StringsStored.embE_esc _ _ _ _ hp
      exact Or.inr (e ▸ take_esc _)

/-- A body that begins with the 16 bits of 164 is none of a stored symbol. -/
theorem storedLike_own {b : List Bool} (h : b.take 16 = t164) : storedLike b = false := by
  unfold storedLike
  rw [h, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  exact ⟨fun e => TypedOracleCompiler.Run.t174_differs.2.2.1 e.symm, fun e => esc16_ne.1 e.symm⟩

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X)

/-- The test on body and salt together, for a page's `leafOK`: with a body that looks like a
stored symbol's the sibling's `startIs` is asked (the bytes of the typed salt's first 256 bits are
cfg); with any other body nothing is asked. -/
def leafOK2 (cfg : ByteArray) (q : Compile.Batch.LeafIn (strung L)) : Bool :=
  if storedLike q.body then startIs cfg q else true

/-- The sibling's `StoredIn`: a page whose leaf code is `pBody ok2` and whose test is `leafOK2`
at its own configuration digest holds the stored symbols, spelled by the stored symbols' code, as
the bodies `embX`. -/
theorem storedIn {K : ℕ} {tg : _root_.Compile.Tag} (C : PageC (strung L) K tg)
    (hC : C.leafP = pBody ok2) (hO : C.leafOK = leafOK2 L C.cfg) :
    StoredIn C (pStored a salt) (embX a salt c) where
  put := fun y => by rw [hC]; exact put_embX a salt c y
  ok := fun y s => by
    rw [hO]
    exact if_pos (storedLike_embX a salt c y)

/-- The sibling's `StoredGet`: `prjX` is a partial inverse of `embX`. -/
theorem storedGet : StoredGet (L := strung L) (embX a salt c) (prjX a salt c) where
  get_e := prjX_embX a salt c
  e_get := fun b y h =>
    (((pStored a salt).orElse c esc16 (stored_no_esc a salt)).put_parse b y h).symm

/-- With a prover's own leaf's body (one that begins with the 16 bits of 164) the test asks nothing.
-/
theorem leafOK2_own (cfg : ByteArray) (q : Compile.Batch.LeafIn (strung L))
    (h : List.take 16 (q.body : List Bool) = t164) : leafOK2 L cfg q = true := by
  unfold leafOK2
  rw [storedLike_own h]
  rfl

end TypedOracleCompiler.Strings
