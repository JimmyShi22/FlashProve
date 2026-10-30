-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryReadsAt.lean: at an entry's part with the page as its implementation
(`EntryClean.atPage`), stored symbols written into bodies by the sibling's `bodyS`, and `back` the
total code of OnBytes/TypedOracleCompiler/Run/PageEBack.lean: the implementation spells vertices and stored leaves
as the one written reading reads them, and the part reads plainly: the two facts from which the
clause `reads` follows.

OnBytes/TypedOracleCompiler/Slice/ShapesReadsPage.lean draws the clause `reads` of a part made by the way "type,
then run" (`reads_ofTyping`) from three facts at all tables: `OneBlock`, `Spells`, `PlainRead`.
`OneBlock` is `EntryClean.atPage_one`. This file gives the other two at one pair of tables. The
sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `atRead`: `EntryClean.atPage` at B := `bodyS D.a n`, a file's salt of 8 n bits, and `back` :=
   `PageEBack.backE2` at the serialiser of stored symbols that every page uses;
 - `atRead_spells`: `Spells` of its implementation, at cfg, the description's depth D.a and salts of
   n bytes: by `spells_implG` from OnBytes/TypedOracleCompiler/Slice/EntryReads.lean's three equations;
 - `atRead_plain`: `PlainRead` of its part at D.a, under a hypothesis on the reading R, which is a
   letter: that it goes by leaves, keeps what the wire reads from a leaf's body, and builds the
   string in the wiring's way;
 - `rdW`: a reading that meets it: the sibling's `Reading.wide` at the part's wire;
   `atRead_plain_wide`: with it the part reads plainly, under no hypothesis.

Main definitions: `atRead`, `rdW`.
Main theorems: `atRead_spells`, `atRead_plain`, `atRead_plain_wide`.

Not claimed. `reads` itself at all tables: it wants the description's depth to be the sizes' depth,
n the sizes' salt length and cfg the digest off the first table, at all tables: whoever gives the
description owes these. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryReads
import OnBytes.TypedOracleCompiler.Slice.EntryClean
import OnBytes.TypedOracleCompiler.Slice.ShapesReadsPage

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.EntryReadsAt
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryClean TypedOracleCompiler.Slice.EntryReads
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD OwnE bodyS)
open OnBytes.Slice (seedEntry decRec GE)
open OnBytes.Slice.Shapes (Files Spells PlainRead spells_implG)
open _root_.Run.PQ (View SgX serW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open scoped ENNReal

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s} (D : XD) (n : ℕ)
  (E : OwnE (List Bool) D) (dec : XE (List T3) lg s → View → Bool)
  (R : Reading (Ls D d₁) (bodyS D.a n).embE) (rts : Files → List (Dig 256))
  (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray)
  (ss : Ser (Sd1 lg s × Sd1 lg s))

/-- The total code behind the escape, at the serialiser of stored symbols that every page uses. -/
abbrev bk : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)) :=
  PageEBack.backE2 D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) ss (bodyS D.a n)
    (Ser.prod Ser.natG (Ser.list serW))

/-- The data of an entry's part at the page, with stored symbols, salt and `back` fixed. n: the
bytes of a file's salt. -/
def atRead : EntryAt (List T3) lg s d₁ :=
  atPage D (bodyS D.a n) E dec R rts cfg hcfg pd rest (8 * n) (bk D n ss)

variable (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : List T3 → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) (εs : ℝ≥0∞)

/-- The implementation spells vertices and stored leaves as the one written reading reads them,
at cfg, the description's depth and salts of n bytes. -/
theorem atRead_spells :
    Spells ((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs).m
      (fun y => ((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs).W.embE
        (((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs).u.symm y))
      cfg D.a n :=
  spells_implG (pg D d₁ cfg hcfg pd rest n (bk D n ss)) (bodyS D.a n).embE cfg D.a n
    (realE_node D d₁ cfg hcfg pd rest n (bk D n ss))
    (realE_stored D d₁ cfg hcfg pd rest n (bk D n ss) D.a)
    (backE2_stored D d₁ n D.a ss)

/-- The part reads plainly at the description's depth, if its reading goes by leaves, keeps what
the wire reads from a leaf's body, and builds the string in the wiring's way. -/
theorem atRead_plain
    (hR : R.ByLeaves
      (keepAll ((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs).W)
      fun φ => ((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs).W.B.ext.build
        fun q => φ q.val) :
    PlainRead ((atRead D n E dec R rts cfg hcfg pd rest ss).base T v eM an εs) D.a where
  depth := rfl
  len := rfl
  fill := fun φ q => by
    show (φ q.val).getD (0, []) = ((φ q.val).map (Equiv.refl SgX)).getD (0, [])
    cases φ q.val <;> rfl
  byLeaves := hR
  back := (bodyS D.a n).get_e
  only := (bodyS D.a n).e_get

/-! ## A reading that meets the hypothesis -/

/-- The wire of an entry's part at these data. -/
abbrev wE : QueryLayout 256 (Ls D d₁) :=
  WXE D (bodyS D.a n) E (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))
    (wTSE D (seedEntry lg s)) (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)

/-- A reading: the sibling's wide one at that wire: at every place it keeps what the wire reads
from the leaf's body, whatever the salt. -/
def rdW : Reading (Ls D d₁) (bodyS D.a n).embE :=
  Reading.wide (W := wE (d₁ := d₁) D n E) (WireE.one_ok (2 ^ D.a) SgX (0, [])) (bodyS D.a n).get_e

/-- With that reading the part reads plainly, under no hypothesis. -/
theorem atRead_plain_wide :
    PlainRead ((atRead D n E dec (rdW (d₁ := d₁) D n E) rts cfg hcfg pd rest ss).base T v eM an
      εs) D.a :=
  atRead_plain D n E dec _ rts cfg hcfg pd rest ss T v eM an εs (Reading.wide_byLeaves _ _)

end TypedOracleCompiler.Slice.EntryReadsAt
