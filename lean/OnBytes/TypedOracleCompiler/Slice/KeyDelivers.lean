-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/KeyDelivers.lean: the key's file in the shape of OnBytes/TypedOracleCompiler/Slice/Shapes.lean:
its part by the way "type, then run", and one theorem that has all twelve clauses of
`FileSpec.Delivers`: those that are had, proved; the rest as hypotheses under their names.

THIS IS WHAT FILLING THE SHAPE LOOKS LIKE; NOTHING IS DELIVERED: the hypotheses are met by nobody.
The like of OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean, over the key's frame as it lies
(OnBytes/TypedOracleCompiler/Slice/Plain3X.lean, Plain3XOff.lean, JudgeOff.lean, JudgeOffRun.lean).

EVERYTHING IS A FUNCTION OF LETTERS: the sizes of a table's record (T, v, eM, lg, s), what the
statements read of a decoded table (A); and, at each pair of tables, the stretches, the decision,
the number of blocks, the salt's length, the ways of writing, the reading, the implementation and
the roots (`KeyAt`). No size is written into a definition.

Main definitions.
 `SdK`, `XK`            the seeds of a table's record; an instance: the table's answers; its seeds.
 `KeyAt`                what the key's part is made of, at one pair of tables. With `KeyAt.W`,
                        `KeyAt.Z`, `KeyAt.ZT`, `KeyAt.pre`.
 `KeyAt.base`           the part but for its checker: the key's frame at the library's kit and wire,
                        the judge `judgeOff` at the record's own terms, one root.
 `keySpec`              THE KEY'S FILE: `FileSpec.ofTyping` (OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean) at
                        that part, a typing `typ`, `preSeed`, and n = 2.
Main theorem.
 `key_delivers`         `(keySpec ..).Delivers S₀ S₁ rd b`.

HAD, of the twelve clauses: `judge`, by `x3_judge_record_chalP`
(OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean); `preNoCoin`, `preQueries` at 2, `blind`, by `preSeed_noCoin`,
`preSeed_queries` (OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean) and `preSeed_blind`
(OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean); `noCoin`, `queries`, `named`, `fit`, by `chkT_noCoin`,
`chkT_queries`, `chkT_det`, `FileSpec.ofTyping_fit`, from what is asked of the typing and the page.

OWED, AS HYPOTHESES. FOR `judge`: hS, SOUNDNESS RECORD BY RECORD, with counts at most εs (hb); no
tree is deeper than 63 (hs); the wiring is lawful (hw); blocks enough (hK); 0 < s; the six
conditions of `collRaw_pr`; the bound of `collRaw_pr` is at most εs (hε). OF THE PAGE: `one`;
`reads`; `blocks` (an answer has at most Bk blocks); `clean` (no typed query of the judge's run has
a public string). OF THE NUMBERS: `flat`. OF THE TYPING: it tosses no coin; it asks at most tT
strings; `few`; `typNamed` (the root of what it returns is read off the files); `okT` (what it
returns has external openings that the reading keeps).

THE PRICE. The count is multiplied by 3; the checker's count of strings takes in the judge's typed
queries, Bk strings each.

Not claimed. NO TYPING, NO PAGE, NO STRETCHES, NO DECISION IS GIVEN. The implementation is a letter
at the interface of these stretches; that a written page fits it, at a key file's stretches and
answers that are lists of triples, is not shown in this library. That
the stretches' depth is the code's: at another depth the language holds of nothing
(`DecR.not_lgK_of_len`), the hypothesis on soundness can be met by no protocol that accepts, and the
part is empty. `keySpec`, `KeyAt.base`, `KeyAt.pre` and `key_delivers` are used by nothing: see
OnBytes/TypedOracleCompiler/Slice/KeyDeliversL.lean; `KeyAt`, `KeyAt.W`, `KeyAt.Z`, `KeyAt.ZT`, `SdK`, `XK` are.
Nothing on proof of work beside the counts. That the hypotheses can be met together. That the record
which a yes tests is that in the instance: `DecR.langK_of_lang_one`
(OnBytes/Slice/DecoderRecTyped.lean) and `x3_run_seed` (OnBytes/TypedOracleCompiler/Slice/SeedsBridgeRun.lean) are
for that, and are not used here. That the program's yes makes the typing succeed and the judge
accept. NO SOUNDNESS IS PROVED. What the heads of SeedsBridge.lean, ShapesTyping.lean and
Shapes.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedsBridgeRun
import OnBytes.TypedOracleCompiler.Slice.ShapesTyping

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP chalP)
open OnBytes.Slice (DecR decRec recZ seedBS seedOfDrawn GE NZ seedEntry Tab NoClash Raw
  lenB)
open OnBytes.Slice.Shapes (Files FileSpec chkT chkT_det chkT_noCoin chkT_queries)
open scoped ENNReal

variable (An : Type) (lg s : ℕ)

/-- The seeds of a table's record. -/
abbrev SdK : Type := Fin s → (Fin lg → GE) × NZ

/-- An instance of the key: the table's answers; its seeds. -/
abbrev XK : Type := An × SdK lg s

/-- What the key's part is made of, at one pair of tables: the three stretches of the key's
chains; the decision, as a function of an instance; the number of blocks; the stretches' ones; the
length of a salt; how a stored symbol is written into a string and read back; a reading; an
implementation; the roots, read off the files. d: the fixed value that a first query holds in the
place of seeds. ALL ARE LETTERS. The kit is the library's "challenges as hash blocks". -/
structure KeyAt (d : SdK lg s) where
  /-- the stretches -/
  G : Stretches
  /-- the decision -/
  dec : XK An lg s → PQ.View → PQ.View → PQ.View → Bool
  /-- the number of blocks of a challenge -/
  K : ℕ
  /-- the stretches' ones -/
  o : (atBlocks G).Ones
  /-- the length of a file's salt, in bytes -/
  salt : ℕ
  /-- a stored symbol as a string -/
  embE : PQ.SgX → List Bool
  /-- read back -/
  prjE : List Bool → Option PQ.SgX
  /-- the reading of the string under a root -/
  R : Reading (LXs (atBlocks G) dec d (seedEntry lg s)) embE
  /-- the implementation of the typed oracles by one oracle -/
  m : OracleCoding (typedOracleFamily 256 (K + 1) (LXs (atBlocks G) dec d (seedEntry lg s))) 256
  /-- the roots, read off the files -/
  rts : Files → List (Dig 256)

variable {An lg s} [DecidableEq (SdK lg s)] {d : SdK lg s} {X : Type} (T : _root_.Fmt.M1.Code)
  (v eM : ℕ) (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (A : (decRec T v eM lg s).Claims X)

/-- The wire, at these data. -/
abbrev KeyAt.W (x : KeyAt An lg s d) :=
  WXo (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o x.salt d (TS (atBlocks x.G) (seedEntry lg s))
    x.embE x.prjE (wTS (atBlocks x.G) x.K (chalP .two x.K) (seedEntry lg s))
    (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _)

/-- The protocol in three stretches with instances, as written, at these data. -/
abbrev KeyAt.Z (x : KeyAt An lg s d) :=
  ZXo (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o x.salt d (TS (atBlocks x.G) (seedEntry lg s))
    x.embE x.prjE (wTS (atBlocks x.G) x.K (chalP .two x.K) (seedEntry lg s))
    (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _)

/-- The seeds' protocol as written, at these data. -/
abbrev KeyAt.ZT (x : KeyAt An lg s d) :=
  testWritten (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o x.salt d
    (TS (atBlocks x.G) (seedEntry lg s)) x.embE x.prjE
    (wTS (atBlocks x.G) x.K (chalP .two x.K) (seedEntry lg s))
    (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _)

/-- The key's part but for its checker: interface, wiring, judge (`judgeOff` at the record's own
terms), error, implementation, roots, symbols. Its checker and the count of the checker's strings
are placeholders: `FileSpec.ofTyping` does not read them. -/
def KeyAt.base (x : KeyAt An lg s d) (εs : ℝ≥0∞) (sMT sFS : ℕ) : Part 256 Files PQ.SgX where
  I := Unit
  X := XK An lg s
  L := LXs (atBlocks x.G) x.dec d (seedEntry lg s)
  W := x.W
  Out := BatchOut x.Z
  J := judgeOff x.Z x.ZT [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
    (seedOfS (atBlocks x.G) (seedEntry lg s) (seedOfDrawn lg s)) sMT sFS x.R
    (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)
    (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)
  e := εs
  m := x.m
  chk := fun _ => OComp.pure none
  rts := x.rts
  tR := 0
  a := 1
  u := Equiv.refl _

/-- What is asked first, at these data. -/
def KeyAt.pre (x : KeyAt An lg s d) :=
  preSeed x.ZT [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _) x.Z

variable (Θ : Tab → Tab → KeyAt An lg s d) (εs : ℝ≥0∞) (sMT sFS : ℕ)

/-- THE KEY'S FILE, BY THE WAY "TYPE, THEN RUN": at all tables the part of `KeyAt.base` with the
checker "the typing `typ`, then the judge's run over the one oracle through the implementation".
What is asked first: the seeds' chain under the root: at most 2 queries. -/
def keySpec
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an A εs sMT sFS).Out))
    (tT Bk : ℕ) : FileSpec :=
  FileSpec.ofTyping (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an A εs sMT sFS) typ
    (fun T₀ T₁ => (Θ T₀ T₁).pre) 2 tT Bk

/-- WHAT IS DELIVERED FOR THE KEY'S FILE, AND WHAT IS STILL OWED. All twelve clauses of
`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean). HAD: `judge` (`x3_judge_record_chalP`), under
the hypotheses named below; `preNoCoin`, `preQueries`, `blind`; `noCoin`, `queries`, `named`, `fit`
from what is asked of the typing. OWED, as hypotheses under their names: see the file's head. -/
theorem key_delivers
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an A εs sMT sFS).Out))
    (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw PQ.SgX) (b : ℕ → ℝ≥0∞)
    -- the numbers of the record
    (hs0 : 0 < s) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs)
    -- the stretches, at all tables
    (hK : ∀ T₀ T₁, (seedBS lg s).b ≤ (Θ T₀ T₁).K)
    (hs : ∀ T₀ T₁, (atBlocks (Θ T₀ T₁).G).Shallow)
    (hw : ∀ T₀ T₁, (wq3X (atBlocks (Θ T₀ T₁).G) (Θ T₀ T₁).dec (Θ T₀ T₁).K
      (chalP .two (Θ T₀ T₁).K) (Θ T₀ T₁).o).OKG)
    -- soundness record by record
    (ε : ∀ T₀ T₁, Err (atBlocks (Θ T₀ T₁).G).sh)
    (hS : ∀ T₀ T₁ x, (Plain3 (atBlocks (Θ T₀ T₁).G) ((Θ T₀ T₁).dec x)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A x) (ε T₀ T₁))
    (hb : ∀ T₀ T₁, Err.Below (ε T₀ T₁) εs)
    -- the page
    (one : ∀ T₀ T₁, OneBlock (Θ T₀ T₁).m)
    (reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
      ((keySpec T v eM an A Θ εs sMT sFS typ tT Bk).part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm)
    (blocks : ∀ T₀ T₁ o, (Θ T₀ T₁).m.blocks o ≤ Bk)
    (clean : ∀ T₀ T₁ (F : Fam (typedOracleFamily 256 ((Θ T₀ T₁).base T v eM an A εs sMT sFS).W.K
        ((Θ T₀ T₁).base T v eM an A εs sMT sFS).L))
      (o : ((Θ T₀ T₁).base T v eM an A εs sMT sFS).Out),
      ∀ e ∈ ((((Θ T₀ T₁).base T v eM an A εs sMT sFS).J.run o).withTrace.det F).2,
        ∀ j, ((Θ T₀ T₁).base T v eM an A εs sMT sFS).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀)
    -- the numbers of the bound
    (flat : ∀ T₀ T₁ t,
      ((keySpec T v eM an A Θ εs sMT sFS typ tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ b t)
    -- the typing
    (typNoCoin : ∀ T₀ T₁ x, (typ T₀ T₁ x).NoCoin)
    (typQueries : ∀ T₀ T₁ x, (typ T₀ T₁ x).QueryBound tT)
    (few : ∀ T₀ T₁ x, ((Θ T₀ T₁).rts x).length ≤ 1)
    (typNamed : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an A εs sMT sFS).Out), (typ T₀ T₁ x).det g = some o →
      ∀ r ∈ ((Θ T₀ T₁).base T v eM an A εs sMT sFS).J.roots o, r ∈ (Θ T₀ T₁).rts x)
    (okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an A εs sMT sFS).Out), (typ T₀ T₁ x).det g = some o →
      ((Θ T₀ T₁).base T v eM an A εs sMT sFS).J.ok o) :
    (keySpec T v eM an A Θ εs sMT sFS typ tT Bk).Delivers S₀ S₁ rd b where
  judge := fun T₀ T₁ => x3_judge_record_chalP T v eM lg s (Θ T₀ T₁).G (Θ T₀ T₁).dec (Θ T₀ T₁).K
    (Θ T₀ T₁).o (Θ T₀ T₁).salt d (Θ T₀ T₁).embE (Θ T₀ T₁).prjE hs0 (hK T₀ T₁) an A ha hk he hJ h3 hl
    sMT sFS (Θ T₀ T₁).R (ε T₀ T₁) εs (hS T₀ T₁) (hb T₀ T₁) (hs T₀ T₁) (hw T₀ T₁) hε
  preNoCoin := fun T₀ T₁ o q => preSeed_noCoin (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).Z o q
  preQueries := fun T₀ T₁ o q => preSeed_queries (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).Z o q
  blind := fun T₀ T₁ F tr cm =>
    preSeed_blind (Θ T₀ T₁).Z (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).R F tr cm
  one := one
  reads := reads
  flat := flat
  noCoin := fun T₀ T₁ x => chkT_noCoin _ (typ T₀ T₁) (typNoCoin T₀ T₁) x
  queries := fun T₀ T₁ x => chkT_queries _ (typ T₀ T₁) tT Bk (typQueries T₀ T₁) (blocks T₀ T₁) x
  few := few
  named := fun T₀ T₁ g x o h => typNamed T₀ T₁ g x o (chkT_det _ (typ T₀ T₁) x g o h).1
  fit := fun T₀ T₁ g x o _ h =>
    FileSpec.ofTyping_fit (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an A εs sMT sFS) typ S₀ S₁ clean okT
      T₀ T₁ g x o h

end TypedOracleCompiler.Slice
