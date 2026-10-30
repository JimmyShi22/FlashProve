-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean: the entry's file in the shape of
OnBytes/TypedOracleCompiler/Slice/Shapes.lean: its part by the way "type, then run", and one theorem that has all
twelve clauses of `FileSpec.Delivers`: those that are had, proved; the rest as hypotheses under
their names.

THIS IS WHAT FILLING THE SHAPE LOOKS LIKE; NOTHING IS DELIVERED: the hypotheses are met by nobody.

EVERYTHING IS A FUNCTION OF LETTERS: the sizes of a table's record (T, v, eM, lg, s); and, at each
pair of tables, the description, the bodies, the decision, the reading, the implementation and the
roots (`EntryAt`). No size is written into a definition.

Main definitions.
 `Sd1`, `XE`            the seeds of one table's record; an instance: both tables' answers; both
                        tables' seeds.
 `EntryAt`              what the entry's part is made of, at one pair of tables. With `EntryAt.Z`,
                        `EntryAt.ZT`, `EntryAt.pre`.
 `EntryAt.base`         the part but for its checker: the frame of OnBytes/TypedOracleCompiler/Slice/EntryX.lean,
                        the judge `judgeEL` at the record's own terms, two roots.
 `entrySpec`            THE ENTRY'S FILE: `FileSpec.ofTyping` (OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean)
                        at that part, a typing `typ`, `preE`, and n = 4.
Main theorem.
 `entry_delivers`       `(entrySpec ..).Delivers S₀ S₁ rd b`.

HAD, of the twelve clauses: `judge`, by `entry_judge_record` (OnBytes/TypedOracleCompiler/Slice/EntryXJudge.lean);
`preNoCoin`, `preQueries` at 4, `blind`, by `preE_noCoin`, `preE_queries` and `preE_blind`
(OnBytes/TypedOracleCompiler/Slice/JudgeE.lean); `noCoin`, `queries`, `named`, `fit`, by `chkT_noCoin`,
`chkT_queries`, `chkT_det`, `FileSpec.ofTyping_fit`, from what is asked of the typing and the page.

OWED, AS HYPOTHESES. FOR `judge`: hS, SOUNDNESS RECORD BY RECORD, with counts at most εs (hb); the
depth of the description's stored tables is the code's (hD: elsewhere the language holds of
everything); the description's field is the second (hf), it has blocks enough (hK), the link's
wiring is lawful (hw); 0 < s; the six conditions of `collRaw_pr`; the bound of `collRaw_pr` is at
most εs (hε). OF THE PAGE: `one`; `reads`; `blocks` (an answer has at most Bk blocks); `clean` (no
typed query of the judge's run has a public string). OF THE NUMBERS: `flat`. OF THE TYPING: it
tosses no coin; it asks at most tT strings; `few`; `typNamed` (the roots of what it returns are read
off the files); `okT` (what it returns has two roots, and external openings that the reading keeps).

THE PRICE. The count is multiplied by 5; the checker's count of strings takes in the judge's typed
queries, Bk strings each.

Not claimed. NO TYPING, NO PAGE, NO DESCRIPTION, NO DECISION IS GIVEN. That the hypotheses can be
met together. That the records which a yes tests are those in the instance: `langE_of_judgeE` and
`entry_run_seeds` (OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean) are for that, and are not used here. That the
program's yes makes the typing succeed and the judge accept. Nothing on proof of work beside the
counts. NO SOUNDNESS IS PROVED. What the heads of EntryXJudge.lean, ShapesTyping.lean and
Shapes.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryXRun
import OnBytes.TypedOracleCompiler.Slice.ShapesTyping

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open _root_.Run.PQ (View SgX)
open OnBytes.Slice (DecR decRec recZ seedBS seedOfDrawn GE NZ seedEntry Tab NoClash Raw
  lenB)
open OnBytes.Slice.Shapes (Files FileSpec chkT chkT_det chkT_noCoin chkT_queries)
open scoped ENNReal

variable (An : Type) (lg s : ℕ)

/-- The seeds of one table's record. -/
abbrev Sd1 : Type := Fin s → (Fin lg → GE) × NZ

/-- An instance of the entry: both tables' answers; both tables' seeds. -/
abbrev XE : Type := (An × An) × (Sd1 lg s × Sd1 lg s)

/-- What the entry's part is made of, at one pair of tables: a description; the type of leaves'
bodies, with how stored symbols and the chain's own symbols lie among them; the decision, as a
function of an instance; a reading; an implementation; the roots, read off the files. d₁: the fixed
value that a first query holds in the place of seeds. ALL ARE LETTERS. -/
structure EntryAt (d₁ : Sd1 lg s) where
  /-- the description of the entry's chain -/
  D : XD
  /-- the leaves' bodies -/
  Bd : Type
  /-- stored symbols among them -/
  B : BodyD Bd
  /-- the chain's own symbols among them -/
  E : OwnE Bd D
  /-- the decision -/
  dec : XE An lg s → View → Bool
  /-- the reading of the string under a root -/
  R : Reading (LXEs (An := An) (Bd := Bd) lg s D d₁) B.embE
  /-- the implementation of the typed oracles by one oracle -/
  m : OracleCoding (typedOracleFamily 256 (D.K + 1) (LXEs (An := An) (Bd := Bd) lg s D d₁)) 256
  /-- the roots, read off the files -/
  rts : Files → List (Dig 256)

variable {An lg s} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s} (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)

/-- The written link with instances, at these data. -/
abbrev EntryAt.Z (x : EntryAt An lg s d₁) :=
  ZXE x.D x.dec x.B x.E (earlyTwo d₁) (TSE x.D (seedEntry lg s)) (wTSE x.D (seedEntry lg s))
    (embST x.D.C (seedEntry lg s) _) (prjST x.D.C (seedEntry lg s) _)

/-- The seeds' protocol as written, at these data. -/
abbrev EntryAt.ZT (x : EntryAt An lg s d₁) :=
  testXE x.D x.B x.E (earlyTwo (A := An × An) d₁) (TSE x.D (seedEntry lg s))
    (wTSE x.D (seedEntry lg s)) (embST x.D.C (seedEntry lg s) _) (prjST x.D.C (seedEntry lg s) _)

/-- The entry's part but for its checker: interface, wiring, judge (`judgeEL` at the record's
own terms), error, implementation, roots, symbols. Its checker and the count of the checker's
strings are placeholders: `FileSpec.ofTyping` does not read them. -/
def EntryAt.base (x : EntryAt An lg s d₁) (εs : ℝ≥0∞) : Part 256 Files SgX where
  I := Unit
  X := XE An lg s
  L := LXEs (An := An) (Bd := x.Bd) lg s x.D d₁
  W := WXE x.D x.B x.E (earlyTwo d₁) (TSE x.D (seedEntry lg s)) (wTSE x.D (seedEntry lg s))
    (embST x.D.C (seedEntry lg s) _) (prjST x.D.C (seedEntry lg s) _)
  Out := OutE x.Z
  J := judgeEL x.Z x.ZT [] default [] (plainsT x.D.C (dSeed (seedEntry lg s)) _)
    (seedOfE x.D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) x.R
    (lgEX T v eM lg s x.D an) (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)
  e := εs
  m := x.m
  chk := fun _ => OComp.pure none
  rts := x.rts
  tR := 0
  a := 2
  u := Equiv.refl _

/-- What is asked first, at these data. -/
def EntryAt.pre (x : EntryAt An lg s d₁) :=
  preE x.ZT [] default [] (plainsT x.D.C (dSeed (seedEntry lg s)) _) x.Z

variable (Θ : Tab → Tab → EntryAt An lg s d₁) (εs : ℝ≥0∞)

/-- THE ENTRY'S FILE, BY THE WAY "TYPE, THEN RUN": at all tables the part of `EntryAt.base` with
the checker "the typing `typ`, then the judge's run over the one oracle through the implementation".
What is asked first: the seeds' chain once under each root: at most 4 queries. -/
def entrySpec
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
    (tT Bk : ℕ) : FileSpec :=
  FileSpec.ofTyping (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).pre) 4 tT Bk

/-- WHAT IS DELIVERED FOR THE ENTRY'S FILE, AND WHAT IS STILL OWED. All twelve clauses of
`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean). HAD: `judge` (`entry_judge_record`), under the
hypotheses named below; `preNoCoin`, `preQueries`, `blind`; `noCoin`, `queries`, `named`, `fit` from
what is asked of the typing. OWED, as hypotheses under their names: see the file's head. -/
theorem entry_delivers
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
    (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞)
    -- the numbers of the record
    (hs0 : 0 < s) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs)
    -- the description, at all tables
    (hD : ∀ T₀ T₁, (Θ T₀ T₁).D.a = T.a)
    (hf : ∀ T₀ T₁, (Θ T₀ T₁).D.base.plan.field = .two)
    (hK : ∀ T₀ T₁, (seedBS lg s).b ≤ (Θ T₀ T₁).D.K)
    (hw : ∀ T₀ T₁, (wq0 (Θ T₀ T₁).D fun _ => true).OKG)
    -- soundness record by record
    (ε : ∀ T₀ T₁, Err (Link0 (Θ T₀ T₁).D fun _ => true).shape)
    (hS : ∀ T₀ T₁ x, (Link0 (Θ T₀ T₁).D ((Θ T₀ T₁).dec x)).Sound
      (fun _ => lgEX T v eM lg s (Θ T₀ T₁).D an x) (ε T₀ T₁))
    (hb : ∀ T₀ T₁, Err.Below (ε T₀ T₁) εs)
    -- the page
    (one : ∀ T₀ T₁, OneBlock (Θ T₀ T₁).m)
    (reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
      ((entrySpec T v eM an Θ εs typ tT Bk).part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm)
    (blocks : ∀ T₀ T₁ o, (Θ T₀ T₁).m.blocks o ≤ Bk)
    (clean : ∀ T₀ T₁ (F : Fam (typedOracleFamily 256 ((Θ T₀ T₁).base T v eM an εs).W.K
        ((Θ T₀ T₁).base T v eM an εs).L)) (o : ((Θ T₀ T₁).base T v eM an εs).Out),
      ∀ e ∈ ((((Θ T₀ T₁).base T v eM an εs).J.run o).withTrace.det F).2,
        ∀ j, ((Θ T₀ T₁).base T v eM an εs).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀)
    -- the numbers of the bound
    (flat : ∀ T₀ T₁ t, ((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ b t)
    -- the typing
    (typNoCoin : ∀ T₀ T₁ x, (typ T₀ T₁ x).NoCoin)
    (typQueries : ∀ T₀ T₁ x, (typ T₀ T₁ x).QueryBound tT)
    (few : ∀ T₀ T₁ x, ((Θ T₀ T₁).rts x).length ≤ 2)
    (typNamed : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an εs).Out), (typ T₀ T₁ x).det g = some o →
      ∀ r ∈ ((Θ T₀ T₁).base T v eM an εs).J.roots o, r ∈ (Θ T₀ T₁).rts x)
    (okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an εs).Out), (typ T₀ T₁ x).det g = some o →
      ((Θ T₀ T₁).base T v eM an εs).J.ok o) :
    (entrySpec T v eM an Θ εs typ tT Bk).Delivers S₀ S₁ rd b where
  judge := fun T₀ T₁ => entry_judge_record T v eM lg s (Θ T₀ T₁).D (Θ T₀ T₁).dec (Θ T₀ T₁).B
    (Θ T₀ T₁).E d₁ (hD T₀ T₁) (hf T₀ T₁) hs0 (hK T₀ T₁) an ha hk he hJ h3 hl (Θ T₀ T₁).R
    (ε T₀ T₁) εs
    (hS T₀ T₁) (hb T₀ T₁) (hw T₀ T₁) hε
  preNoCoin := fun T₀ T₁ o q => preE_noCoin (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).Z o q
  preQueries := fun T₀ T₁ o q => preE_queries (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).Z o q
  blind := fun T₀ T₁ F tr cm =>
    preE_blind (Θ T₀ T₁).Z (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).R F tr cm
  one := one
  reads := reads
  flat := flat
  noCoin := fun T₀ T₁ x => chkT_noCoin _ (typ T₀ T₁) (typNoCoin T₀ T₁) x
  queries := fun T₀ T₁ x => chkT_queries _ (typ T₀ T₁) tT Bk (typQueries T₀ T₁) (blocks T₀ T₁) x
  few := few
  named := fun T₀ T₁ g x o h => typNamed T₀ T₁ g x o (chkT_det _ (typ T₀ T₁) x g o h).1
  fit := fun T₀ T₁ g x o _ h =>
    FileSpec.ofTyping_fit (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an εs) typ S₀ S₁ clean okT
      T₀ T₁ g x o h

end TypedOracleCompiler.Slice
