-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunTop.lean: THE VERIFIER's SIDE OF A RUN ON AN ENTRY FILE, AS ONE PLAIN
DEFINITION THAT LEAN's COMPILER TAKES, and the theorem that ties it to the judge's own run: what is
evaluated says yes exactly if what was read is assembled to a typed value and the judge's run on
that value, under the family that is read out of the oracle made from Lean's BLAKE2b through the
entry's page, says yes.

The pipeline has two stages. A converter, which is not trusted, turns the bytes of an entry file
into what a reader returns: two roots, an instance, a chain as read. Then the verifier: the judge's
run of OnBytes/TypedOracleCompiler/Slice/JudgeE.lean (`judgeRunEL`: the seeds' chain under each root with a
comparison, then the compiled lax verifier of the written link), over one oracle through a page.
This file is the second stage. It joins an evaluable mirror of the judge's run
(OnBytes/TypedOracleCompiler/Slice/EntryJudgeRun.lean: `runJE`), the page's family at the realised oracle in a form
that comes home when evaluated (OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean: `famSafe`; the page's own data
do not: an interface as a value is deadly to the evaluator), the page at computable tests
(OnBytes/TypedOracleCompiler/Slice/EntryFillRun.lean), of which the theorem speaks, a total code `back` that
compiles (OnBytes/TypedOracleCompiler/Run/PageESer.lean), and a twin of `Slice.seedOfDrawn` that compiles
(OnBytes/Slice/SeedDrawnCode.lean). NO PIN IS AN ARGUMENT: the configuration digest, the parameter
digest, the salt's length and what stands behind a root in a table's name are read off the
description D and the tables' shape; the label is the port's label of a link's chain, whatever D
says. The sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `cfgOf D`, `pdOf D`, `restAt D sh`, `saltOf D`, `backOf D d₁`: the pins off the description: its
   configuration digest; the format's hash under 169 of its parameter bytes; what stands behind the
   root in a table's name, at the shape sh; the plan's salt, in bytes; the total code;
 - `pageOf`: the page's data at these pins (for the theorems: not to be evaluated); `famOf`: its
   family, for the evaluator;
 - `partAt R rts`: the data of an entry's part at these pins (`EntryFillRun.atRun`), at any reading
   and any way to read roots off files; `partOf`: the same with placeholders;
 - `runTop D hok hcfg d₁ sh dec r0 r1 x o : Bool`: WHAT RUNS;
 - `runTop_eq`, `runTop_at`: it is true exactly if `assembleEZ` returns some typed value `out` and
   the judge's run of the part, on `out`, under `readBlocks (the part's m) Run.oBits`, is true: at
   `partOf`, and at `partAt R rts` for all R, rts;
 - `partAt_atPage`, `partAt_atRead`: the part is the one of which OnBytes/TypedOracleCompiler/Slice/EntryClean.lean
   and EntryReadsAt.lean speak.

Main definitions: `pageOf`, `famOf`, `partAt`, `runTop`.
Main theorems: `famOf_eq`, `runTop_eq`, `runTop_at`, `partAt_atPage`, `partAt_atRead`.

Not claimed. That the compiler takes `runTop` is a fact of the build, not a theorem; nothing on
speed. NOTHING TIES THE PINS TO A FILE: that D's label is the port's label of a link's chain (the
page has that label, whatever D says), that every stored table's salt is the plan's, that the
shape's salt is the plan's, that D's depth is the shape's: guards for whoever runs it
(a file of this project that is not in this library: `pinsOk D sh`). WHAT THE JUDGE ASKS OF AN
OUTPUT BESIDE THE RUN's
YES (two roots; openings that the reading keeps) is not had from `runTop`. The converter is not
here. No soundness: that the judge's yes means anything is another file's. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryJudgeRun
import OnBytes.TypedOracleCompiler.Slice.EntryFillRun
import OnBytes.TypedOracleCompiler.Slice.EntryReadsAt
import OnBytes.TypedOracleCompiler.Slice.PartChainStr
import OnBytes.TypedOracleCompiler.Run.EntryPageSafe
import OnBytes.TypedOracleCompiler.Run.PageESer
import OnBytes.Slice.SeedDrawnCode

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.EntryRunTop
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryFillRun TypedOracleCompiler.Slice.EntryReadsAt
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.EntryPageSafe
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open OnBytes.Slice (seedEntry seedOfDrawn seedOfDrawnC seedOfDrawnC_eq GE decRec)
open OnBytes.Slice.Shapes (Files)
open _root_.Run.PQ (View SgX serW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open scoped ENNReal

/-! ## The pins, off the description -/

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD)

/-- The configuration's digest. -/
def cfgOf : ByteArray := D.base.cfg

/-- The parameter digest: the format's hash under 169, index 1, of the parameter bytes. -/
def pdOf : Dig 256 := bytesToDig (_root_.Fmt.formatHash 169 0 1 _root_.Fmt.zero32 D.base.params)

/-- What stands behind the root in a table's name, at the tables' shape. -/
def restAt (sh : OnBytes.Params.IndexShape) : ByteArray :=
  FirstName.restOf D.base.cfg sh.code.logN sh.code.ell sh.code.r sh.v sh.answers sh.saltBytes

/-- The bytes of a file's salt. -/
def saltOf : ℕ := D.base.plan.salt

/-- The total code behind the escape. -/
def backOf (d₁ : Sd1 lg s) : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)) :=
  PageESer.backEs D d₁ (bodyS D.a (saltOf D)) (Ser.prod Ser.natG (Ser.list serW))

variable (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
  (sh : OnBytes.Params.IndexShape)

/-- The page's data at these pins. -/
def pageOf : Page (Ls D d₁) (D.K + 1) :=
  pgRun D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D) (backOf D d₁)

/-- Its family at the oracle made from Lean's BLAKE2b, for the evaluator: by the writing side
that takes the interface in types alone (OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean). -/
def famOf : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) :=
  famSafe D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (d₁, d₁)
    (pinsE D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh)) (D.K + 1) (8 * saltOf D) (backOf D d₁)

variable (dec : XE (List T3) lg s → View → Bool)

/-- The data of an entry's part at these pins, at any reading R and any way rts to read roots
off files: the run reads neither. -/
def partAt (R : Reading (Ls D d₁) (bodyS D.a (saltOf D)).embE) (rts : Files → List (Dig 256)) :
    EntryAt (List T3) lg s d₁ :=
  atRun D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D) (backOf D d₁)
    (bodyS D.a (saltOf D)) (ownES D hok) dec R rts

/-- The same with placeholders: the wide reading, and no root read off files. A part that is to
deliver needs its own: `partAt`. -/
def partOf : EntryAt (List T3) lg s d₁ :=
  partAt D hok hcfg d₁ sh dec (rdW (d₁ := d₁) D (saltOf D) (ownES D hok)) fun _ => []

/-- WHAT RUNS: the judge's run, evaluable, at the page's evaluable family. r0, r1: the two
roots; x: the instance; o: the chain as read. -/
def runTop (r0 r1 : ByteArray) (x : XE (List T3) lg s) (o : _root_.Fmt.ChainOut) : Bool :=
  runJE D dec (bodyS D.a (saltOf D)) (ownES D hok) (earlyTwo (A := List T3 × List T3) d₁)
    (seedEntry lg s) (seedOfDrawnC lg s) (famOf D hcfg d₁ sh) r0 r1 x o

variable (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : List T3 → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) (εs : ℝ≥0∞)

/-- The evaluable family is the family that is read out of the realised oracle through the part's
implementation. -/
theorem famOf_eq :
    famOf D hcfg d₁ sh = readBlocks (partOf D hok hcfg d₁ sh dec).m oBits := by
  have hm : (partOf D hok hcfg d₁ sh dec).m =
      pageForE D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D) (backOf D d₁) :=
    pageRunE_eq _ _ _ _ _ _ _ _
  rw [hm]
  exact famSafe_eq _ _ _ _ _ _ _ _

/-- WHAT RUNS IS THE JUDGE's OWN RUN. `runTop` is true exactly if what was read is assembled to
a typed value, and the run of the judge of the part `partOf` on that value, under the family that is
read out of the oracle made from Lean's BLAKE2b through the part's implementation, is true. -/
theorem runTop_eq (r0 r1 : ByteArray) (x : XE (List T3) lg s) (o : _root_.Fmt.ChainOut) :
    runTop D hok hcfg d₁ sh dec r0 r1 x o = true ↔
      ∃ out, assembleEZ D dec (bodyS D.a (saltOf D)) (ownES D hok)
          (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))
          (wTSE D (seedEntry lg s)) (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)
          r0 r1 x o = some out ∧
        ((((partOf D hok hcfg d₁ sh dec).base T v eM an εs).J.run out).det
          (readBlocks (partOf D hok hcfg d₁ sh dec).m oBits)) = true := by
  unfold runTop
  rw [seedOfDrawnC_eq, famOf_eq D hok hcfg d₁ sh dec]
  exact runJE_eq D dec (bodyS D.a (saltOf D)) (ownES D hok)
    (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (seedOfDrawn lg s) _ r0 r1 x o

/-- The same at any reading and any roots: the judge's run and the implementation hang on
neither. -/
theorem runTop_at (R : Reading (Ls D d₁) (bodyS D.a (saltOf D)).embE)
    (rts : Files → List (Dig 256)) (r0 r1 : ByteArray) (x : XE (List T3) lg s)
    (o : _root_.Fmt.ChainOut) :
    runTop D hok hcfg d₁ sh dec r0 r1 x o = true ↔
      ∃ out, assembleEZ D dec (bodyS D.a (saltOf D)) (ownES D hok)
          (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))
          (wTSE D (seedEntry lg s)) (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)
          r0 r1 x o = some out ∧
        ((((partAt D hok hcfg d₁ sh dec R rts).base T v eM an εs).J.run out).det
          (readBlocks (partAt D hok hcfg d₁ sh dec R rts).m oBits)) = true :=
  runTop_eq D hok hcfg d₁ sh dec T v eM an εs r0 r1 x o

/-- The part is `EntryClean.atPage`'s, of which the clauses `one`, `blocks`, `clean` are shown.
-/
theorem partAt_atPage (R : Reading (Ls D d₁) (bodyS D.a (saltOf D)).embE)
    (rts : Files → List (Dig 256)) :
    partAt D hok hcfg d₁ sh dec R rts =
      EntryClean.atPage D (bodyS D.a (saltOf D)) (ownES D hok) dec R rts (cfgOf D) hcfg (pdOf D)
        (restAt D sh) (8 * saltOf D) (backOf D d₁) :=
  atRun_eq _ _ _ _ _ _ _ _ _ _ _ _ _

/-- And `EntryReadsAt.atRead`'s, of which `Spells` and `PlainRead` are shown. This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. -/
theorem partAt_atRead (R : Reading (Ls D d₁) (bodyS D.a (saltOf D)).embE)
    (rts : Files → List (Dig 256)) :
    partAt D hok hcfg d₁ sh dec R rts =
      atRead D (saltOf D) (ownES D hok) dec R rts (cfgOf D) hcfg (pdOf D) (restAt D sh)
        (PageESer.serSd2 lg s) :=
  partAt_atPage D hok hcfg d₁ sh dec R rts

end TypedOracleCompiler.Slice.EntryRunTop
