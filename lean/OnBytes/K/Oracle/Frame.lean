-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/Frame.lean: the entry file's checker with A READER THAT ASKS THE ORACLE in the
place of a plain converter: the frame, general in the reader.

Why. OnBytes/TypedOracleCompiler/Slice/EntryHome.lean has the checker "convert by a plain function, then the
compiled verifier" and its bound at every converter. A converter that hashes by a fixed hash makes
that bound say next to nothing (its own words). Here the first step may ask the oracle, as the
verifier of an argument in the random-oracle model does; its queries are counted in the bound.

 `HomeData.Reader tT` a reader: an oracle computation from the five files to what the typed verifier
     takes in, a family over the two tables of the oracle's values at the public strings; a plain
     function that reads at most two roots off the files; four laws: no coin; at most tT queries;
     under every oracle what it returns has two roots, which are the roots read off the files; at
     most two roots.
 `HomeData.specO`   the checker: read through the oracle, then the compiled verifier.
 `HomeData.Left.debtsO`, `HomeData.Left.one_worldO` from what is left of the entry's debts
     (`HomeData.Left`, which names no converter): over one uniformly random oracle, for every such
     reader and every maker with at most t queries, the bad event (`HomeData.LoseO`: `EntryLose`,
     OnBytes/TypedOracleCompiler/Slice/EntryOne.lean, at this checker) has probability at most `entryB εs tT Bk V t`
     + t^2 / 2^256.
 `HomeData.chk_eq_runO`   what the checker computes under an oracle.

What is not claimed. No reader is given here. That a reader has anything to do with a program is not
said here. The strings of the event are read off the MAKER's log alone. All that the heads of
EntryHome.lean and EntryOne.lean do not claim. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHome

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (DecR decRec recZ seedBS seedEntry GE NZ Tab NoClash Raw offSet s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ rdC Spells)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- **A READER THAT ASKS THE ORACLE**: from the five files to what the typed verifier takes in, as
an oracle computation; a family over the two tables. Beside it a plain function that reads at most
two roots off the files. tT: a bound on its queries. -/
structure Reader (tT : ℕ) where
  /-- the reader -/
  ty : ∀ T₀ T₁, Files → OComp (rom 256) (Option (H.Out cfg T₀ T₁))
  /-- the roots, read off the files without a query -/
  rts : Tab → Tab → Files → List (Dig 256)
  /-- it tosses no coin -/
  noCoin : ∀ T₀ T₁ x, (ty T₀ T₁ x).NoCoin
  /-- it asks at most tT strings -/
  queries : ∀ T₀ T₁ x, (ty T₀ T₁ x).QueryBound tT
  /-- under every oracle: what it returns has two roots, and they are the roots read off the
  files -/
  roots : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : H.Out cfg T₀ T₁),
    (ty T₀ T₁ x).det g = some o → o.1.length = 2 ∧ rts T₀ T₁ x = o.1
  /-- at most two roots are read off any files -/
  few : ∀ T₀ T₁ x, (rts T₀ T₁ x).length ≤ 2

variable {H cfg} {tT : ℕ} (Y : H.Reader cfg tT)

/-- The entry's part but for its checker, with the roots that are read off the files. -/
def atO (T₀ T₁ : Tab) : EntryAt (List T3) z.lg z.s d₁ := H.atR cfg (Y.rts T₀ T₁) T₀ T₁

/-- The reader as the frame's typing. -/
def typO (εs : ℝ≥0∞) : ∀ T₀ T₁, Files → OComp (rom 256)
    (Option ((atO Y T₀ T₁).base z.T z.v z.eM (anT z.v z.s) εs).Out) := Y.ty

/-- **THE ENTRY FILE's SPEC: READ THROUGH THE ORACLE, THEN THE COMPILED VERIFIER.** -/
abbrev specO (εs : ℝ≥0∞) (Bk : ℕ) : FileSpec :=
  entrySpec z.T z.v z.eM (anT z.v z.s) (atO Y) εs (typO Y εs) tT Bk

/-- **From what is left to the whole list of the entry's debts, for every reader that asks the
oracle.** -/
theorem Left.debtsO {εs : ℝ≥0∞} {Bk V : ℕ} (h : H.Left cfg εs Bk V) :
    EntryDebts z.T z.v z.eM (anT z.v z.s) (atO Y) εs (typO Y εs) tT Bk (pubS₀ cfg)
      (pubS₁ [H.prm] cfg) (rdC z cfg) (entryB εs tT Bk V) where
  nums := OnBytes.Slice.Shapes.recNums_of_fit z h.fit εs h.price
  depthIs := fun T₀ _ => h.depthIs (dgOf cfg T₀) (dgOf_size cfg T₀)
  field := fun T₀ _ => h.field (dgOf cfg T₀) (dgOf_size cfg T₀)
  enough := fun T₀ _ => h.enough (dgOf cfg T₀) (dgOf_size cfg T₀)
  wiring := fun T₀ _ => h.wiring (dgOf cfg T₀) (dgOf_size cfg T₀)
  sound := fun T₀ _ => h.sound (dgOf cfg T₀) (dgOf_size cfg T₀)
  file :=
    { one := fun _ _ => EntryFill.pageForE_one _ _ _ _ _ _ _ _
      reads := OnBytes.Slice.Shapes.reads_ofTyping _ (typO Y εs) _ 4 tT Bk z (dgOf cfg)
        (dgOf_size cfg)
        (fun T₀ T₁ => h.depthIs (dgOf cfg T₀) (dgOf_size cfg T₀) ▸
          (atO Y T₀ T₁).plainRead z.T z.v z.eM (anT z.v z.s) rfl εs)
        (fun _ _ => EntryFill.pageForE_one _ _ _ _ _ _ _ _) h.spells
      blocks := fun T₀ _ o => le_trans (EntryFill.pageForE_blocks _ _ _ _ _ _ _ _ o)
        (h.blocksLe (dgOf cfg T₀) (dgOf_size cfg T₀))
      clean := fun T₀ T₁ F o => EntryClean.atPage_clean _ _ _ _ _ _ _ _ _ _ _ _ z.T z.v z.eM
        (anT z.v z.s) εs (pubS₀ cfg ∪ pubS₁ [H.prm] cfg T₀) (fun t ht => by
          rcases Finset.mem_union.1 ht with h0 | h1
          · exact OnBytes.Slice.Shapes.pubS₀_169 cfg t h0
          · exact OnBytes.Slice.Shapes.pubS₁_169 _ cfg T₀ t h1) F o
      flat := entry_flat z.T z.v z.eM (anT z.v z.s) (atO Y) εs (typO Y εs) tT Bk
        (pubS₀ cfg) (pubS₁ [H.prm] cfg) V h.count
      typNoCoin := Y.noCoin
      typQueries := Y.queries
      few := Y.few
      typNamed := fun T₀ T₁ g x o ho r hr => by
        show r ∈ Y.rts T₀ T₁ x
        rw [(Y.roots T₀ T₁ g x o ho).2]
        exact hr
      okT := fun T₀ T₁ g x o ho =>
        ((atO Y T₀ T₁).ok_iff z.T z.v z.eM (anT z.v z.s) rfl εs o).2 (Y.roots T₀ T₁ g x o ho).1 }

/-- **THE BAD EVENT AT A READER THAT ASKS THE ORACLE.** -/
abbrev LoseO (εs : ℝ≥0∞) (Bk : ℕ) :=
  EntryLose z.T z.v z.eM (anT z.v z.s) (atO Y) εs (typO Y εs) tT Bk (pubS₀ cfg)
    (pubS₁ [H.prm] cfg) (rdC z cfg)

/-- **(a) FOR THE ENTRY FILE: READ THROUGH THE ORACLE, THEN THE COMPILED VERIFIER.** Over one
uniformly random oracle, for every reader that asks the oracle at most tT strings and every maker
with at most t queries: the bad event has probability at most `entryB εs tT Bk V t` + t^2 / 2^256.
-/
theorem Left.one_worldO {εs : ℝ≥0∞} {Bk V : ℕ} (h : H.Left cfg εs Bk V)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (LoseO Y εs Bk) ≤ entryB εs tT Bk V t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  entry_one_world z.T z.v z.eM (anT z.v z.s) (atO Y) εs (typO Y εs) tT Bk
    (pubS₀ cfg) (pubS₁ [H.prm] cfg) (rdC z cfg) _ (h.debtsO Y)
    (OnBytes.Slice.Shapes.rdC_off z cfg [H.prm]) A t hA

/-- **What the checker computes.** Under every oracle g, at g's own values at the public strings:
the checker returns what the reader makes of the files under g, if the compiled verifier's run
accepts it under the family that is read out of g through the page; else nothing. -/
theorem chk_eq_runO (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files) :
    (((specO Y εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g =
    ((Y.ty (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d).det g).bind
      fun o => if (((atO Y (own₀ (pubS₀ cfg) g)
          (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).base z.T z.v z.eM (anT z.v z.s) εs).J.run
            o).det (readBlocks (atO Y (own₀ (pubS₀ cfg) g)
              (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).m g) = true then some o else none := by
  rw [FileSpec.chk_own]
  exact OnBytes.Slice.Shapes.chkT_det_eq _ _ d g

end HomeData

end TypedOracleCompiler.Slice
