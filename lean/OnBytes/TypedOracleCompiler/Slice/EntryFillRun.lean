-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFillRun.lean: the page of an entry's judge at the port's label, and an
entry's part's data at that page, as terms that Lean's compiler takes; each equal to the term of
which the theorems speak. NOT TO BE EVALUATED (see OnBytes/TypedOracleCompiler/Run/EntryPageRun.lean's head).

`EntryFill.pageForE` and `EntryClean.atPage` hold `EntryPage.implE`, whose tests are by classical
logic: Lean's compiler refuses them (measured). OnBytes/TypedOracleCompiler/Run/EntryPageRun.lean says the page once
more with computable tests and shows that it is the same implementation. This file carries that to
the two terms of which the run's theorem speaks. The sibling is a second form of the library's
soundness road, under OnBytes/TypedOracleCompiler/.
 - `pgRun`: the page's data (OnBytes/TypedOracleCompiler/Run/PageG.lean: `Page`) at computable tests; `pgRun_impl`:
   the general implementation at these data is `pageForE`;
 - `pageRunE`: the implementation; `pageRunE_eq`: it is `pageForE`;
 - `atRun`: the data of an entry's part; `atRun_eq`: they are `atPage`'s.

Main definitions: `pgRun`, `pageRunE`, `atRun`.
Main theorems: `pgRun_impl`, `pageRunE_eq`, `atRun_eq`.

Not claimed. That the compiler takes the three definitions is a fact of the build, not a theorem.
That a term has code does not say that its evaluation ends: these do not come home. Nothing on
speed. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier`
is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPageRun
import OnBytes.TypedOracleCompiler.Slice.EntryClean

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.EntryFillRun
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryClean TypedOracleCompiler.Run.EntryPageRun
open TypedOracleCompiler.Run.PageG
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open OnBytes.Slice (seedEntry)
open OnBytes.Slice.Shapes (Files)
open _root_.Run.PQ (View)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray)
  (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)))

/-- The page's data, at computable tests. -/
def pgRun : Page (Ls D d₁) (D.K + 1) :=
  pageT (Tests.run D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (d₁, d₁))
    (pinsE D d₁ cfg hcfg pd rest) (D.K + 1) (KeyLeaves.leavesAt (L0 D d₁) n cfg) back

/-- The implementation, at computable tests. -/
def pageRunE : OracleCoding (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) 256 := implG (pgRun D d₁ cfg hcfg pd rest n back)

/-- It is `EntryFill.pageForE`. -/
theorem pageRunE_eq :
    pageRunE D d₁ cfg hcfg pd rest n back = pageForE D d₁ cfg hcfg pd rest n back :=
  implT_eq _ _ _ _ _

/-- The general implementation at `pgRun` is `EntryFill.pageForE`. -/
theorem pgRun_impl :
    implG (pgRun D d₁ cfg hcfg pd rest n back) = pageForE D d₁ cfg hcfg pd rest n back :=
  pageRunE_eq D d₁ cfg hcfg pd rest n back

variable (B : BodyD (List Bool)) (E : OwnE (List Bool) D)
  (dec : XE (List T3) lg s → View → Bool) (R : Reading (Ls D d₁) B.embE)
  (rts : Files → List (Dig 256))

/-- The data of an entry's part at the page, at computable tests. -/
def atRun : EntryAt (List T3) lg s d₁ :=
  ⟨D, List Bool, B, E, dec, R, pageRunE D d₁ cfg hcfg pd rest n back, rts⟩

/-- They are `EntryClean.atPage`'s. -/
theorem atRun_eq :
    atRun D d₁ cfg hcfg pd rest n back B E dec R rts =
      atPage D B E dec R rts cfg hcfg pd rest n back := by
  unfold atRun atPage
  rw [pageRunE_eq]

end TypedOracleCompiler.Slice.EntryFillRun
