-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunG.lean: the run's function of an entry file, under `famOf`'s family with
the hash function an argument, is tied to the checker of the entry's part at every hash function.

Definitions, and statements with their proofs. `HomeData.chk_iff_why`
(OnBytes/TypedOracleCompiler/Slice/EntryRunTie.lean) says at every g: the checker "convert; two roots; the judge's
run" returns o under g exactly if the converter makes o of the files and the run's function
`whyOutE` says "YES" on o under the family that is read out of g through the part's page. That
family is no term for a run. The family that a run evaluates (`EntryRunTop.famOf`) stands at one
fixed function, and its pins hold that function's digest of the parameter bytes. Here both are
letters.

Main names:
  `EntryRunTop.famOfG D hcfg d₁ sh pd g`: `famOf`'s text with g for the realised oracle and pd for
    the format's own digest of the parameter bytes (`famSafeG`,
    OnBytes/TypedOracleCompiler/Run/EntryPageSafeG.lean).
  `EntryRunTop.famOfG_eq`: it is the family read out of g through the entry's page at these pins.
  `EntryRunTop.famOfG_oBits`: at `Run.oBits` and `pdOf D` it is `famOf`.
  `HomeData.PinsAtG sh c`: `PinsAt` less its equation on pd: four equations. `PinsAt.toG`.
  `HomeData.famOfG_at`: where the four hold, `famOfG` at the second table's value at the string of
    the parameter bytes is the family read out of g through the part's page: every g, any two
    tables.
  `HomeData.chk_iff_whyG`: `chk_iff_why` with `famOfG` at g's own values at the public strings.

Limits.
  1. H is a letter: the checker is that of the entry's part H. A bound over a random function is
     proved of this checker at two written parts alone (`homeFull`, `homeSmall`; the bounds:
     OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean, EntrySmallTop.lean), under their own hypotheses. What they
     bound is not "a yes on a false statement": the head of OnBytes/TypedOracleCompiler/Slice/EntryOne.lean says
     what. No bound is joined here.
  2. The four equations and hcfg are hypotheses. They are met at a ground where the pins fit
     (OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean).
  3. That `whyOutE` under `famOfG` comes home is a fact of a run; none has been made. By the heads
    of the files on its walk it does not run at the full size as
     it stands.
  4. A yes of the checker is a yes of the value that the converter hands over, not of the files. All
     that the heads of EntryRunTie.lean, EntryRunTop.lean and EntryPageSafeG.lean do not claim. The
     compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
     definitions of Compile/.
     No probability stands here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunTie
import OnBytes.TypedOracleCompiler.Run.EntryPageSafeG

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.EntryRunTop
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryFillRun TypedOracleCompiler.Slice.EntryReadsAt
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.EntryPageSafe
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
  (sh : OnBytes.Params.IndexShape) (pd : Dig 256) (g : Fam (rom 256))

/-- The page's family with the hash function an argument, for a run: `famOf`'s text with g where
that has the realised oracle, and with the digest pd of the parameter bytes a letter where that has
the format's own. -/
def famOfG : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) :=
  famSafeG D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (d₁, d₁)
    (pinsE D d₁ (cfgOf D) hcfg pd (restAt D sh)) (D.K + 1) (8 * saltOf D) (backOf D d₁) g

/-- It is the family that is read out of g through the entry's page at these pins: every g. -/
theorem famOfG_eq :
    famOfG D hcfg d₁ sh pd g =
      readBlocks (pageForE D d₁ (cfgOf D) hcfg pd (restAt D sh) (8 * saltOf D) (backOf D d₁)) g :=
  famSafeG_eq _ _ _ _ _ _ _ _ _

/-- At the realised oracle and the format's own digest of the parameter bytes it is `famOf`. -/
theorem famOfG_oBits : famOfG D hcfg d₁ sh (pdOf D) oBits = famOf D hcfg d₁ sh :=
  famSafeG_oBits _ _ _ _ _ _ _ _

end TypedOracleCompiler.Slice.EntryRunTop

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (decRec GE NZ seedEntry seedOfDrawnC Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁) (cfg : Cfg)

/-- `PinsAt` less its equation on the digest of the parameter bytes: four equations, none of which
names a hash function's value but the digest c. -/
structure PinsAtG (sh : OnBytes.Params.IndexShape) (c : ByteArray) : Prop where
  /-- the description holds the digest -/
  cfgIs : (H.DX c).base.cfg = c
  /-- what stands behind a root in a table's name -/
  restIs : TypedOracleCompiler.Run.FirstName.restOf c z.T.a z.T.l z.T.r z.v z.s z.shape.saltBytes =
    EntryRunTop.restAt (H.DX c) sh
  /-- the sizes' length of a salt is the plan's -/
  saltIs : z.shape.saltBytes = (H.DX c).base.plan.salt
  /-- the code behind the escape -/
  backIs : H.back c = EntryRunTop.backOf (H.DX c) d₁

omit [DecidableEq (Sd1 z.lg z.s)] in
variable {H} in
/-- The five give the four. -/
theorem PinsAt.toG {sh : OnBytes.Params.IndexShape} {c : ByteArray} {pd : Dig 256}
    (h : H.PinsAt sh c pd) : H.PinsAtG sh c :=
  ⟨h.cfgIs, h.restIs, h.saltIs, h.backIs⟩

/-- Where the four pins agree, the family that a run evaluates at g, at the value that the second
table holds at the string of the parameter bytes, is the family that is read out of g through the
part's page: every g, any two tables. -/
theorem famOfG_at (conv : H.Conv cfg) (sh : OnBytes.Params.IndexShape) (T₀ T₁ : Tab)
    (hp : H.PinsAtG sh (dgOf cfg T₀)) (hcfg : (H.DX (dgOf cfg T₀)).base.cfg.size = 32)
    (g : Fam (rom 256)) :
    EntryRunTop.famOfG (H.DX (dgOf cfg T₀)) hcfg d₁ sh (T₁ (s0Of (H.prm (dgOf cfg T₀)))) g =
      readBlocks (H.at cfg conv T₀ T₁).m g := by
  rw [EntryRunTop.famOfG_eq]
  congr 1
  show EntryFill.pageForE _ _ _ _ _ _ _ _ = EntryFill.pageForE _ _ _ _ _ _ _ _
  exact pageForE_congr _ d₁ hp.cfgIs _ _ rfl hp.restIs.symm
    (congrArg (8 * ·) hp.saltIs.symm) hp.backIs.symm

/-- The checker of which the bound speaks returns o under g exactly if the converter makes o of the
files and the run's function says "YES" on o under the family that a run evaluates at g: at every
g, at g's own values at the public strings. -/
theorem chk_iff_whyG (conv : H.Conv cfg) (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files)
    (o : H.Out cfg (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g))
    (sh : OnBytes.Params.IndexShape) (hp : H.PinsAtG sh (dgOf cfg (own₀ (pubS₀ cfg) g)))
    (hcfg : (H.DX (dgOf cfg (own₀ (pubS₀ cfg) g))).base.cfg.size = 32) :
    (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g = some o ↔
      conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d = some o ∧
        whyOutE (H.DX (dgOf cfg (own₀ (pubS₀ cfg) g)))
          (H.ok _ (dgOf_size cfg (own₀ (pubS₀ cfg) g))) d₁
          (H.dec (dgOf cfg (own₀ (pubS₀ cfg) g)))
          (EntryRunTop.famOfG (H.DX (dgOf cfg (own₀ (pubS₀ cfg) g))) hcfg d₁ sh
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g
              (s0Of (H.prm (dgOf cfg (own₀ (pubS₀ cfg) g))))) g) o.1 o.2.1
          (toPS _ _ o.2.2) = "YES" := by
  rw [H.famOfG_at cfg conv sh _ _ hp hcfg g]
  exact H.chk_iff_why cfg conv εs Bk g d o

end HomeData

end TypedOracleCompiler.Slice
