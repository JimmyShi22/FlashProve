-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunTieX.lean: `HomeData.yes_of_run` (OnBytes/TypedOracleCompiler/Slice/EntryRunTie.lean) for
the roots and the WHOLE instance of an accepted value: both tables' answers and both tables' seeds.

Why. `HomeData.stmt` (OnBytes/TypedOracleCompiler/Slice/EntryHomeRun.lean) gives out the two roots and both tables'
answers. The commitment ID's string holds the record's seeds too (R4.11), so the statement word of a
typed value (`stmtId`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) reads the seeds in the value. Whoever
carries that word from the value that a converter makes to the value that the checker returns needs
that the two have the same seeds.

Main names (namespace `TypedOracleCompiler.Slice.HomeData`):
  `stmtX o`: the two roots and the instance.
  `yes_of_runX`: `yes_of_run` with `stmtX` in the place of `stmt`: the same premises, the same
    proof.

Limits: those of `yes_of_run`: at the one oracle made from the format's hash; no probability.
Nothing says that the seeds in a value are the drawn ones: that is the judge's test. Nothing on
soundness or on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunTie

set_option autoImplicit false

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
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- The two roots and the whole instance of an accepted value: both tables' answers and both tables'
seeds. -/
def stmtX {χ δ : Type} (o : List (Dig 256) × χ × δ) : List (Dig 256) × χ := (o.1, o.2.1)

set_option maxRecDepth 20000 in
/-- `yes_of_run` for the roots and the whole instance: the value that the checker returns has o's
roots, answers and seeds. -/
theorem yes_of_runX (convC : H.ConvC) (sh : OnBytes.Params.IndexShape)
    (εs : ℝ≥0∞) (Bk : ℕ) (d : Files) (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hp : H.PinsAt sh c (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits
      (s0Of (H.prm c))))
    (hcfg : (H.DX c).base.cfg.size = 32) (o : H.OutC c h32) (ho : convC c h32 d = some o)
    (hy : whyOutE (H.DX c) (H.ok c h32) d₁ (H.dec c) (EntryRunTop.famOf (H.DX c) hcfg d₁ sh) o.1
      o.2.1 (toPS _ _ o.2.2) = "YES") :
    ((((H.spec cfg (H.convOf cfg convC) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits).map
          (fun o' : H.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) => stmtX o') =
      some (stmtX o) := by
  subst hc
  have ef := H.famOf_at cfg (H.convOf cfg convC) sh _ _ hp hcfg
  have h := (H.chk_iff_why cfg (H.convOf cfg convC) εs Bk _root_.Run.oBits d o).2
    ⟨ho, (congrArg (fun F => whyOutE _ _ d₁ _ F o.1 o.2.1 (toPS _ _ o.2.2)) ef).symm.trans hy⟩
  rw [h]
  rfl

end HomeData

end TypedOracleCompiler.Slice

#print axioms TypedOracleCompiler.Slice.HomeData.yes_of_runX
