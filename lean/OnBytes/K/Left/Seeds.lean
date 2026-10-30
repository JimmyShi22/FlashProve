-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Seeds.lean: the comparison of the seeds in the entry's checker says yes at the
program's own seeds.

The checker of an entry file (OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean, `whyOutE`) compares the two seeds
in its instance with what the seeds' chain yields under each of the two roots, in the family of
typed oracle functions that the entry's page reads out of the oracle made from Lean's BLAKE2b
(`EntryRunTop.famOf`): `cmpE`. "The program" is the Lean program `verify-on-bytes`
(OnBytes/Main.lean); it draws a table's seeds by `recordSeeds` on the table's name.

Main theorem. `cmpE_program`: let k₀ and k₁ be two keys (shape, configuration digest, table) of one
shape and one digest, with roots and digest of 32 bytes, and let `recordSeeds` on their tables'
names return l₀ and l₁. Then `cmpE`, at the page's family, under the two roots, at the seeds read
off l₀ and l₁, is true. Asked of the description D: its field is the second one; its configuration
digest is the keys'; there is at least one seed; the seeds' round fits into D's blocks, of which
there are fewer than 2 ^ 48.

What is not claimed. Nothing on soundness. That a converter's instance holds these seeds, and that
the keys are those of a call's two tables, are other files' statements. All that the heads of
OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean, EntryPagePaid.lean, EntryRunTop.lean and ShapesOBits.lean do not
claim. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop
import OnBytes.TypedOracleCompiler.Slice.EntryPagePaid
import OnBytes.TypedOracleCompiler.Slice.EntryXRun
import OnBytes.TypedOracleCompiler.Slice.ShapesOBits

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left

open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryRunTop
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open OnBytes.Slice (seedEntry seedOfDrawn seedOfDrawnC seedOfDrawnC_eq seedOf seedUnder seedBS)
open _root_.Run.PQ (View)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD)
  (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
  (sh : OnBytes.Params.IndexShape)

include hok in
/-- The comparison of the seeds says yes at the program's own seeds. -/
theorem cmpE_program (dec : XE (List T3) lg s → View → Bool)
    (hf : D.base.plan.field = .two) (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ D.K)
    (hK48 : D.K + 1 < 2 ^ 48) (t₀ t₁ : OnBytes.Params.TableName)
    (h₀ : t₀.root.size = 32) (h₁ : t₁.root.size = 32)
    (hr : (restAt D sh).size < 2 ^ 32) (l₀ l₁ : List (List E × E))
    (e₀ : recordSeeds .two (OnBytes.Key.nameOf sh D.base.cfg t₀) lg s = some l₀)
    (e₁ : recordSeeds .two (OnBytes.Key.nameOf sh D.base.cfg t₁) lg s = some l₁) :
    cmpE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (seedOfDrawnC lg s)
      (famOf D hcfg d₁ sh) [bytesToDig t₀.root, bytesToDig t₁.root] 0
      (seedOf lg s l₀, seedOf lg s l₁) = true := by
  have hp := pageForE_seeds_two D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D)
    (backOf D d₁) hK48 (sh, D.base.cfg, t₀) (sh, D.base.cfg, t₁) h₀ h₁ rfl rfl rfl hr
  have u₀ : seedUnder lg s (sh, D.base.cfg, t₀) oBits = some (seedOf lg s l₀) := by
    rw [OnBytes.Slice.Shapes.seedUnder_oBits lg s (sh, D.base.cfg, t₀) h₀ hcfg]
    show (recordSeeds .two (OnBytes.Key.nameOf sh D.base.cfg t₀) lg s).map _ = _
    rw [e₀]
    rfl
  have u₁ : seedUnder lg s (sh, D.base.cfg, t₁) oBits = some (seedOf lg s l₁) := by
    rw [OnBytes.Slice.Shapes.seedUnder_oBits lg s (sh, D.base.cfg, t₁) h₁ hcfg]
    show (recordSeeds .two (OnBytes.Key.nameOf sh D.base.cfg t₁) lg s).map _ = _
    rw [e₁]
    rfl
  have hm : (partOf D hok hcfg d₁ sh dec).m =
      pageForE D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D) (backOf D d₁) :=
    EntryFillRun.pageRunE_eq _ _ _ _ _ _ _ _
  rw [seedOfDrawnC_eq, famOf_eq D hok hcfg d₁ sh dec, hm,
    ← cmpE_eq D (bodyS D.a (saltOf D)) (ownES D hok) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry lg s) (seedOfDrawn lg s)]
  refine cmpT_det_of (Ex := ext2R (LXEs (An := List T3) (Bd := List Bool) lg s D d₁))
    (testXE D (bodyS D.a (saltOf D)) (ownES D hok) (earlyTwo d₁) (TSE D (seedEntry lg s))
      (wTSE D (seedEntry lg s)) (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
    [] default [] (plainsT D.C (dSeed (seedEntry lg s)) _)
    (seedOfE D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) (readBlocks _ oBits)
    [bytesToDig t₀.root, bytesToDig t₁.root] 0 (seedOf lg s l₀, seedOf lg s l₁) fun j hj => ?_
  have hdet := fun cm => chainAt_seeds_det (L := LXEs (An := List T3) (Bd := List Bool) lg s D d₁)
    .test D.C (seedEntry lg s) _ id D.K (chalP D.base.plan.field D.K) (we1 D.a)
    (readBlocks (pageForE D d₁ (cfgOf D) hcfg (pdOf D) (restAt D sh) (8 * saltOf D) (backOf D d₁))
      oBits) [cm]
  have hj2 : j < 2 := hj
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · refine ⟨_, hdet _, ?_⟩
    have h2 := entry_chain_seed lg s D (bodyS D.a (saltOf D)) (ownES D hok) d₁ hf hs0 hK _
      (sh, D.base.cfg, t₀) _ hp.1 oBits _ (hdet _)
    exact Option.some.inj (h2.symm.trans u₀)
  · refine ⟨_, hdet _, ?_⟩
    have h2 := entry_chain_seed lg s D (bodyS D.a (saltOf D)) (ownES D hok) d₁ hf hs0 hK _
      (sh, D.base.cfg, t₁) _ hp.2 oBits _ (hdet _)
    exact Option.some.inj (h2.symm.trans u₁)

end OnBytes.K.Left
