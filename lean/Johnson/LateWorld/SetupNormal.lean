-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SetupNormal.lean: THE REDUCTION's SETUP AGAINST THE REAL GAME IN ITS NORMAL FORM:
the proof of Spec.setupNormal (Johnson/LateWorld/SpecSetupA.lean).

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

The making of a table is hash work on the reduction's own table of answers, then one call to the
game (run_tableA). The hash work reads the table of answers alone, the game's reply reads the game's
state and the seed alone: so the two can be made in either order (PMF.bind_comm). For a list of
tables, one exchange a table carries all hash work to the front (run_tablesA); for the setup, one
more carries the first table's call behind the copies' hash work.

Main names (namespace OnBytes.LateWorld).
  run_tableA    one table against the game: its hash work, then the call.
  run_tablesA   a list of tables against the game: all hash work, then all calls.
  setupNormal   THE STATEMENT.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSetupA

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop)
  (s1 : ℕ) (i : I)

/-- One table against the game: its hash work, then the call. -/
theorem run_tableA (s : ℕ → Bits) (T : Tb W) (g : StGm W) :
    runG W r₀ a Gs s1 i (tableA W S r₀ a.side s T) g =
      (tabFR W S a.b₀ s T).bind fun o =>
        (repG W r₀ a Gs s1 i g (.table o.1.2)).bind fun p =>
          PMF.pure ((tabOf r₀ o.1.1 p.1, o.2), p.2) := by
  unfold tableA tabFR
  rw [runG_bind, runG_defer, PMF.bind_map, PMF.bind_map]
  refine congrArg _ (funext fun o => ?_)
  show runG W r₀ a Gs s1 i (.call (.table o.1.2) _) g = _
  rw [runG_call]
  refine congrArg _ (funext fun p => ?_)
  cases p.1 <;> rfl

/-- A list of tables against the game: all hash work, then all calls. -/
theorem run_tablesA : ∀ (ss : List (ℕ → Bits)) (T : Tb W) (g : StGm W),
    runG W r₀ a Gs s1 i (tablesA W S r₀ a.side ss T) g =
      (tabsFR W S a.b₀ ss T).bind fun os =>
        (gameTabs W r₀ a Gs s1 i os.1 g).bind fun q => PMF.pure ((q.1, os.2), q.2)
  | [], T, g => by
    simp only [tablesA, tabsFR, gameTabs, runG_halt, PMF.pure_bind]
  | s :: ss, T, g => by
    rw [tablesA, runG_bind, run_tableA]
    simp only [tabsFR, gameTabs, PMF.bind_bind, PMF.pure_bind, PMF.bind_map, PMF.map,
      Function.comp_def, runG_bind, runG_halt, run_tablesA ss]
    refine congrArg _ (funext fun o => ?_)
    exact PMF.bind_comm _ _ _

/-- **The reduction's setup against the game in its normal form.** -/
theorem setupNormal : Spec.setupNormal := by
  intro I X lam L Bd aT aL W S cA r₀ a Gs s1 i T g
  rw [setupA_eq, runG_bind, runG_lazy, PMF.bind_map]
  simp only [phase1, contW, PMF.bind_bind, PMF.pure_bind, Function.comp_def, runG_bind,
    run_tableA, run_tablesA]
  refine congrArg _ (funext fun o₀ => congrArg _ (funext fun o₁ => ?_))
  exact PMF.bind_comm _ _ _

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.setupNormal
