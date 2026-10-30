-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Count.lean: EVERY RUN OF AN ADVERSARY AGAINST THE CHALLENGER STAYS WITHIN THE
WRITTEN COUNTS: the proofs of Spec.stepCount and Spec.withinTwin (Johnson/TokenRules/Spec.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  stepCount    From the statement on a step of the challenger (Spec.safeStep): what holds of a
               program whatever the coins, the answers and the tables are, holds of every outcome of
               its run, in both modes (safeRunO, Compile/Batch/Discipline.lean).
  withinTwin   From stepCount and from Spec.zeroOutside, by the library's induction over an
               adversary that asks for one setup and then for batches (within_interactB,
               Compile/Batch/DisciplineWorld.lean), and the library's step from a well-formed state
               within counts to what deferred programming asks (withinO',
               Compile/Batch/WithinVCB.lean). The invariant does not look at the table, so a query
               of the adversary keeps it.
Both are stated from their grounds as hypotheses; the closed forms are in
Johnson/TokenRules/Closed.lean.
Follows the pattern of Compile/Batch/WithinVCB.lean.

-/
import Johnson.TokenRules.Spec
import Compile.Batch.WithinVCB

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-- **The step of the induction over an adversary**, from the statement on a step. -/
theorem stepCount (hS : Spec.safeStep) : Spec.stepCount := by
  intro I X lam L Bd aT aL W S cA r₀ h tl bl bf i m s d c hl hI y hy
  have h0 := safeRunO _ _ _ _ _ d _ m (hS I X lam L Bd aT aL W S cA r₀ h tl bl bf i s c d hl hI)
    y hy
  exact ⟨h0.1, fun o => ⟨h0.2.plain o, h0.2.marked o⟩⟩

/-- **Every run against the challenger stays within the counts.** -/
theorem withinTwin (hS : Spec.stepCount) (hZ : Spec.zeroOutside) : Spec.withinTwin := by
  intro I X lam L Bd aT aL W S cA r₀ h tl bl bf i m α ok A n hl hA x hx
  obtain ⟨hI, hc⟩ := within_interactB (challT W S cA r₀ h tl i) m
    (InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)))
    (eSetup W S h) (mSetup W h tl) (eSess W) (mSess W h tl)
    (fun _ _ T hI => ⟨hI.1.table T, hI.2⟩)
    (fun s d c hI => hS I X lam L Bd aT aL W S cA r₀ h tl bl bf i m s d c hl hI)
    ok A false n none (DSt.init _) hA (invT_init _) x hx
  refine withinO' _ (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) _ _ _ _ hI.1
    (hZ I X lam L Bd aT aL W h tl n) (fun o => ?_) (fun o => ?_)
  · have h1 : x.2.2.nPlain o ≤ 0 + eSetup W S h o + n * eSess W o := (hc o).1
    rw [Nat.zero_add] at h1
    exact h1
  · have h1 : nEv x.2.2 o ≤ 0 + mSetup W h tl o + n * mSess W h tl o := (hc o).2
    rw [Nat.zero_add] at h1
    exact h1

/-- **The counts of the token programs**, from the statement on a step and the zeros. -/
theorem countTwin (hS : Spec.safeStep) (hZ : Spec.zeroOutside) : Spec.countTwin :=
  ⟨stepCount hS, hZ, withinTwin (stepCount hS) hZ⟩

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.stepCount
#print axioms OnBytes.TokenRules.withinTwin
