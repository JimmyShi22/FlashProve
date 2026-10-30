-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubReal.lean: lemmas for the first two hops of zero-knowledge compilation for batches,
with a function of the key published at the setup (the challenger `VCBP` of
Compile/Batch/PubChall.lean).

This file does not prove the hops. The kindred statements, with a program pq in the place of the
prover's, are in Compile/Batch/PubProgReal.lean: `map_fst_interact_realWPG` and `real_eq_modeRPG`,
on the token form `argBPGT`, under the hypothesis `MaskProg` on pq; `hopRPG`, which compares
`RealBPG'` with mode R (`world false`; the modes: Rom/Defer.lean) of the challenger `VCBPG`. (not
all hypotheses are named here: see their statements)

  `erase_Pp_replyP`  As far as the reply to a batch goes, the program that makes proof strings for
                     the adversary's own requests only is the same oracle algorithm (`erase`) as
                     the program that makes all.
  `VCBP_setup`, `VCBP_own`, `VCBP_none`  The steps of `VCBP`, unfolded: the setup; a batch with a
                                         request of the adversary's own; a batch without one.
-/
import Compile.Batch.PubChall
import Compile.Batch.RealB
import Compile.Step1_life2_Chall

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall GAdm realW ownPf)
open Compile.Life2
  (virt viewVals ofOComp_reply chall_reply runLazy_bind_pure run_fresh0 run_bind map_fst_call
    map_fst_query viewVals_dummy run_false_virt run_false_eq_erase vals_prefix)

/-! ## What is not shown is not made -/

section RealP

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)

theorem erase_Pp_replyP {γ : Type} (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit)
    (vs : List Bits) (st : γ) :
    ((erase (Pp W WP p k (ownFlag b) (reqs b)) vs).bind fun o =>
        OComp.pure (replyOfP V b o.1, st)) =
      (erase (Pp W WP p k (fun _ => true) (reqs b)) vs).bind fun o =>
        OComp.pure (replyOfP V b o.1, st) := by
  have h := congrArg
    (fun c : TypedOracleComputation lam W.K L (BIn lam L × γ) => c.bind fun y => OComp.pure (toP V y.1, y.2))
    (RealB.erase_Pp_reply W WP p k b vs st)
  simp only [OComp.bind_assoc, OComp.bind] at h
  exact h

end RealP

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)

namespace HopRP

/-! ## The replies, unfolded -/


theorem VCBP_setup :
    (VCBP W WP p pw i).step none .setup =
      (Cp W WP p i).bind fun o =>
        Step.fresh 0 fun t => Step.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t)) := rfl

theorem VCBP_own (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    (VCBP W WP p pw i).step (some (k, N₀)) (.batch b) = Step.fresh 0 fun t₀ =>
      (virt N₀ (t₀ + 1 - N₀) (Pp W WP p k (ownFlag b) (reqs b))).bind fun πs =>
          Step.pure (replyOfP V b πs, some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h, if_pos rfl]

theorem VCBP_none (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    (VCBP W WP p pw i).step (some (k, N₀)) (.batch b) = Step.pure (.inr [], some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h]
  rfl




end HopRP

open HopRP

end Compile.Batch
