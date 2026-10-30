-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OpenKindsAtEight.lean

Behind the eight sub-protocols of the linear claim's shared rounds no open row of the statement is
marked as a sample row (`OpenKinds`, Johnson/Desc/Means/Holds.lean): wherever their fold returns
from the shared chain's first state. One theorem.

  `openKinds_behind_eight`: general in the parameters, the key, the first tree's number, the rounds
      and the columns.

Why. `saysAt_run_U_shown` (SaysAtRunU.lean) takes this fact of shape as a premise at the state
behind the eight.

By what. The library's three: the eight keep every relation on statements that the ground's plain
functions keep (`Desc.K14.blocks_keep`, Johnson/Desc/K14/BlocksKeep.lean); "no open row is marked as
a sample row" goes along these functions (`groundKeeps_openKinds`,
Johnson/Desc/Means/FrameKeeps.lean); a fold over sub-protocols that keep a relation keeps it
(`foldBlocks_keeps`, Johnson/Desc/FoldKeeps.lean). At the first state the statement has no group
(`OpenKinds.start`). The library has the like at the key file's three chains
(`openKinds_at_reached₂`, Johnson/RunOne/KeyWalkAny.lean).

Limits. Of the eight as the kind's text makes them, at the kind's own type of claims; a proof file's
description holds them carried to its own type, behind a front sub-protocol. A fact of shape:
nothing on a value. Nothing behind a proximity test. Nothing on completeness, on soundness or on
what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.K14.BlocksKeep
import Johnson.Desc.Means.FrameKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open OnBytes.Means (OpenKinds groundKeeps_openKinds)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open Desc.K14 (P14 St blocks first)

/-- **Behind the shared chain's eight no open row is marked as a sample row.** Wherever the fold
over the eight sub-protocols that the kind's text makes returns from the chain's first state, at any
key, rounds and columns. -/
theorem openKinds_behind_eight (P : P14) (bs : List (Block St Unit)) (hb : blocks P = some bs)
    (key : TableKey) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first P.codes key) rs cols = .ok out) : OpenKinds out.1.st :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps
    (VerifiableInference.Desc.Ground.By (fun a b => OpenKinds a → OpenKinds b) Desc.K14.stOf)
    (fun _ k => k) (fun _ _ _ k₁ k₂ x => k₂ (k₁ x)) ft bs
    (Desc.K14.blocks_keep groundKeeps_openKinds P bs hb) _ rs cols out h
    (OpenKinds.start P.codes)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.openKinds_behind_eight
