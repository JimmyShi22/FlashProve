-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/OneSlot.lean: what a compiler takes of a one-chain description beside its
decision: THE ROUNDS AND THE STORED
OPENINGS, MADE OF `OneChainFileDescription.roundsDeclaredByBlocks` BY THE LIBRARY's ROAD (the third term that the frame's files
set: dec · ds · xs are one declared line).
  written F file   the declared rounds as written rounds with their stored parts: the library's
  `writtenOf`
                   (Johnson/G/RoundsOfPlan.lean) at (roundsDeclaredByBlocks, [], []): it may refuse
  roundsOf F file  the written rounds alone: of these the compiler's data ds are `Run.PQ.rds` at a
  description that holds them
  xsOf F           the stored openings: for each round, each stored part: the round's number, which
  table, from which draw, how many
Definitions with code; no theorem.
-/
import Johnson.Desc.Link.OneChainFileDescription
import Johnson.G.RoundsOfPlan
import Run.PlanQX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {Xi : Type}

def OneChainFileDescription.written (F : OneChainFileDescription Xi) (file : String) : Except String
    (List (Fmt.Round × List Fmt.Stored)) :=
  (Johnson.G.OfPlan.writtenOf file (F.roundsDeclaredByBlocks, [], [])).map (·.1)

def OneChainFileDescription.roundsOf (F : OneChainFileDescription Xi) (file : String) : Except String (List Fmt.Round) :=
  (F.written file).map (·.map (·.1))

def OneChainFileDescription.xsOf (F : OneChainFileDescription Xi) : List (Nat × Bool × Nat × Nat) :=
  F.roundsDeclaredByBlocks.zipIdx.flatMap fun r => r.1.stored.map fun s => (r.2, s.item == 1, s.lo, s.count)

end VerifiableInference.Desc
