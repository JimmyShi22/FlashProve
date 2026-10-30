-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Side.lean: the honest side of an attention segment's own rounds
with the form of a simulator beside each part, as a side (`Side`, Honest/Side.lean). Definitions
with code; no theorem.

  `k5Pairs`   the kind's row at a place, each part with the form of a simulator
  `k5Side`    that row beside the member of a description's first chain that stands at the place

The forms. Beside a masked sumcheck: as many coins of its own as the sumcheck sends scalars, each
sent as it is (`sumSim`, Honest/Sum.lean). Beside the round of masked scalars: the like. Beside a
round that sends nothing: no coin, an empty round. None reads anything that it is handed but its own
coins.

THE SIMULATORS ARE DATA. Nothing is said here of what they are good for, and no sentence on a side
(`Good`) is stated or claimed at this one.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- The row at a place, each part with the form of a simulator beside it. -/
def k5Pairs (cells : Tr → Cells) (Z : Seat5) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb) :=
  (k5Half cells Z).parts.zip (simsOf Z.place Z.P.x)

/-- **The side**: `none` if no member of the list stands at the place. bs: the first chain's list
(`Chain.blocksInOrder`). -/
def k5Side (bs : List (VerifiableInference.Desc.Block S Cl)) (cells : Tr → Cells) (Z : Seat5) :
    Option (Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) :=
  Side.seated bs Z.place (k5Pairs cells Z)

end ProofFile.Honest.K5
