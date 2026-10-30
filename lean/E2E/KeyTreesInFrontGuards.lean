-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTreesInFrontGuards.lean

How many trees the key file's shared chain has sent in front of its two proximity tests, off the
blocks themselves and not off a place's field `free`, by Lean's evaluator.

  `PF`, `QK`       copied word for word from E2E/KeyShapeSharedFull.lean, which is not on
                   the lane, so that this trial stands on the working ground alone
  `treesOfBlock`   how many oracle messages a block declares
  `treesEight`     the same for each of the eight, at the written value `QK`
  `treesGu`        the same for the test on G_u, at the written places `PF`

Limits. Evaluations outside the kernel: no theorem. The list of eight is `blocksOr QK`, the chain's
members 1 to 8; the chain's front, member 0, is not in it. Nothing on completeness, on soundness or
on what is hidden.
-/
import Johnson.Desc.K12.Law.SitsKeyChains
import Johnson.Desc.K14.Blocks
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyTreesInFront
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (LaterPlaces beforeSharedPoint)
open _root_.Desc.K14 (P14)
open Lk6.AtPlan (keyFull)

/-- The later places' numbers: the library's written value. -/
def PF : LaterPlaces := Johnson.KB8.laterPlacesFull

/-- The linear claim's parameters at the written sized key. -/
def QK : P14 :=
  { set := keyFull.set, scope := if keyFull.once.lines.oneTime then .once else .shared
    codes := keyFull.codes, S := keyFull.once.shape, item := 0
    beforePoint := beforeSharedPoint PF }

/-- How many oracle messages a block declares. -/
def treesOfBlock {S Cl : Type} (b : Block S Cl) : Nat := (b.oracles.flatMap id).length

/-- The eight members behind the front, at the written value. -/
def treesEight : List Nat := (_root_.Desc.K14.blocksOr QK).map treesOfBlock

/-- The test on G_u, at the written places. -/
def treesGu : Nat := treesOfBlock (H2K.JointK.keyGu PF)

-- What they are: printed, so that a no shows its number.
#eval treesEight
#eval treesGu

-- Foretold: one tree at «send o_u», two at «send o_omega», none elsewhere; four at the test on G_u.
#guard treesEight == [0, 1, 0, 0, 2, 0, 0, 0]
#guard treesGu == 4
#guard treesEight.sum == 3
#guard treesEight.sum + treesGu == 7

end AtPublicFiles.KeyTreesInFront

#print axioms AtPublicFiles.KeyTreesInFront.PF
#print axioms AtPublicFiles.KeyTreesInFront.QK
#print axioms AtPublicFiles.KeyTreesInFront.treesOfBlock
#print axioms AtPublicFiles.KeyTreesInFront.treesEight
#print axioms AtPublicFiles.KeyTreesInFront.treesGu
