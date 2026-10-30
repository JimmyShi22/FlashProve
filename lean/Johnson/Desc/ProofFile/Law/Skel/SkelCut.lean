-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelCut.lean: A ROW OF THE CUT IS SIX FIELDS OF THE SKELETON:
`PlanWritten.cutOf` (Johnson/Desc/Ok/PlanWritten/CutTest.lean) reads a block through `skel` alone.
Two statements with their proofs.
  `told_is`      `toldRounds b = toldFrom 0 b.oracles`
  `cutOf_skel`   T0: `cutOf bs = (bs.map skel).map Skel.row`
So where a chain's flat list has the skeletons fl (`back_of_skel`, SkelEnd.lean), its cut is
`fl.map Skel.row`.
Limits. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (toldRounds cutOf)

variable {S Cl : Type}

theorem told_is (b : Block S Cl) : toldRounds b = toldFrom 0 b.oracles :=
  toldFrom_zip b.oracles 0

/-- **T0.** -/
theorem cutOf_skel (bs : List (Block S Cl)) : cutOf bs = (bs.map skel).map Skel.row := by
  unfold cutOf
  rw [List.map_map]
  refine List.map_congr_left fun b _ => ?_
  show (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) =
    (b.name, b.place, b.rounds.length, b.oracles.length, toldFrom 0 b.oracles, b.before)
  rw [told_is]

end ProofFile.Sk

#print axioms ProofFile.Sk.told_is
#print axioms ProofFile.Sk.cutOf_skel
