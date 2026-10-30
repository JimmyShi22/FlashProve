-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/TilesOk.lean: A CLOSED FACT AT THE WRITTEN DATA
(Full/Data.lean), DECIDED BY LEAN's KERNEL, alone in its file: with each name's start read off the
written flat list itself, the 358 skeletons tile (`tilesB`, SkelTiles.lean).
  `startsOf ks s`  each skeleton's name with the sum of the numbers of rounds before it, from s
  `WW n`           the start of the name n in `flatW`; 0 for a name that is not there
  `totalW`         the sum of `flatW`'s numbers of rounds
  `tiles_full`     the closed fact. It would fail if a name that has a round stood twice
Limits. On numbers and names alone: no round's entry is read. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Data
import Johnson.Desc.ProofFile.Law.Skel.SkelTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

def startsOf : List Skel → Nat → List (String × Nat)
  | [], _ => []
  | k :: r, s => (k.name, s) :: startsOf r (s + k.nRounds)

def WW (n : String) : Nat := ((startsOf flatW 0).lookup n).getD 0

def totalW : Nat := (flatW.map (·.nRounds)).sum

theorem tiles_full : tilesB WW flatW 0 = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.tiles_full
