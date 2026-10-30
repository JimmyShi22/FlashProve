-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Whole.lean: THE HONEST SIDE THAT LAYS LATE IS CLOSE TO THE REDUCTION AROUND THE
REAL GAME: Spec.lateToWrap (Johnson/LateWorld/SpecWrap.lean), WITH NO HYPOTHESIS.

This file states no goal of the release: the statement is one step of the proof of index privacy for
the scheme with the whole key published (the second hypothesis of wholeKeyPrivacy_of_parts,
Johnson/WholeKey/Assembly.lean).

It puts the proofs of the eleven parts into lateToWrap_of (Johnson/LateWorld/End.lean):
  the honest setup in its normal form, the seeds' bound, two facts on what the first phase can give
      (Johnson/LateWorld/Normal.lean, TabList.lean);
  the reduction's setup against the game in its normal form (Johnson/LateWorld/SetupNormal.lean);
  the key's test (Johnson/LateWorld/Branches.lean);
  the game's tables, the host's state after them, the links (Johnson/LateWorld/SetupGame.lean).

Main name (namespace OnBytes.LateWorld).
  lateToWrap   THE STATEMENT.

What it says and does not say: the head of Johnson/LateWorld/SpecWrap.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.End
import Johnson.LateWorld.Normal
import Johnson.LateWorld.TabList
import Johnson.LateWorld.SetupNormal
import Johnson.LateWorld.Branches
import Johnson.LateWorld.SetupGame

set_option autoImplicit false

namespace OnBytes.LateWorld

/-- **THE STATEMENT.** -/
theorem lateToWrap : Spec.lateToWrap :=
  lateToWrap_of lateNormal phaseBad
    (fun _ _ _ _ _ _ _ W S h T => phase1_len W S h T)
    (fun _ _ _ _ _ _ _ W S h T => phase1_coins W S h T)
    setupNormal testBranch linksW gameTabsGood stAfterKeeps stAfterCopies stAfterOod

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.lateToWrap
