-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LendHead.lean: one lemma on the function `lend`
(Honest/Frame.lean), which hands a part of the prover the runs of other parts' coins that the
list of entries names. No definition.

  `lend_head`   where `lend` returns at a list of runs and a list of entries that both have a first
     member: the first run that it returns is the cut of the coins of the first entry's owner, from
     the entry's start on, at the count at which the first run is typed. And `lend` returns the
     other runs at the two lists' tails

This file imports Honest/Frame.lean and Honest/Law/Play.lean only, so that other kinds' files can
call the lemma.

Limits.
  * `look`, the function that returns an owner's coins, is a variable.
  * Nothing is said on whether `lend` returns.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {look : Addr → (d : Due) × Cs d}

/-- What `lend` returns for its first entry is the cut of that entry's owner's coins, from the
entry's start on. The other runs are lent for the other entries. -/
theorem lend_head {d : String × Due} {ds : List (String × Due)} {e : Ahead} {es : List Ahead}
    {c : CsAll (d :: ds)} (h : lend look (d :: ds) (e :: es) = .ok c) :
    (look e.owner).2.cut e.start d.2 = some c.1 ∧ lend look ds es = .ok c.2 := by
  simp only [lend] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i x hx
  obtain ⟨y, hy, rfl⟩ := exMap_ok h
  exact ⟨hx, hy⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.lend_head
