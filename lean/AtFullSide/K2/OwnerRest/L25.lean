-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/L25.lean: the written lists of the owner at the link 25: a listing off the written book.
-/
import AtFullSide.K2.OwnerRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open ProofFile.Honest.K2.Law (placesW)

/-- The entries in the book's stretches. -/
def restA25 : List (Addr × Due × Due × Bool) := []

/-- The entries in the chain of segments' piece. -/
def restS25 : List (Addr × Due × Due × Bool) := [
  (⟨⟨1, none, 2, .K12⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩, false),
  (⟨⟨1, none, 2, .K12⟩, 1⟩, ⟨0, 0⟩, ⟨0, 439⟩, false),
  (⟨⟨1, none, 2, .K12⟩, 1⟩, ⟨0, 439⟩, ⟨0, 222⟩, false)]

/-- The entries in the seven small pieces. -/
def restO25 : List (List (Addr × Due × Due × Bool)) := [[
  (⟨⟨1, none, 2, .K12⟩, 0⟩, ⟨0, 439⟩, ⟨0, 3⟩, true)], [], [], [], [], [], []]

end AtFullSide.K2

