-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/GivenLetters.lean: WHERE THE BLOCK's given RETURNS AND THE TESTS ON THE PLAN PASS, THE LETTERS THAT
THE KIND's FORMULAS READ ARE THE WEIGHTS THAT THEY ARE TAKEN FOR: given_ok (Law/FromGiven.lean) and the law of
fromLookup (Law/FromLookup.lean), laid together: so that the laws which start at free floor, zx, zk
(HeadOutLaw.lean; Law/OutJoin.lean; K06AtLookup.lean [not in this library]) are spent at the block
that runs. No chance in it.
WHAT IT DOES NOT SAY. That the record's points are the same at the hearing and at the runs of claims: a law
of the blocks between (each leaves that reading of the record): owed.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.Kinds.Law.OutCall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

variable {S : Type}

/-- **The letters at the block that runs.** -/
theorem given_letters (p : Par) (L : Seat S) (s : S) (g : Given) (h : given p L s = .ok g) (sT : Nat)
    (hplan : @planOk g.sizes g.policy sT = true) :
    ∃ z : Point × (Nat → Point), L.lookup s = some z ∧ @PointsOk g.sizes p.floor z.1 z.2 ∧
      g.normIn = (@fromLookup g.sizes p.floor z.1 z.2).norm ∧
      g.headIn = (@fromLookup g.sizes p.floor z.1 z.2).head ∧
      g.calls = (@fromLookup g.sizes p.floor z.1 z.2).calls ∧
      @LettersOk g.sizes p.floor z.2 (@fromLookup g.sizes p.floor z.1 z.2) := by
  obtain ⟨z, y, hz, _, hP, rfl⟩ := given_ok p L s g h
  letI := p.sizes
  letI := p.policy
  letI : Request := L.request s
  letI : Token := ⟨y⟩
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  exact ⟨z, hz, hP, rfl, rfl, rfl, fromLookup_law p.floor z.1 z.2 hV (lens_small hplan) hP⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.given_letters
