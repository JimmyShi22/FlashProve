-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsK6.lean: K6.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksK6.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksK6
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.SlotsWalk
import Johnson.Desc.Kinds.Law.KeepsTrees
import Johnson.Desc.First.Link.Law.SlotsK6Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law

/-- **K6: the output head's own rounds.** -/
theorem k6_stepsS (nsOf : ℕ → ℕ × ℕ) (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    (blockAt h iU3 work l).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, a2, a3, a4⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : sl (s'.fork?.getD {}) = sl (s.fork?.getD {}) :=
    blockAt_sl h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨F0, L, a1, a2, ?_, ?_⟩
  · rw [Option.some.inj (a4.symm.trans hL')]
  · rw [← Option.some.inj (a3.symm.trans hG)]
    exact id ht

/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6_steps_seatedS (nsOf : ℕ → ℕ × ℕ) {W : OnBytes.Model.Verify.Public} {l : ℕ}
    {ms : List (ℕ × ℕ)} {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps (KeepsSlots nsOf) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_stepsS nsOf W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin
